/**************************************************************************/
/*                                                                        */
/*  This file is part of Frama-Clang                                      */
/*                                                                        */
/*  Copyright (C) 2012-2020                                               */
/*    CEA (Commissariat à l'énergie atomique et aux énergies              */
/*         alternatives)                                                  */
/*                                                                        */
/*  you can redistribute it and/or modify it under the terms of the GNU   */
/*  Lesser General Public License as published by the Free Software       */
/*  Foundation, version 2.1.                                              */
/*                                                                        */
/*  It is distributed in the hope that it will be useful,                 */
/*  but WITHOUT ANY WARRANTY; without even the implied warranty of        */
/*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the         */
/*  GNU Lesser General Public License for more details.                   */
/*                                                                        */
/*  See the GNU Lesser General Public License version 2.1                 */
/*  for more details (enclosed in the file LICENSE).                      */
/*                                                                        */
/**************************************************************************/

//
// Description:
//   Implementation of pointers for Virtual Method Tables
//

#include "RTTITable.h"
#include "llvm/Support/raw_ostream.h"
#include "clang/AST/DeclTemplate.h"

bool
RTTITable::ClassInfo::hasSameSignature(
  const clang::CXXMethodDecl* first,
  const clang::CXXMethodDecl* second) const
{ if (first->isConst() != second->isConst())
    return false;
  if (first->param_size() != second->param_size())
    return false;
  if (first->getReturnType().getCanonicalType()
      != second->getReturnType().getCanonicalType())
    return false;
  
  clang::FunctionDecl::param_const_iterator paramFirstIterEnd
    = first->param_end();
  clang::FunctionDecl::param_const_iterator paramFirstIter
    = first->param_begin();
  clang::FunctionDecl::param_const_iterator paramSecondIter
    = second->param_begin();
  while (paramFirstIter != paramFirstIterEnd) {
    if ((*paramFirstIter)->getType().getCanonicalType()
        != (*paramSecondIter)->getType().getCanonicalType())
      return false;
    ++paramFirstIter;
    ++paramSecondIter;
  };
  return true;
}

int
RTTITable::ClassInfo::addDerivation(const ClassInfo& source,
    const clang::CXXRecordDecl* base, bool isVirtual)
{ int oldPosition = _virtualMethodTable.size();
  bool isFirst = _derivationsPosition.empty();
  if (!isVirtual)
    // update _derivationsPosition
    _derivationsPosition.push_back(std::make_pair(base, oldPosition));

  // update _firstMultiplePosition
  if (_firstMultiplePosition == 0) {
    if (oldPosition > 0)
      _firstMultiplePosition = oldPosition;
    else if (!source._virtualMethodTable.empty()
          || !source._virtualBaseClassTable.empty()) {
      if (!isFirst || !source.hasPvmtAsFirstField()) {
        _firstMultiplePosition = -1;
        _pvmtAccess = source._pvmtAccess;
        _pvmtAccess.push_back(std::make_pair(base, 0 /* oldPosition */));
      };
    };
  };

  if (isVirtual) {
    // update _virtualBaseClassTable and _virtualDerivationsPosition
    std::vector<const clang::CXXRecordDecl*>::const_iterator
      iter = _virtualBaseClassTable.begin(),
      iterEnd = _virtualBaseClassTable.end();
    for (; iter != iterEnd; ++iter)
      if (base == *iter)
        break;
    if (iter == iterEnd) {
      _virtualBaseClassTable.push_back(base);
      _virtualDerivationsPosition.push_back(oldPosition);
    };

    // update _virtualMethodTable
    _virtualMethodTable.push_back(VirtualMethodInfo());
    _virtualMethodTable.back().setVirtualInherits(base, oldPosition);
  };

  // merge _virtualBaseClassTable and _virtualDerivationsPosition
  //    with source._virtualBaseClassTable and source._virtualBaseClassTable
  { std::vector<const clang::CXXRecordDecl*>::const_iterator
      sourceIter = source._virtualBaseClassTable.begin(),
      sourceIterEnd = source._virtualBaseClassTable.end();
    int sourceIndex = 0;
    for (; sourceIter != sourceIterEnd; ++sourceIter) {
      std::vector<const clang::CXXRecordDecl*>::const_iterator
        iter = _virtualBaseClassTable.begin(),
        iterEnd = _virtualBaseClassTable.end();
      bool hasFound = false;
      for (; !hasFound && iter != iterEnd; ++iter)
        hasFound = *iter == *sourceIter;
      if (!hasFound) {
        _virtualBaseClassTable.push_back(*sourceIter);
        int position = oldPosition
          + source._virtualDerivationsPosition[sourceIndex];
        _virtualDerivationsPosition.push_back(!isVirtual
            ? position : (position+1));
      };
      ++sourceIndex;
    };
  };

  // update _virtualMethodTable
  std::vector<VirtualMethodInfo>::const_iterator
    iter = source._virtualMethodTable.begin(),
    iterEnd = source._virtualMethodTable.end();
  for (; iter != iterEnd; iter++) {
    VirtualMethodInfo vmi = VirtualMethodInfo(*iter);
    if (!isVirtual)
      vmi.addInherits(base, oldPosition);
    else
      vmi.setVirtualInherits(base, oldPosition);
    _virtualMethodTable.insert(_virtualMethodTable.end(), vmi);
  }
  return oldPosition;
}

int
RTTITable::ClassInfo::getBasePosition(const clang::CXXRecordDecl* base,
    bool& isVirtual) const
{ { std::vector<const clang::CXXRecordDecl*>::const_iterator
      iter = _virtualBaseClassTable.begin(),
      iterEnd = _virtualBaseClassTable.end();
    int virtualBaseIndex = -1;
    isVirtual = false;
    for (; !isVirtual && iter != iterEnd; ++iter) {
      ++virtualBaseIndex;
      isVirtual = *iter == base;
    };
    if (isVirtual) {
      assert(virtualBaseIndex < (int) _virtualDerivationsPosition.size());
      return _virtualDerivationsPosition[virtualBaseIndex];
    };
  };

  int result = 0;
  InheritancePath::const_iterator baseIterEnd = _derivationsPosition.end();
  InheritancePath::const_iterator baseIter = _derivationsPosition.begin();
  bool hasResult = false;
  for (; !hasResult && (baseIter != baseIterEnd); ++baseIter)
    if (baseIter->first == base) {
      hasResult = true;
      result = baseIter->second;
    };
  assert(hasResult);
  return result;
}

bool RTTITable::ClassInfo::isSameMethod(
  const clang::CXXMethodDecl* m1, const clang::CXXMethodDecl* m2) const {
  // in case both m1 and m2 are (virtual) destructors, we must return true,
  // as there is at most one destructor in the vmt, the one for the most
  // derived class. However, the two DeclarationName are not equal
  // because of the class name.
  // In all other cases, we just have to compare names and signatures
  const clang::DeclarationName& n1 = m1->getNameInfo().getName();
  const clang::DeclarationName& n2 = m2->getNameInfo().getName();
  bool dest = n1.getNameKind() == clang::DeclarationName::CXXDestructorName;
  dest = dest && n2.getNameKind() == clang::DeclarationName::CXXDestructorName;
  return dest || (n1 == n2 && hasSameSignature(m1,m2));
}

int
RTTITable::ClassInfo::addVirtualMethod(clang::CXXMethodDecl* method)
{ typedef std::vector<VirtualMethodInfo>::iterator MethodIterator;
  MethodIterator iterEnd = _virtualMethodTable.end();
  int result = 0, index = 0;
  bool hasFound = false;
  for (MethodIterator iter = _virtualMethodTable.begin();
      iter != iterEnd; ++iter) {
    if (iter->isMethod() && isSameMethod(iter->getMethod(), method)) {
      if (_virtualBaseClassTable.empty()
          && (_firstMultiplePosition == 0 || _firstMultiplePosition > index))
        *iter = VirtualMethodInfo(method); // erase getInheritancePath()
      else
        iter->setMethod(method);
      if (!hasFound)
        result = index;
      if (_derivationsPosition.empty()
          || _derivationsPosition.back().second <= index)
        return result;
      hasFound = true;
    };
    ++index;
  };
  if (!hasFound)
    _virtualMethodTable.push_back(VirtualMethodInfo(method));
  else
    result = index;
  return result;
}

int
RTTITable::ClassInfo::getIndexOfMethod(clang::CXXMethodDecl* method,
    const InheritancePath*& inheritancePath,
    const VirtualInheritancePath*& virtualInheritancePath) const
{ MethodIterator iterEnd = _virtualMethodTable.end();
  int result = 0;
  for (MethodIterator iter = _virtualMethodTable.begin();
      iter != iterEnd; ++iter) {
    if (iter->isMethod() && isSameMethod(iter->getMethod(), method)) {
      inheritancePath = &iter->getInheritancePath();
      if (iter->hasVirtualInheritancePath())
        virtualInheritancePath = &iter->getVirtualInheritancePath();
      return result;
    };
    ++result;
  };
  assert(false);
  return 0;
}

void
RTTITable::DelayedMethodCalls::MethodCall::apply(const Clang_utils& utils,
    const ClassInfo& methodTable)
{ assert(!_indexShiftObject.empty());
  const InheritancePath* inheritancePath = NULL;
  const VirtualInheritancePath* virtualInheritancePath = NULL;
  int methodIndex;
  if (_method)
    methodIndex = methodTable.getIndexOfMethod(_method, inheritancePath,
      virtualInheritancePath);
  else {
    assert(_base);
    bool isVirtual = false;
    methodIndex = methodTable.getBasePosition(_base, isVirtual);
    assert(isVirtual);
    //const VirtualMethodInfo& info = methodTable.beginOfMethods()[methodIndex];
    // assert(info.isVirtualBaseAccess());
    // inheritancePath = &info.getInheritancePath();
    // if (info.hasVirtualInheritancePath())
    //   virtualInheritancePath = &info.getVirtualInheritancePath();
  };
  /* inheritance */ list shiftObject = NULL;
  /* inheritance */ list shiftPvmt = NULL;
  if (_method && virtualInheritancePath) {
    tkind templateParameters =
      utils.makeTemplateKind(virtualInheritancePath->first);
    shiftObject = cons_container(inheritance_cons(
          utils.makeQualifiedName(*virtualInheritancePath->first), 
          templateParameters, PUBLIC, VVIRTUAL,
          virtualInheritancePath->second), NULL);
  };
  if (_method) {
    ForwardReferenceList shiftEnd(shiftObject);
    InheritancePath::const_iterator iterEnd = inheritancePath->end();
    for (InheritancePath::const_iterator iter = inheritancePath->begin();
        iter != iterEnd; ++iter) {
      tkind templateParameters = utils.makeTemplateKind(iter->first);
      shiftEnd.insertContainer(
        inheritance_cons(
          utils.makeQualifiedName(*iter->first), templateParameters,
          PUBLIC, VSTANDARD, iter->second));
    }

    if (!methodTable.hasPvmtAsFirstField()) {
      ForwardReferenceList shiftEnd = ForwardReferenceList(shiftPvmt);
      inheritancePath = &methodTable.getPvmtField();
      InheritancePath::const_reverse_iterator iterEnd = inheritancePath->rend(),
          iter = inheritancePath->rbegin();
      for (; iter != iterEnd; ++iter) {
        tkind templateParameters = utils.makeTemplateKind(iter->first);
        shiftEnd.insertContainer(
          inheritance_cons(
            utils.makeQualifiedName(*iter->first), templateParameters, 
            PUBLIC, VSTANDARD, 0 /* iter->second */));
      };
    };
  };

  std::vector<std::pair<int64_t*, std::pair</* inheritance */ list*,
      /* inheritance */ list*> > >::const_iterator
    iterUpdateEnd = _indexShiftObject.end(),
    iterUpdate = _indexShiftObject.begin();
  assert(iterUpdate != iterUpdateEnd);
  *iterUpdate->first = methodIndex;
  if (_method) {
    *iterUpdate->second.first = shiftObject;
    *iterUpdate->second.second = shiftPvmt;
  };
  for (++iterUpdate; iterUpdate != iterUpdateEnd; ++iterUpdate) {
    *iterUpdate->first = methodIndex;
    if (_method) {
      list* backToUpdate = iterUpdate->second.first;
      list shiftIter = shiftObject;
      while (shiftIter) {
        *backToUpdate = cons_container(inheritance_dup((inheritance)
            shiftIter->element.container), NULL);
        backToUpdate = &(*backToUpdate)->next;
        shiftIter = shiftIter->next;
      };
      if (shiftPvmt) {
        backToUpdate = iterUpdate->second.second;
        shiftIter = shiftPvmt;
        while (shiftIter) {
          *backToUpdate = cons_container(inheritance_dup((inheritance)
              shiftIter->element.container), NULL);
          backToUpdate = &(*backToUpdate)->next;
          shiftIter = shiftIter->next;
        };
      };
    };
  };
  _indexShiftObject.clear();
}

void
RTTITable::DelayedMethodCalls::addMethodCall(clang::CXXMethodDecl* method,
    int64_t* methodIndex, /* inheritance */ list* shiftObject,
    /* inheritance */ list* shiftPvmt)
{ std::vector<MethodCall>::iterator iterEnd = _delayedCalls.end();
  for (std::vector<MethodCall>::iterator iter = _delayedCalls.begin();
      iter != iterEnd; ++iter) {
    if (iter->getMethod() == method) {
      iter->add(methodIndex, shiftObject, shiftPvmt);
      return;
    };
  };
  _delayedCalls.push_back(MethodCall(method, methodIndex, shiftObject,
    shiftPvmt));
}

void
RTTITable::DelayedMethodCalls::addFieldAccess(
    clang::CXXRecordDecl* baseClass, int64_t* accessIndex)
{ std::vector<MethodCall>::iterator iterEnd = _delayedCalls.end();
  for (std::vector<MethodCall>::iterator iter = _delayedCalls.begin();
      iter != iterEnd; ++iter) {
    if (iter->getBaseAccess() == baseClass) {
      iter->add(accessIndex);
      return;
    };
  };
  _delayedCalls.push_back(MethodCall(baseClass, accessIndex));
}

void
RTTITable::DelayedMethodCalls::updateWith(const Clang_utils& utils,
    const ClassInfo& methodTable)
{ std::vector<MethodCall>::iterator iterEnd = _delayedCalls.end();
  for (std::vector<MethodCall>::iterator iter = _delayedCalls.begin();
      iter != iterEnd; ++iter)
    iter->apply(utils, methodTable);
  _delayedCalls.clear();
}

qualified_name RTTITable::specialMemberName(
  const Clang_utils& utils, const char* base) const
{
  const clang::CXXRecordDecl* currClass = _currentClass.front();
  tkind templateArgs = utils.makeTemplateKind(currClass);
  return
    utils.makeQualifiedName(currClass, strdup(base), NULL, &templateArgs);
}

void
RTTITable::insertVMTContentPrelude(ForwardReferenceList& globals, location loc)
{ 
  // struct _frama_c_vmt_content {
  //   void (*method_ptr)();
  //   int shift_this;
  // };
  { /* class_decl */ list vmtContent = NULL;
    ForwardReferenceList endVmtContent(vmtContent);
    { typ methodPtrType = typ_Pointer(pkind_PFunctionPointer(signature_cons(
          qual_type_cons(NULL, typ_Void()), NULL, true)));
      endVmtContent.insertContainer(class_decl_CFieldDecl(copy_loc(loc),
          strdup("method_ptr"), qual_type_cons(NULL, methodPtrType),
          opt_none(), false));
    }
    { endVmtContent.insertContainer(class_decl_CFieldDecl(copy_loc(loc),
          strdup("shift_this"), qual_type_cons(NULL, typ_Int(IINT)),
          opt_none(), false));
    };
    globals.insertContainer(
      translation_unit_decl_Compound(
        copy_loc(loc),
        decl_or_impl_name_Implementation(
          qualified_name_cons(NULL, strdup("_frama_c_vmt_content"))),
        CSTRUCT, opt_none(),
        opt_some_container(vmtContent),
        false, tkind_TStandard(), false, false));
  };
}

void
RTTITable::insertVMTTypePrelude(ForwardReferenceList& globals, location loc) {
  // struct _frama_c_vmt {
  //   struct _frama_c_vmt_content* table;
  //   int table_size;
  //   struct _frama_c_rtti_name_info_node* rtti_info;
  // };
  { /* class_decl */ list vmtContent = NULL;
    ForwardReferenceList endVmtContent(vmtContent);
    { typ tableType = typ_Pointer(pkind_PDataPointer(
          qual_type_cons(NULL, typ_Struct(qualified_name_cons(NULL,
            strdup("_frama_c_vmt_content")), tkind_TStandard()))));
      endVmtContent.insertContainer(class_decl_CFieldDecl(copy_loc(loc),
          strdup("table"), qual_type_cons(NULL, tableType), opt_none(), false));
    }
    { endVmtContent.insertContainer(class_decl_CFieldDecl(copy_loc(loc),
          strdup("table_size"), qual_type_cons(NULL, typ_Int(IINT)),
          opt_none(), false));
    };
    { typ rttiInfoType = typ_Pointer(pkind_PDataPointer(
          qual_type_cons(NULL, typ_Struct(qualified_name_cons(NULL,
            strdup("_frama_c_rtti_name_info_node")), tkind_TStandard()))));
      endVmtContent.insertContainer(
        class_decl_CFieldDecl(
          copy_loc(loc),
          strdup("rtti_info"),
          qual_type_cons(NULL, rttiInfoType),
          opt_none(),
          false));
    }
    globals.insertContainer(
      translation_unit_decl_Compound(
        copy_loc(loc),
        decl_or_impl_name_Implementation(
          qualified_name_cons(NULL, strdup("_frama_c_vmt"))),
        CSTRUCT, opt_none(),
        opt_some_container(vmtContent),
        false, tkind_TStandard(), false, false));
  };
}

void
RTTITable::insertRTTIInfoPrelude(ForwardReferenceList& globals, location loc) {
  // struct _frama_c_rtti_name_info_content {
  //   struct _frama_c_rtti_name_info_node* value;
  //   int shift_object; 
  //   int shift_vmt; 
  // };
  { /* class_decl */ list rttiContent = NULL;
    ForwardReferenceList endRttiContent(rttiContent);
    { typ valueType = typ_Pointer(pkind_PDataPointer(
          qual_type_cons(NULL, typ_Struct(qualified_name_cons(NULL,
              "_frama_c_rtti_name_info_node"), tkind_TStandard()))));
      endRttiContent.insertContainer(
        class_decl_CFieldDecl(
          copy_loc(loc),
          strdup("value"),
          qual_type_cons(NULL, valueType),
          opt_none(),
          false));
    }
    { endRttiContent.insertContainer(
        class_decl_CFieldDecl(
          copy_loc(loc),
          strdup("shift_object"),
          qual_type_cons(NULL, typ_Int(IINT)),
          opt_none(),
          false));
      endRttiContent.insertContainer(
        class_decl_CFieldDecl(
          copy_loc(loc),
          strdup("shift_vmt"),
          qual_type_cons(NULL, typ_Int(IINT)),
          opt_none(),
          false));
    };
    globals.insertContainer(
      translation_unit_decl_Compound(
        copy_loc(loc),
        decl_or_impl_name_Implementation(
          qualified_name_cons(NULL, strdup("_frama_c_rtti_name_info_content"))),
        CSTRUCT, opt_none(),
        opt_some_container(rttiContent),
        false, tkind_TStandard(), false, false));
  };

  // struct _frama_c_rtti_name_info_node {
  //   const char* name;
  //   struct _frama_c_rtti_name_info_content* base_classes;
  //   int number_of_base_classes;
  //   struct _frama_c_vmt* pvmt;
  // };
  { /* class_decl */ list rttiContent = NULL;
    ForwardReferenceList endRttiContent(rttiContent);
    { typ nameType = typ_Pointer(pkind_PDataPointer(
          qual_type_cons(cons_plain(CONST, NULL), typ_Int(ICHAR))));
      endRttiContent.insertContainer(
        class_decl_CFieldDecl(
          copy_loc(loc),
          strdup("name"),
          qual_type_cons(NULL, nameType),
          opt_none(),
          false));
    }
    { typ baseClassesType = typ_Pointer(pkind_PDataPointer(
          qual_type_cons(NULL, typ_Struct(qualified_name_cons(NULL,
            strdup("_frama_c_rtti_name_info_content")), tkind_TStandard()))));
      endRttiContent.insertContainer(
        class_decl_CFieldDecl(
          copy_loc(loc),
          strdup("base_classes"),
          qual_type_cons(NULL, baseClassesType),
          opt_none(),
          false));
    }
    { endRttiContent.insertContainer(
        class_decl_CFieldDecl(
          copy_loc(loc),
          strdup("number_of_base_classes"),
          qual_type_cons(NULL, typ_Int(IINT)),
          opt_none(),
          false));
    }
    { typ vmtType = typ_Pointer(pkind_PDataPointer(
          qual_type_cons(NULL, typ_Struct(qualified_name_cons(NULL,
            strdup("_frama_c_vmt")), tkind_TStandard()))));
      endRttiContent.insertContainer(
        class_decl_CFieldDecl(
          copy_loc(loc),
          strdup("pvmt"),
          qual_type_cons(NULL, vmtType),
          opt_none(),
          false));
    }
    globals.insertContainer(
      translation_unit_decl_Compound(
        copy_loc(loc),
        decl_or_impl_name_Implementation(
          qualified_name_cons(NULL, strdup("_frama_c_rtti_name_info_node"))),
        CSTRUCT, opt_none(),
        opt_some_container(rttiContent),
        false, tkind_TStandard(), false, false));
  };
}

/* statement */ list*
RTTITable::insertRTTIAlgorithmsAuxDeclPrelude(ForwardReferenceList& globals,
    location loc) {
  // int _frama_c_find_dynamic_cast_aux(
  //   struct _frama_c_rtti_name_info_node* target_info,
  //   struct _frama_c_rtti_name_info_content* concrete_base,
  //   int number_of_bases, int found_shift_object, int found_shift_vmt,
  //   int last_shift_vmt, int* shift_object, int* distance) { ... }
  /* arg_decl */ list arguments = NULL;
  decl_or_impl_name functionName = decl_or_impl_name_Implementation(
      qualified_name_cons(NULL, strdup("_frama_c_find_dynamic_cast_aux")));
  { ForwardReferenceList argumentsEnd(arguments);
    argumentsEnd.insertContainer(arg_decl_cons(
      qual_type_cons(NULL, typ_Pointer(pkind_PDataPointer(qual_type_cons(NULL,
          typ_Struct(qualified_name_cons(NULL,
              strdup("_frama_c_rtti_name_info_node")), tkind_TStandard()))))),
      strdup("target_info"), copy_loc(loc)));
    argumentsEnd.insertContainer(arg_decl_cons(
      qual_type_cons(NULL, typ_Pointer(pkind_PDataPointer(qual_type_cons(NULL,
        typ_Struct(qualified_name_cons(NULL,
            strdup("_frama_c_rtti_name_info_content")), tkind_TStandard()))))),
      strdup("concrete_base"), copy_loc(loc)));
    argumentsEnd.insertContainer(arg_decl_cons(
      qual_type_cons(NULL, typ_Int(IINT)),
      strdup("number_of_bases"), copy_loc(loc)));
    argumentsEnd.insertContainer(arg_decl_cons(
      qual_type_cons(NULL, typ_Int(IINT)),
      strdup("found_shift_object"), copy_loc(loc)));
    argumentsEnd.insertContainer(arg_decl_cons(
      qual_type_cons(NULL, typ_Int(IINT)),
      strdup("found_shift_vmt"), copy_loc(loc)));
    argumentsEnd.insertContainer(arg_decl_cons(
      qual_type_cons(NULL, typ_Int(IINT)),
      strdup("last_shift_vmt"), copy_loc(loc)));
    argumentsEnd.insertContainer(arg_decl_cons(
      qual_type_cons(NULL, typ_Pointer(pkind_PDataPointer(qual_type_cons(NULL,
          typ_Int(IINT))))), strdup("shift_object"), copy_loc(loc)));
    argumentsEnd.insertContainer(arg_decl_cons(
      qual_type_cons(NULL, typ_Pointer(pkind_PDataPointer(qual_type_cons(NULL,
          typ_Int(IINT))))), strdup("distance"), copy_loc(loc)));
  };

  option result = opt_some_container(NULL);
  globals.insertContainer(
    translation_unit_decl_Function(
      functionName, funkind_FKFunction(), copy_loc(loc),
      qual_type_cons(NULL, typ_Int(IINT)),
      arguments, result, false /* is_extern_c */,
      false /* is_ghost */,
      false /* is_variadic */,
      tkind_TStandard(),
      false /* has_further_definition */,
      opt_none() /* throws */,
      opt_none() /* fun_spec */));
  return (/* statement */ list*) &result->content.container;
}

/* statement */ list*
RTTITable::insertRTTIAlgorithmsAuxWhilePrelude(/* statement */ list*
    functionBodyRef, location loc) {
  ForwardReferenceList functionBody(*functionBodyRef);
  { functionBody.insertContainer(statement_VarDecl(copy_loc(loc),
      strdup("result"), qual_type_cons(NULL, typ_Int(IINT)),
      opt_some_container(
        init_expr_Single_init(makeIntLiteral(loc,IINT,0)))));
    functionBody.insertContainer(statement_VarDecl(copy_loc(loc),
      strdup("cursor"),
      qual_type_cons(NULL, typ_Pointer(pkind_PDataPointer(qual_type_cons(NULL,
          typ_Struct(qualified_name_cons(NULL,
              "_frama_c_rtti_name_info_content"), tkind_TStandard()))))),
      opt_some_container(init_expr_Single_init(expression_cons(copy_loc(loc),
          exp_node_Variable(variable_FunctionParameter(
              strdup("concrete_base"))))))));
    functionBody.insertContainer(statement_VarDecl(copy_loc(loc),
      strdup("is_over"), qual_type_cons(NULL, typ_Int(IINT)),
      opt_some_container(
        init_expr_Single_init(makeIntLiteral(loc,IINT,0)))));
    functionBody.insertContainer(statement_VarDecl(copy_loc(loc),
      strdup("base_index"), qual_type_cons(NULL, typ_Int(IINT)),
      opt_some_container(
        init_expr_Single_init(makeIntLiteral(loc,IINT,0)))));
  };

  /* statement */ list* result = NULL;
  //   while (base_index < number_of_bases) {
  //     ...
  //   }; /* end of while */
  { expression conditionWhile = expression_cons(copy_loc(loc),
      exp_node_Binary_operator(BOLESS, AKRVALUE,
        expression_cons(copy_loc(loc), exp_node_Variable(variable_Local(
                qualified_name_cons(NULL, strdup("base_index"))))),
        expression_cons(copy_loc(loc), exp_node_Variable(
          variable_FunctionParameter(strdup("number_of_bases"))))));
    statement body = statement_Block(copy_loc(loc), NULL);
    functionBody.insertContainer(statement_While(copy_loc(loc),
      conditionWhile, body, NULL /* annot */));
    result = (/* statement */ list*) &body->cons_statement.Block.instructions;
  };

  //   return result;
  // }
  functionBody.insertContainer(statement_Return(copy_loc(loc),
    opt_some_container(expression_cons(copy_loc(loc), exp_node_Variable(
      variable_Local(qualified_name_cons(NULL, strdup("result"))))))));
  return result;
}

//     if (cursor->value == target_info) {
//       if (*distance < 0 || *distance >= 1) {
//         ...
//       }
//     }
//     else if (cursor->shift_vmt <= found_shift_vmt && (
//       (base_index < number_of_bases-1)
//         ? ((cursor+1)->shift_vmt > found_shift_vmt)
//         : ((last_shift_vmt == -1) || (found_shift_vmt < last_shift_vmt)))) {
//       ...
//     }
//     else if (*distance < 0 || *distance > 1) {
//       ...
//     }

void
RTTITable::insertRTTIAlgorithmsAuxWhileBodyPrelude(/* statement */ list*
    whileBodyRef, location loc, /* statement */ list*& then,
    /* statement */ list*& elseThen, /* statement */ list*& elseElseThen) {
  ForwardReferenceList whileBody(*whileBodyRef);
  //     if (cursor->value == target_info) {
  //       if (*distance < 0 || *distance >= 1) {
  //         ...
  //       }
  //     }
  expression subconditionIf =
    expression_cons(
      copy_loc(loc),
      exp_node_Binary_operator(
        BOLOGICALOR, AKRVALUE,
        expression_cons(
          copy_loc(loc),
          exp_node_Binary_operator(
            BOLESS, AKRVALUE,
            expression_cons(
              copy_loc(loc),
              exp_node_Dereference(
                expression_cons(
                  copy_loc(loc),
                  exp_node_Variable(
                    variable_FunctionParameter(strdup("distance")))))),
            makeIntLiteral(loc,IINT,0))),
        expression_cons(
          copy_loc(loc),
          exp_node_Binary_operator(
            BOGREATEROREQUAL, AKRVALUE,
            expression_cons(
              copy_loc(loc),
              exp_node_Dereference(
                expression_cons(
                  copy_loc(loc),
                  exp_node_Variable(
                    variable_FunctionParameter(strdup("distance")))))),
            makeIntLiteral(loc,IINT,1)))));
  expression conditionIf = expression_cons(copy_loc(loc),
    exp_node_Binary_operator(BOEQUAL, AKRVALUE,
      expression_cons(copy_loc(loc), exp_node_FieldAccess(
        expression_cons(copy_loc(loc), exp_node_Dereference(
          expression_cons(copy_loc(loc), exp_node_Variable(variable_Local(
                  qualified_name_cons(NULL, strdup("cursor"))))))),
        strdup("value"))),
      expression_cons(copy_loc(loc), exp_node_Variable(
        variable_FunctionParameter(strdup("target_info"))))));
  statement thenBlock = statement_Block(copy_loc(loc), NULL);
  statement firstCondition =
    statement_Condition(
      copy_loc(loc),
      cond_statement_CondExpression(conditionIf),
      statement_Condition(
        copy_loc(loc),
        cond_statement_CondExpression(subconditionIf),
        thenBlock,
        statement_Nop(copy_loc(loc))),
      statement_Nop(copy_loc(loc)));
  then = (/* statement */ list*) &thenBlock->cons_statement.Block.instructions;
  whileBody.insertContainer(firstCondition);
  statement* elseStmt = &firstCondition->cons_statement.Condition
    .else_instruction;

  //     else if (cursor->shift_vmt <= found_shift_vmt && (
  //       (base_index < number_of_bases-1)
  //         ? ((cursor+1)->shift_vmt > found_shift_vmt)
  //         : ((last_shift_vmt == -1) || (found_shift_vmt < last_shift_vmt))))
  //     {
  //       ...
  //     }

  expression localFirstAndExpression =
    expression_cons(
      copy_loc(loc),
      exp_node_Binary_operator(
        BOLESSOREQUAL, AKRVALUE,
        expression_cons(
          copy_loc(loc),
          exp_node_FieldAccess(
            expression_cons(
              copy_loc(loc),
              exp_node_Dereference(
                expression_cons(
                  copy_loc(loc),
                  exp_node_Variable(
                    variable_Local(
                      qualified_name_cons(NULL, strdup("cursor"))))))),
            strdup("shift_vmt"))),
        expression_cons(
          copy_loc(loc),
          exp_node_Variable(
            variable_FunctionParameter(strdup("found_shift_vmt"))))));
  exp_node* localSecondAndNode = NULL;
  expression localSecondAndExpression = expression_cons(copy_loc(loc), NULL);
  localSecondAndNode = &localSecondAndExpression->econtent;
  statement elseThenBlock = statement_Block(copy_loc(loc), NULL);
  elseThen = (/* statement */ list*) &elseThenBlock->cons_statement.Block
    .instructions;

  *elseStmt =
      statement_Condition(
        copy_loc(loc),
        cond_statement_CondExpression(
          expression_cons(
            copy_loc(loc),
            exp_node_Binary_operator(
              BOLOGICALAND,
              AKRVALUE, localFirstAndExpression, localSecondAndExpression))),
        elseThenBlock,
        statement_Nop(copy_loc(loc)));
  statement* elseElseStmt = &(*elseStmt)->cons_statement.Condition
    .else_instruction;
  { exp_node expressionCondition =
      exp_node_Binary_operator(
        BOLESS, AKRVALUE,
        expression_cons(
          copy_loc(loc),
          exp_node_Variable(
            variable_Local(qualified_name_cons(NULL, strdup("base_index"))))),
        expression_cons(
          copy_loc(loc),
          exp_node_Binary_operator(
            BOMINUS, AKRVALUE,
            expression_cons(
              copy_loc(loc),
              exp_node_Variable(
                variable_FunctionParameter(strdup("number_of_bases")))),
            makeIntLiteral(loc,IINT,1))));
    exp_node expressionThenCondition =
      exp_node_Binary_operator(
        BOGREATER, AKRVALUE,
        expression_cons(
          copy_loc(loc),
          exp_node_FieldAccess(
            expression_cons(
              copy_loc(loc),
              exp_node_Dereference(
                expression_cons(
                  copy_loc(loc),
                  exp_node_Binary_operator(
                    BOPLUS, AKRVALUE,
                    expression_cons(
                      copy_loc(loc),
                      exp_node_Variable(
                        variable_Local(
                          qualified_name_cons(NULL, strdup("cursor"))))),
                    makeIntLiteral(loc,IINT,1))))),
            strdup("shift_vmt"))),
        expression_cons(
          copy_loc(loc),
          exp_node_Variable(
            variable_FunctionParameter(strdup("found_shift_vmt")))));
    exp_node expressionElseFirstCondition =
      exp_node_Binary_operator(
        BOEQUAL, AKRVALUE,
        expression_cons(
          copy_loc(loc),
          exp_node_Variable(
            variable_FunctionParameter(strdup("last_shift_vmt")))),
        expression_cons(
          copy_loc(loc),
          exp_node_Unary_operator(
            uokind_UOOpposite(),
            makeIntLiteral(loc,IINT,1))));
    exp_node expressionElseSecondCondition = exp_node_Binary_operator(
      BOLESS, AKRVALUE, expression_cons(copy_loc(loc), exp_node_Variable(
        variable_FunctionParameter(strdup("found_shift_vmt")))),
      expression_cons(copy_loc(loc), exp_node_Variable(
          variable_FunctionParameter(strdup("last_shift_vmt")))));
    *localSecondAndNode = exp_node_Conditional(
      expression_cons(copy_loc(loc), expressionCondition),
      expression_cons(copy_loc(loc), expressionThenCondition),
      expression_cons(copy_loc(loc), exp_node_Binary_operator(
        BOLOGICALOR, AKRVALUE,
        expression_cons(copy_loc(loc), expressionElseFirstCondition),
        expression_cons(copy_loc(loc),
          expressionElseSecondCondition))));
  };

  //     else if (*distance < 0 || *distance > 1) {
  //       ...
  //     };
  //           /* case 0 and 1 are not possible */
  exp_node* localFirstOrNode = NULL;
  expression localFirstOrExpression = expression_cons(copy_loc(loc), NULL);
  localFirstOrNode = &localFirstOrExpression->econtent;
  exp_node* localSecondOrNode = NULL;
  expression localSecondOrExpression = expression_cons(copy_loc(loc), NULL);
  localSecondOrNode = &localSecondOrExpression->econtent;
  statement elseElseThenBlock = statement_Block(copy_loc(loc), NULL);
  elseElseThen = (/* statement */ list*) &elseElseThenBlock->cons_statement
    .Block.instructions;

  *elseElseStmt = statement_Condition(copy_loc(loc),
    cond_statement_CondExpression(expression_cons(copy_loc(loc),
      exp_node_Binary_operator(BOLOGICALOR, AKRVALUE, localFirstOrExpression,
        localSecondOrExpression))),
    elseElseThenBlock, statement_Nop(copy_loc(loc)));

  *localFirstOrNode =
    exp_node_Binary_operator(
      BOLESS, AKRVALUE, 
      expression_cons(
        copy_loc(loc),
        exp_node_Dereference(
          expression_cons(
            copy_loc(loc),
            exp_node_Variable(
              variable_FunctionParameter(strdup("distance")))))),
      makeIntLiteral(loc,IINT,0));
  *localSecondOrNode =
    exp_node_Binary_operator(
      BOGREATEROREQUAL, AKRVALUE, 
      expression_cons(
        copy_loc(loc),
        exp_node_Dereference(
          expression_cons(
            copy_loc(loc),
            exp_node_Variable(
              variable_FunctionParameter(strdup("distance")))))),
      makeIntLiteral(loc,IINT,1));
  //     cursor++;
  whileBody.insertContainer(
    statement_Expression(
      copy_loc(loc),
      expression_cons(
        copy_loc(loc),
        exp_node_Unary_operator(
          uokind_UOPostInc(),
          expression_cons(
            copy_loc(loc),
            exp_node_Variable(
              variable_Local(qualified_name_cons(NULL, strdup("cursor")))))))));
  //     base_index++;
  whileBody.insertContainer(
    statement_Expression(
      copy_loc(loc),
      expression_cons(
        copy_loc(loc),
        exp_node_Unary_operator(
          uokind_UOPostInc(),
          expression_cons(
            copy_loc(loc),
            exp_node_Variable(
              variable_Local(
                qualified_name_cons(NULL, strdup("base_index")))))))));
}

void
RTTITable::insertRTTIAlgorithmsAuxWhileThenBodyPrelude(/* statement */ list*
    statements, location loc) {
  ForwardReferenceList statementsEnd(*statements);

//         if (found_shift_vmt == cursor->shift_vmt)
  expression conditionIf = expression_cons(copy_loc(loc),
    exp_node_Binary_operator(BOEQUAL, AKRVALUE,
      expression_cons(copy_loc(loc), exp_node_Variable(
          variable_FunctionParameter(strdup("found_shift_vmt")))),
      expression_cons(copy_loc(loc), exp_node_FieldAccess(
        expression_cons(copy_loc(loc), exp_node_Dereference(
        expression_cons(copy_loc(loc), exp_node_Variable(
        variable_Local(qualified_name_cons(NULL, strdup("cursor"))))))),
        strdup("shift_vmt")))));
//           *distance = 0; /* impossible case */
  statement thenFoundLocation =
    statement_Expression(
      copy_loc(loc),
      expression_cons(
        copy_loc(loc),
        exp_node_Assign(
          expression_cons(
            copy_loc(loc),
            exp_node_Dereference(
              expression_cons(
                copy_loc(loc),
                exp_node_Variable(
                  variable_Local(
                    qualified_name_cons(NULL, strdup("distance"))))))),
          makeIntLiteral(loc,IINT,0))));
//         else
//           *distance = 1;
  statement elseFoundLocation =
    statement_Expression(
      copy_loc(loc),
      expression_cons(
        copy_loc(loc),
        exp_node_Assign(
          expression_cons(
            copy_loc(loc),
            exp_node_Dereference(
              expression_cons(
                copy_loc(loc),
                exp_node_Variable(
                  variable_Local(
                    qualified_name_cons(NULL, strdup("distance"))))))),
          makeIntLiteral(loc,IINT,1))));
  statementsEnd.insertContainer(
    statement_Condition(
      copy_loc(loc),
      cond_statement_CondExpression(conditionIf),
      thenFoundLocation,
      elseFoundLocation));
//         *shift_object = found_shift_object - cursor->shift_object;
  statementsEnd.insertContainer(statement_Expression(
    copy_loc(loc), expression_cons(copy_loc(loc), exp_node_Assign(
      expression_cons(copy_loc(loc), exp_node_Dereference(
        expression_cons(copy_loc(loc), exp_node_Variable(
          variable_FunctionParameter(strdup("shift_object")))))),
      expression_cons(copy_loc(loc), exp_node_Binary_operator(BOMINUS, AKRVALUE,
        expression_cons(copy_loc(loc), exp_node_Variable(variable_Local(
          qualified_name_cons(NULL, strdup("found_shift_object"))))),
        expression_cons(copy_loc(loc), exp_node_FieldAccess(
          expression_cons(copy_loc(loc), exp_node_Dereference(
            expression_cons(copy_loc(loc), exp_node_Variable(
              variable_Local(qualified_name_cons(NULL, strdup("cursor"))))))),
                strdup("shift_object")))))))));
//         result = 1;
  statementsEnd.insertContainer(
    statement_Expression(
      copy_loc(loc),
      expression_cons(
        copy_loc(loc),
        exp_node_Assign(
          expression_cons(
            copy_loc(loc),
            exp_node_Variable(
              variable_Local(qualified_name_cons(NULL, strdup("result"))))),
          makeIntLiteral(loc,IINT,1)))));
}

void
RTTITable::insertRTTIAlgorithmsAuxWhileElseThenBodyPrelude(/* statement */ list*
    statements, location loc) {
  ForwardReferenceList statementsEnd(*statements);
  //       int local_distance = 0;
  statementsEnd.insertContainer(
    statement_VarDecl(
      copy_loc(loc),
      strdup("local_distance"),
      qual_type_cons(NULL, typ_Int(IINT)),
      opt_some_container(
        init_expr_Single_init(makeIntLiteral(loc,IINT,0)))));
  //       int local_shift_object = 0;
  statementsEnd.insertContainer(
    statement_VarDecl(
      copy_loc(loc),
      strdup("local_shift_object"),
      qual_type_cons(NULL, typ_Int(IINT)),
      opt_some_container(
        init_expr_Single_init(makeIntLiteral(loc,IINT,0)))));
  //       int local_result = _frama_c_find_dynamic_cast_aux(target_info,
  //         cursor->value->base_classes,
  //         cursor->value->number_of_base_classes,
  //         found_shift_object - cursor->shift_object,
  //         found_shift_vmt - cursor->shift_vmt,
  //         (base_index < number_of_bases-1) ? (cursor+1)->shift_vmt
  //                                          : last_shift_vmt,
  //         &local_shift_object, &local_distance);

  /* qual_type */ list parameters = NULL;
  ForwardReferenceList parametersEnd(parameters);
  parametersEnd.insertContainer(qual_type_cons(NULL, typ_Pointer(
    pkind_PDataPointer(qual_type_cons(NULL, typ_Struct(qualified_name_cons(
      NULL, strdup("_frama_c_rtti_name_info_node")), tkind_TStandard()))))));
  parametersEnd.insertContainer(qual_type_cons(NULL, typ_Pointer(
    pkind_PDataPointer(qual_type_cons(NULL, typ_Struct(qualified_name_cons(
      NULL, strdup("_frama_c_rtti_name_info_content")), tkind_TStandard()))))));
  parametersEnd.insertContainer(qual_type_cons(NULL, typ_Int(IINT)));
  parametersEnd.insertContainer(qual_type_cons(NULL, typ_Int(IINT)));
  parametersEnd.insertContainer(qual_type_cons(NULL, typ_Int(IINT)));
  parametersEnd.insertContainer(qual_type_cons(NULL, typ_Int(IINT)));
  parametersEnd.insertContainer(qual_type_cons(NULL, typ_Pointer(
    pkind_PDataPointer(qual_type_cons(NULL, typ_Int(IINT))))));
  parametersEnd.insertContainer(qual_type_cons(NULL, typ_Pointer(
    pkind_PDataPointer(qual_type_cons(NULL, typ_Int(IINT))))));
  signature callSignature = signature_cons(qual_type_cons(NULL, typ_Int(IINT)),
    parameters, false /* variadic */);
  /* expression */ list callArguments = NULL;
  ForwardReferenceList callArgumentsEnd(callArguments);
  callArgumentsEnd.insertContainer(expression_cons(copy_loc(loc),
    exp_node_Variable(variable_FunctionParameter(strdup("target_info")))));
  callArgumentsEnd.insertContainer(expression_cons(copy_loc(loc),
    exp_node_FieldAccess(expression_cons(copy_loc(loc), exp_node_Dereference(
      expression_cons(copy_loc(loc), exp_node_FieldAccess(
        expression_cons(copy_loc(loc), exp_node_Dereference(
          expression_cons(copy_loc(loc), exp_node_Variable(variable_Local(
            qualified_name_cons(NULL, strdup("cursor"))))))),
        strdup("value"))))), strdup("base_classes"))));
  callArgumentsEnd.insertContainer(expression_cons(copy_loc(loc),
    exp_node_FieldAccess(expression_cons(copy_loc(loc), exp_node_Dereference(
      expression_cons(copy_loc(loc), exp_node_FieldAccess(
        expression_cons(copy_loc(loc), exp_node_Dereference(
          expression_cons(copy_loc(loc), exp_node_Variable(variable_Local(
            qualified_name_cons(NULL, strdup("cursor"))))))),
        strdup("value"))))), strdup("number_of_base_classes"))));
  callArgumentsEnd.insertContainer(expression_cons(copy_loc(loc),
    exp_node_Binary_operator(BOMINUS, AKRVALUE,
      expression_cons(copy_loc(loc), exp_node_Variable(
        variable_FunctionParameter(strdup("found_shift_object")))),
      expression_cons(copy_loc(loc), exp_node_FieldAccess(expression_cons(
        copy_loc(loc), exp_node_Dereference(expression_cons(copy_loc(loc),
          exp_node_Variable(variable_Local(qualified_name_cons(NULL,
            strdup("cursor"))))))), strdup("shift_object"))))));
  callArgumentsEnd.insertContainer(expression_cons(copy_loc(loc),
    exp_node_Binary_operator(BOMINUS, AKRVALUE,
      expression_cons(copy_loc(loc), exp_node_Variable(
        variable_FunctionParameter(strdup("found_shift_vmt")))),
      expression_cons(copy_loc(loc), exp_node_FieldAccess(expression_cons(
        copy_loc(loc), exp_node_Dereference(expression_cons(copy_loc(loc),
          exp_node_Variable(variable_Local(qualified_name_cons(NULL,
            strdup("cursor"))))))), strdup("shift_vmt"))))));
  callArgumentsEnd.insertContainer(
    expression_cons(
      copy_loc(loc),
      exp_node_Conditional(
        expression_cons(
          copy_loc(loc),
          exp_node_Binary_operator(
            BOLESS, AKRVALUE,
            expression_cons(
              copy_loc(loc),
              exp_node_Variable(
                variable_Local(
                  qualified_name_cons(NULL, strdup("base_index"))))),
            expression_cons(
              copy_loc(loc),
              exp_node_Binary_operator(
                BOMINUS, AKRVALUE,
                expression_cons(
                  copy_loc(loc),
                  exp_node_Variable(
                    variable_FunctionParameter(strdup("number_of_bases")))),
                makeIntLiteral(loc,IINT,1))))),
        expression_cons(
          copy_loc(loc),
          exp_node_FieldAccess(
            expression_cons(
              copy_loc(loc),
              exp_node_Dereference(
                expression_cons(
                  copy_loc(loc),
                  exp_node_Binary_operator(
                    BOPLUS, AKRVALUE,
                    expression_cons(
                      copy_loc(loc),
                      exp_node_Variable(
                        variable_Local(
                          qualified_name_cons(NULL, strdup("cursor"))))),
                    makeIntLiteral(loc,IINT,1))))),
            strdup("shift_vmt"))),
        expression_cons(
          copy_loc(loc),
          exp_node_Variable(
            variable_FunctionParameter(
              strdup("last_shift_vmt")))))));
  callArgumentsEnd.insertContainer(expression_cons(copy_loc(loc),
    exp_node_Address(expression_cons(copy_loc(loc),
      exp_node_Variable(variable_Local(qualified_name_cons(NULL,
        strdup("local_shift_object"))))))));
  callArgumentsEnd.insertContainer(expression_cons(copy_loc(loc),
    exp_node_Address(expression_cons(copy_loc(loc),
      exp_node_Variable(variable_Local(qualified_name_cons(NULL,
        strdup("local_distance"))))))));

  statementsEnd.insertContainer(statement_VarDecl(copy_loc(loc),
    strdup("local_result"), qual_type_cons(NULL, typ_Int(IINT)),
    opt_some_container(init_expr_Single_init(expression_cons(copy_loc(loc),
      exp_node_Static_call(
        qualified_name_cons(NULL, strdup("_frama_c_find_dynamic_cast_aux")),
        callSignature, funkind_FKFunction(),
        callArguments, tkind_TStandard(), false /* extern_c_call */))))));

  //       if (local_result && (local_distance >= 0)) {
  //         ...
  //       };
  statement* thenStatement = NULL;
  statement thenThenBlock = statement_Block(copy_loc(loc), NULL);
  statement condition =
    statement_Condition(
      copy_loc(loc),
      cond_statement_CondExpression(
        expression_cons(
          copy_loc(loc),
          exp_node_Binary_operator(
            BOLOGICALAND, AKRVALUE,
            expression_cons(
              copy_loc(loc),
              exp_node_Binary_operator(
                BODIFFERENT, AKRVALUE,
                expression_cons(
                  copy_loc(loc),
                  exp_node_Variable(
                    variable_Local(
                      qualified_name_cons(NULL, strdup("local_result"))))),
                makeIntLiteral(loc,IINT,0))),
            expression_cons(
              copy_loc(loc),
              exp_node_Binary_operator(
                BOGREATEROREQUAL, AKRVALUE,
                expression_cons(
                  copy_loc(loc),
                  exp_node_Variable(
                    variable_Local(
                      qualified_name_cons(NULL, strdup("local_distance"))))),
                makeIntLiteral(loc,IINT,0)))))),
      thenThenBlock,
      statement_Nop(copy_loc(loc)));
  statementsEnd.insertContainer(condition);
  thenStatement = &condition->cons_statement.Condition.then_instruction;

  //         if (*distance < 0 || *distance >= local_distance) {
  //           ...
  //         };
  /* statement */ list* thenThenBody = NULL;
  thenThenBody = &thenThenBlock->cons_statement.Block.instructions;
  *thenStatement =
    statement_Condition(
      copy_loc(loc),
      cond_statement_CondExpression(
        expression_cons(
          copy_loc(loc),
          exp_node_Binary_operator(
            BOLOGICALOR, AKRVALUE,
            expression_cons(
              copy_loc(loc),
              exp_node_Binary_operator(
                BOLESS, AKRVALUE,
                expression_cons(
                  copy_loc(loc),
                  exp_node_Dereference(
                    expression_cons(
                      copy_loc(loc),
                      exp_node_Variable(
                        variable_FunctionParameter(strdup("distance")))))),
                makeIntLiteral(loc,IINT,0))),
            expression_cons(
              copy_loc(loc),
              exp_node_Binary_operator(
                BOGREATEROREQUAL, AKRVALUE,
                expression_cons(
                  copy_loc(loc),
                  exp_node_Dereference(
                    expression_cons(
                      copy_loc(loc),
                      exp_node_Variable(
                        variable_FunctionParameter(strdup("distance")))))),
                expression_cons(
                  copy_loc(loc),
                  exp_node_Variable(
                    variable_Local(
                      qualified_name_cons(
                        NULL, strdup("local_distance")))))))))),
      thenThenBlock, statement_Nop(copy_loc(loc)));
  ForwardReferenceList thenThenBodyEnd(*thenThenBody);
  //           result = local_result;
  thenThenBodyEnd.insertContainer(statement_Expression(copy_loc(loc),
    expression_cons(copy_loc(loc), exp_node_Assign(
      expression_cons(copy_loc(loc), exp_node_Variable(variable_Local(
        qualified_name_cons(NULL, strdup("result"))))),
      expression_cons(copy_loc(loc), exp_node_Variable(variable_Local(
        qualified_name_cons(NULL, strdup("local_result")))))))));
  //           *shift_object = local_shift_object - cursor->shift_object;
  thenThenBodyEnd.insertContainer(statement_Expression(copy_loc(loc),
    expression_cons(copy_loc(loc), exp_node_Assign(
      expression_cons(copy_loc(loc), exp_node_Dereference(expression_cons(
        copy_loc(loc), exp_node_Variable(variable_FunctionParameter(
          strdup("shift_object")))))),
      expression_cons(copy_loc(loc), exp_node_Binary_operator(BOMINUS, AKRVALUE,
        expression_cons(copy_loc(loc), exp_node_Variable(variable_Local(
          qualified_name_cons(NULL, strdup("local_shift_object"))))),
        expression_cons(copy_loc(loc), exp_node_FieldAccess(expression_cons(
          copy_loc(loc), exp_node_Dereference(expression_cons(copy_loc(loc),
            exp_node_Variable(variable_Local(qualified_name_cons(NULL,
              strdup("cursor"))))))), strdup("shift_object")))))))));
  //           *distance = local_distance;
  thenThenBodyEnd.insertContainer(statement_Expression(copy_loc(loc),
    expression_cons(copy_loc(loc), exp_node_Assign(
      expression_cons(copy_loc(loc), exp_node_Dereference(expression_cons(
        copy_loc(loc), exp_node_Variable(variable_FunctionParameter(
          strdup("distance")))))),
      expression_cons(copy_loc(loc), exp_node_Variable(variable_Local(
        qualified_name_cons(NULL, strdup("local_distance")))))))));

  //       is_over = 1;
  statementsEnd.insertContainer(
    statement_Expression(
      copy_loc(loc),
      expression_cons(
        copy_loc(loc),
        exp_node_Assign(
          expression_cons(
            copy_loc(loc),
            exp_node_Variable(
              variable_Local(qualified_name_cons(NULL, strdup("is_over"))))),
          makeIntLiteral(loc,IINT,1)))));
}

void
RTTITable::insertRTTIAlgorithmsAuxWhileElseElseThenBodyPrelude(
    /* statement */ list* statements, location loc) {
  ForwardReferenceList statementsEnd(*statements);
//       int local_distance = 0;
  statementsEnd.insertContainer(
    statement_VarDecl(
      copy_loc(loc),
      strdup("local_distance"),
      qual_type_cons(NULL, typ_Int(IINT)),
      opt_some_container(init_expr_Single_init(makeIntLiteral(loc,IINT,0)))));
//       int local_shift_object = 0;
  statementsEnd.insertContainer(
    statement_VarDecl(
      copy_loc(loc),
      strdup("local_shift_object"),
      qual_type_cons(NULL, typ_Int(IINT)),
      opt_some_container(init_expr_Single_init(makeIntLiteral(loc,IINT,0)))));
//       int local_result = _frama_c_find_dynamic_cast_aux(target_info,
//         cursor->value->base_classes,
//         cursor->value->number_of_base_classes,
//         found_shift_object - cursor->shift_object,
//         found_shift_vmt - cursor->shift_vmt,
//         (base_index < number_of_bases-1) ? (cursor+1)->shift_vmt
//                                          : last_shift_vmt,
//         &local_shift_object, &local_distance);
  /* qual_type */ list parameters = NULL;
  ForwardReferenceList parametersEnd(parameters);
  parametersEnd.insertContainer(qual_type_cons(NULL, typ_Pointer(
    pkind_PDataPointer(qual_type_cons(NULL, typ_Struct(qualified_name_cons(
      NULL, strdup("_frama_c_rtti_name_info_node")), tkind_TStandard()))))));
  parametersEnd.insertContainer(qual_type_cons(NULL, typ_Pointer(
    pkind_PDataPointer(qual_type_cons(NULL, typ_Struct(qualified_name_cons(
      NULL, strdup("_frama_c_rtti_name_info_content")), tkind_TStandard()))))));
  parametersEnd.insertContainer(qual_type_cons(NULL, typ_Int(IINT)));
  parametersEnd.insertContainer(qual_type_cons(NULL, typ_Int(IINT)));
  parametersEnd.insertContainer(qual_type_cons(NULL, typ_Int(IINT)));
  parametersEnd.insertContainer(qual_type_cons(NULL, typ_Int(IINT)));
  parametersEnd.insertContainer(qual_type_cons(NULL, typ_Pointer(
    pkind_PDataPointer(qual_type_cons(NULL, typ_Int(IINT))))));
  parametersEnd.insertContainer(qual_type_cons(NULL, typ_Pointer(
    pkind_PDataPointer(qual_type_cons(NULL, typ_Int(IINT))))));
  signature callSignature = signature_cons(qual_type_cons(NULL, typ_Int(IINT)),
    parameters, false /* variadic */);
  /* expression */ list callArguments = NULL;
  ForwardReferenceList callArgumentsEnd(callArguments);
  callArgumentsEnd.insertContainer(expression_cons(copy_loc(loc),
    exp_node_Variable(variable_FunctionParameter(strdup("target_info")))));
  callArgumentsEnd.insertContainer(expression_cons(copy_loc(loc),
    exp_node_FieldAccess(expression_cons(copy_loc(loc), exp_node_Dereference(
      expression_cons(copy_loc(loc), exp_node_FieldAccess(
        expression_cons(copy_loc(loc), exp_node_Dereference(
          expression_cons(copy_loc(loc), exp_node_Variable(variable_Local(
            qualified_name_cons(NULL, strdup("cursor"))))))),
        strdup("value"))))), strdup("base_classes"))));
  callArgumentsEnd.insertContainer(expression_cons(copy_loc(loc),
    exp_node_FieldAccess(expression_cons(copy_loc(loc), exp_node_Dereference(
      expression_cons(copy_loc(loc), exp_node_FieldAccess(
        expression_cons(copy_loc(loc), exp_node_Dereference(
          expression_cons(copy_loc(loc), exp_node_Variable(variable_Local(
            qualified_name_cons(NULL, strdup("cursor"))))))),
        strdup("value"))))), strdup("number_of_base_classes"))));
  callArgumentsEnd.insertContainer(expression_cons(copy_loc(loc),
    exp_node_Binary_operator(BOMINUS, AKRVALUE,
      expression_cons(copy_loc(loc), exp_node_Variable(
        variable_FunctionParameter(strdup("found_shift_object")))),
      expression_cons(copy_loc(loc), exp_node_FieldAccess(expression_cons(
        copy_loc(loc), exp_node_Dereference(expression_cons(copy_loc(loc),
          exp_node_Variable(variable_Local(qualified_name_cons(NULL,
            strdup("cursor"))))))), strdup("shift_object"))))));
  callArgumentsEnd.insertContainer(expression_cons(copy_loc(loc),
    exp_node_Binary_operator(BOMINUS, AKRVALUE,
      expression_cons(copy_loc(loc), exp_node_Variable(
        variable_FunctionParameter(strdup("found_shift_vmt")))),
      expression_cons(copy_loc(loc), exp_node_FieldAccess(expression_cons(
        copy_loc(loc), exp_node_Dereference(expression_cons(copy_loc(loc),
          exp_node_Variable(variable_Local(qualified_name_cons(NULL,
            strdup("cursor"))))))), strdup("shift_vmt"))))));
  callArgumentsEnd.insertContainer(
    expression_cons(
      copy_loc(loc),
      exp_node_Conditional(
        expression_cons(
          copy_loc(loc),
          exp_node_Binary_operator(
            BOLESS, AKRVALUE,
            expression_cons(
              copy_loc(loc),
              exp_node_Variable(
                variable_Local(
                  qualified_name_cons(NULL, strdup("base_index"))))),
            expression_cons(
              copy_loc(loc),
              exp_node_Binary_operator(
                BOPLUS, AKRVALUE,
                expression_cons(
                  copy_loc(loc),
                  exp_node_Variable(
                    variable_FunctionParameter(strdup("number_of_bases")))),
                makeIntLiteral(loc,IINT,1))))),
        expression_cons(
          copy_loc(loc),
          exp_node_FieldAccess(
            expression_cons(
              copy_loc(loc),
              exp_node_Dereference(
                expression_cons(
                  copy_loc(loc),
                  exp_node_Binary_operator(
                    BOPLUS, AKRVALUE,
                    expression_cons(
                      copy_loc(loc),
                      exp_node_Variable(
                        variable_Local(
                          qualified_name_cons(NULL, strdup("cursor"))))),
                    makeIntLiteral(loc,IINT,1))))),
            strdup("shift_vmt"))),
        expression_cons(
          copy_loc(loc),
          exp_node_Variable(
            variable_FunctionParameter(strdup("last_shift_vmt")))))));
  callArgumentsEnd.insertContainer(expression_cons(copy_loc(loc),
    exp_node_Address(expression_cons(copy_loc(loc), exp_node_Variable(
      variable_Local(qualified_name_cons(NULL,
        strdup("local_shift_object"))))))));
  callArgumentsEnd.insertContainer(expression_cons(copy_loc(loc),
    exp_node_Address(expression_cons(copy_loc(loc), exp_node_Variable(
      variable_Local(qualified_name_cons(NULL, strdup("local_distance"))))))));

  statementsEnd.insertContainer(statement_VarDecl(copy_loc(loc),
    strdup("local_result"), qual_type_cons(NULL, typ_Int(IINT)),
    opt_some_container(init_expr_Single_init(expression_cons(copy_loc(loc),
      exp_node_Static_call(
        qualified_name_cons(NULL, strdup("_frama_c_find_dynamic_cast_aux")),
        callSignature, funkind_FKFunction(),
        callArguments, tkind_TStandard(), false /* extern_c_call */))))));

//       if (local_result && (local_distance >= 0)) {
//         ...
//       };
  statement* thenStatement = NULL;
  statement thenThenBlock = statement_Block(copy_loc(loc), NULL);
  statement condition =
    statement_Condition(
      copy_loc(loc),
      cond_statement_CondExpression(
        expression_cons(
          copy_loc(loc),
          exp_node_Binary_operator(
            BOLOGICALAND, AKRVALUE,
            expression_cons(
              copy_loc(loc),
              exp_node_Binary_operator(
                BODIFFERENT, AKRVALUE,
                expression_cons(
                  copy_loc(loc),
                  exp_node_Variable(
                    variable_Local(
                      qualified_name_cons(NULL, strdup("local_result"))))),
                makeIntLiteral(loc,IINT,0))),
            expression_cons(
              copy_loc(loc),
              exp_node_Binary_operator(
                BOGREATEROREQUAL, AKRVALUE,
                expression_cons(
                  copy_loc(loc),
                  exp_node_Variable(
                    variable_Local(
                      qualified_name_cons(NULL, strdup("local_distance"))))),
                makeIntLiteral(loc,IINT,0)))))),
      thenThenBlock, statement_Nop(copy_loc(loc)));
  statementsEnd.insertContainer(condition);
  thenStatement = &condition->cons_statement.Condition.then_instruction;

//         if (*distance < 0 || *distance
//               > (!is_over ? local_distance : (local_distance+1))) { ... };
  /* statemement */ list* thenThenBody = &thenThenBlock->cons_statement.Block
    .instructions;
  *thenStatement =
    statement_Condition(
      copy_loc(loc),
      cond_statement_CondExpression(
        expression_cons(
          copy_loc(loc),
          exp_node_Binary_operator(
            BOLOGICALOR, AKRVALUE,
            expression_cons(
              copy_loc(loc),
              exp_node_Binary_operator(
                BOLESS, AKRVALUE,
                expression_cons(
                  copy_loc(loc),
                  exp_node_Dereference(
                    expression_cons(
                      copy_loc(loc),
                      exp_node_Variable(
                        variable_FunctionParameter(strdup("distance")))))),
                makeIntLiteral(loc,IINT,0))),
            expression_cons(
              copy_loc(loc),
              exp_node_Binary_operator(
                BOGREATER, AKRVALUE,
                expression_cons(
                  copy_loc(loc),
                  exp_node_Dereference(
                    expression_cons(
                      copy_loc(loc),
                      exp_node_Variable(
                        variable_FunctionParameter(strdup("distance")))))),
                expression_cons(
                  copy_loc(loc),
                  exp_node_Conditional(
                    expression_cons(
                      copy_loc(loc),
                      exp_node_Binary_operator(
                        BOEQUAL, AKRVALUE,
                        expression_cons(
                          copy_loc(loc),
                          exp_node_Variable(
                            variable_Local(
                              qualified_name_cons(NULL, strdup("is_over"))))),
                        makeIntLiteral(loc,IINT,0))),
                    expression_cons(
                      copy_loc(loc),
                      exp_node_Variable(
                        variable_Local(
                          qualified_name_cons(
                            NULL, strdup("local_distance"))))),
                    expression_cons(
                      copy_loc(loc),
                      exp_node_Binary_operator(
                        BOPLUS, AKRVALUE,
                        expression_cons(
                          copy_loc(loc),
                          exp_node_Variable(
                            variable_Local(
                              qualified_name_cons(
                                NULL, strdup("local_distance"))))),
                        makeIntLiteral(loc,IINT,1)))))))))),
      thenThenBlock, statement_Nop(copy_loc(loc)));
  ForwardReferenceList thenThenBodyEnd(*thenThenBody);
//           result = local_result;
  thenThenBodyEnd.insertContainer(statement_Expression(copy_loc(loc),
    expression_cons(copy_loc(loc), exp_node_Assign(
      expression_cons(copy_loc(loc), exp_node_Variable(variable_Local(
        qualified_name_cons(NULL, strdup("result"))))),
      expression_cons(copy_loc(loc), exp_node_Variable(variable_Local(
        qualified_name_cons(NULL, strdup("local_result")))))))));
//           *shift_object = local_shift_object - cursor->shift_object;
  thenThenBodyEnd.insertContainer(statement_Expression(copy_loc(loc),
    expression_cons(copy_loc(loc), exp_node_Assign(
      expression_cons(copy_loc(loc), exp_node_Dereference(expression_cons(
        copy_loc(loc), exp_node_Variable(variable_FunctionParameter(
          strdup("shift_object")))))),
      expression_cons(copy_loc(loc), exp_node_Binary_operator(BOMINUS, AKRVALUE,
        expression_cons(copy_loc(loc), exp_node_Variable(variable_Local(
          qualified_name_cons(NULL, strdup("local_shift_object"))))),
        expression_cons(copy_loc(loc), exp_node_FieldAccess(expression_cons(
          copy_loc(loc), exp_node_Dereference(expression_cons(copy_loc(loc),
            exp_node_Variable(variable_Local(qualified_name_cons(NULL,
              strdup("cursor"))))))), strdup("shift_object")))))))));
//           *distance = local_distance+1;
  thenThenBodyEnd.insertContainer(
    statement_Expression(
      copy_loc(loc),
      expression_cons(
        copy_loc(loc),
        exp_node_Assign(
          expression_cons(
            copy_loc(loc),
            exp_node_Dereference(
              expression_cons(
                copy_loc(loc),
                exp_node_Variable(
                  variable_FunctionParameter(strdup("distance")))))),
          expression_cons(
            copy_loc(loc),
            exp_node_Binary_operator(
              BOPLUS, AKRVALUE,
              expression_cons(
                copy_loc(loc),
                exp_node_Variable(
                  variable_Local(
                    qualified_name_cons(NULL, strdup("local_distance"))))),
              makeIntLiteral(loc,IINT,1)))))));
}

// int _frama_c_find_dynamic_cast_aux(
//   struct _frama_c_rtti_name_info_node* target_info,
//   struct _frama_c_rtti_name_info_content* concrete_base,
//   int number_of_bases, int found_shift_object, int found_shift_vmt,
//   int last_shift_vmt, int* shift_object, int* distance)
// { int result = 0;
//   struct _frama_c_rtti_name_info_content* cursor = concrete_base;
//   int is_over = 0;
//   int base_index = 0;
//   while (base_index < number_of_bases) {
//     if (cursor->value == target_info) {
//       if (*distance < 0 || *distance >= 1) {
//           /* case 0 and 1 are not possible */
//         if (found_shift_vmt == cursor->shift_vmt)
//           *distance = 0; /* impossible case */
//         else
//           *distance = 1;
//         *shift_object = found_shift_object - cursor->shift_object;
//         result = 1;
//       }
//     }
//     else if (cursor->shift_vmt <= found_shift_vmt && (
//       (base_index < number_of_bases-1)
//         ? ((cursor+1)->shift_vmt > found_shift_vmt)
//         : ((last_shift_vmt == -1) || (found_shift_vmt < last_shift_vmt))))
//     { int local_distance = 0;
//       int local_shift_object = 0;
//       int local_result = _frama_c_find_dynamic_cast_aux(target_info,
//         cursor->value->base_classes,
//         cursor->value->number_of_base_classes,
//         found_shift_object - cursor->shift_object,
//         found_shift_vmt - cursor->shift_vmt,
//         (base_index < number_of_bases-1) ? (cursor+1)->shift_vmt
//                                          : last_shift_vmt,
//         &local_shift_object, &local_distance);
//       if (local_result && (local_distance >= 0)) {
//         if (*distance < 0 || *distance >= local_distance) {
//           result = local_result;
//           *shift_object = local_shift_object - cursor->shift_object;
//           *distance = local_distance;
//         };
//       };
//       is_over = 1;
//     }
//     else if (*distance < 0 || *distance > 1) {
//       int local_distance = 0;
//       int local_shift_object = 0;
//       int local_result = _frama_c_find_dynamic_cast_aux(target_info,
//         cursor->value->base_classes,
//         cursor->value->number_of_base_classes,
//         found_shift_object - cursor->shift_object,
//         found_shift_vmt - cursor->shift_vmt,
//         (base_index < number_of_bases-1) ? (cursor+1)->shift_vmt
//                                          : last_shift_vmt,
//         &local_shift_object, &local_distance);
//       if (local_result && (local_distance >= 0)) {
//         if (*distance < 0 || *distance
//               > (!is_over ? local_distance : (local_distance+1))) {
//           result = local_result;
//           *shift_object = local_shift_object - cursor->shift_object;
//           *distance = local_distance+1;
//         };
//       };
//     };
//     cursor = cursor+1;
//     base_index = base_index+1;
//   }; /* end of while */
//   return result;
// }

/* statement */ list*
RTTITable::insertRTTIAlgorithmsAuxPrelude(ForwardReferenceList& globals,
    location loc) {
  /* statement */ list* functionBody = insertRTTIAlgorithmsAuxDeclPrelude(
      globals, loc);
  /* statement */ list* whileBody = insertRTTIAlgorithmsAuxWhilePrelude(
      functionBody, loc);
  /* statement */ list* whileThen = NULL;
  /* statement */ list* whileElseThen = NULL;
  /* statement */ list* whileElseElseThen = NULL;
  insertRTTIAlgorithmsAuxWhileBodyPrelude(whileBody, loc, whileThen,
      whileElseThen, whileElseElseThen);
  insertRTTIAlgorithmsAuxWhileThenBodyPrelude(whileThen, loc);
  insertRTTIAlgorithmsAuxWhileElseThenBodyPrelude(whileElseThen, loc);
  insertRTTIAlgorithmsAuxWhileElseElseThenBodyPrelude(whileElseElseThen, loc);
  return functionBody;
}

/* statement */ list*
RTTITable::insertRTTIAlgorithmsDeclPrelude(ForwardReferenceList& globals,
    location loc) {
// int _frama_c_find_dynamic_cast(
//   struct _frama_c_rtti_name_info_node* declared_info,
//   struct _frama_c_vmt* declared_vmt, 
//   struct _frama_c_rtti_name_info_node* target_info,
//   int* shift_object) { ... }
  /* arg_decl */ list arguments = NULL;
  ForwardReferenceList argumentsEnd(arguments);
  argumentsEnd.insertContainer(arg_decl_cons(
    qual_type_cons(NULL, typ_Pointer(pkind_PDataPointer(qual_type_cons(NULL,
      typ_Struct(qualified_name_cons(NULL,
        strdup("_frama_c_rtti_name_info_node")), tkind_TStandard()))))),
    strdup("declared_info"), copy_loc(loc)));
  argumentsEnd.insertContainer(arg_decl_cons(
    qual_type_cons(NULL, typ_Pointer(pkind_PDataPointer(qual_type_cons(NULL,
      typ_Struct(qualified_name_cons(NULL, strdup("_frama_c_vmt")),
        tkind_TStandard()))))), strdup("declared_vmt"), copy_loc(loc)));
  argumentsEnd.insertContainer(arg_decl_cons(
    qual_type_cons(NULL, typ_Pointer(pkind_PDataPointer(qual_type_cons(NULL,
      typ_Struct(qualified_name_cons(NULL,
        strdup("_frama_c_rtti_name_info_node")), tkind_TStandard()))))),
    strdup("target_info"), copy_loc(loc)));
  argumentsEnd.insertContainer(arg_decl_cons(qual_type_cons(NULL,
      typ_Pointer(pkind_PDataPointer(qual_type_cons(NULL, typ_Int(IINT))))),
    strdup("shift_object"), copy_loc(loc)));

  /* statement list */ option result = opt_some_container(NULL);
  globals.insertContainer(
    translation_unit_decl_Function(
      decl_or_impl_name_Implementation(
        qualified_name_cons(NULL, strdup("_frama_c_find_dynamic_cast"))),
      funkind_FKFunction(), copy_loc(loc),
      qual_type_cons(NULL, typ_Int(IINT)), arguments, result,
      false /* is_extern_c */, false /* is_ghost */,
      false /* is_variadic */, tkind_TStandard(),
      false /* has_further_definition */,
      opt_none() /* throws */,
      opt_none() /* fun_spec */));
  return (/* statement */ list*) &result->content.container;
}

/* statement */ list*
RTTITable::insertRTTIAlgorithmsFirstPartPrelude(/* statement */ list*
    statements, location loc) {
  ForwardReferenceList statementsEnd(*statements);
//   struct _frama_c_rtti_name_info_node*
//     concrete_info = declared_vmt->rtti_info;
  statementsEnd.insertContainer(statement_VarDecl(copy_loc(loc),
    strdup("concrete_info"), qual_type_cons(NULL, typ_Pointer(
      pkind_PDataPointer(qual_type_cons(NULL, typ_Struct(qualified_name_cons(
        NULL, strdup("_frama_c_rtti_name_info_node")), tkind_TStandard()))))),
    opt_some_container(init_expr_Single_init(expression_cons(copy_loc(loc),
      exp_node_FieldAccess(expression_cons(copy_loc(loc), exp_node_Dereference(
        expression_cons(copy_loc(loc), exp_node_Variable(
          variable_FunctionParameter(strdup("declared_vmt")))))),
        strdup("rtti_info")))))));
//   int shift_vmt, elaborated_shift_vmt = 0, elaborated_shift_object = 0,
//       elaborated_shift_target;
  statementsEnd.insertContainer(statement_VarDecl(copy_loc(loc),
    strdup("shift_vmt"), qual_type_cons(NULL, typ_Int(IINT)), opt_none()));
  statementsEnd.insertContainer(
    statement_VarDecl(
      copy_loc(loc),
      strdup("elaborated_shift_vmt"),
      qual_type_cons(NULL, typ_Int(IINT)),
      opt_some_container(init_expr_Single_init(makeIntLiteral(loc,IINT,0)))));
  statementsEnd.insertContainer(
    statement_VarDecl(
      copy_loc(loc),
      strdup("elaborated_shift_object"),
      qual_type_cons(NULL, typ_Int(IINT)),
      opt_some_container(init_expr_Single_init(makeIntLiteral(loc,IINT,0)))));
  statementsEnd.insertContainer(
    statement_VarDecl(
      copy_loc(loc),
      strdup("elaborated_shift_target"),
      qual_type_cons(NULL, typ_Int(IINT)),
      opt_none()));
//   struct _frama_c_rtti_name_info_content* cursor;
//   int cursor_index = 0, number_of_bases;
//   int distance = -1;
  statementsEnd.insertContainer(statement_VarDecl(copy_loc(loc),
    strdup("cursor"), qual_type_cons(NULL, typ_Pointer(pkind_PDataPointer(
      qual_type_cons(NULL, typ_Struct(qualified_name_cons(NULL,
        strdup("_frama_c_rtti_name_info_content")), tkind_TStandard()))))),
        opt_none()));
  statementsEnd.insertContainer(
    statement_VarDecl(
      copy_loc(loc),
      strdup("cursor_index"),
      qual_type_cons(NULL, typ_Int(IINT)),
      opt_some_container(init_expr_Single_init(makeIntLiteral(loc,IINT,0)))));
  statementsEnd.insertContainer(
    statement_VarDecl(
      copy_loc(loc),
      strdup("number_of_bases"),
      qual_type_cons(NULL, typ_Int(IINT)),
      opt_none()));
  statementsEnd.insertContainer(
    statement_VarDecl(
      copy_loc(loc),
      strdup("distance"),
      qual_type_cons(NULL, typ_Int(IINT)),
      opt_some_container(
        init_expr_Single_init(
          expression_cons(
            copy_loc(loc),
            exp_node_Unary_operator(
              uokind_UOOpposite(),
              makeIntLiteral(loc,IINT,1)))))));

//   if (concrete_info->pvmt > declared_vmt
//       || declared_vmt > concrete_info->pvmt + declared_vmt->table_size)
//     return 0;
  statementsEnd.insertContainer(
    statement_Condition(
      copy_loc(loc),
      cond_statement_CondExpression(
        expression_cons(
          copy_loc(loc),
          exp_node_Binary_operator(
            BOLOGICALOR, AKRVALUE,
            expression_cons(
              copy_loc(loc),
              exp_node_Binary_operator(
                BOGREATER, AKRVALUE,
                expression_cons(
                  copy_loc(loc),
                  exp_node_FieldAccess(
                    expression_cons(
                      copy_loc(loc),
                      exp_node_Dereference(
                        expression_cons(
                          copy_loc(loc),
                          exp_node_Variable(
                            variable_Local(
                              qualified_name_cons(
                                NULL, strdup("concrete_info"))))))),
                    strdup("pvmt"))),
                expression_cons(
                  copy_loc(loc),
                  exp_node_Variable(
                    variable_FunctionParameter(strdup("declared_vmt")))))),
            expression_cons(
              copy_loc(loc),
              exp_node_Binary_operator(
                BOGREATER, AKRVALUE,
                expression_cons(
                  copy_loc(loc),
                  exp_node_Variable(
                    variable_FunctionParameter(strdup("declared_vmt")))),
                expression_cons(
                  copy_loc(loc),
                  exp_node_Binary_operator(
                    BOPLUS, AKRVALUE,
                    expression_cons(
                      copy_loc(loc),
                      exp_node_FieldAccess(
                        expression_cons(
                          copy_loc(loc),
                          exp_node_Dereference(
                            expression_cons(
                              copy_loc(loc),
                              exp_node_Variable(
                                variable_Local(
                                  qualified_name_cons(
                                    NULL, strdup("concrete_info"))))))),
                        strdup("pvmt"))),
                    expression_cons(
                      copy_loc(loc),
                      exp_node_FieldAccess(
                        expression_cons(
                          copy_loc(loc),
                          exp_node_Dereference(
                            expression_cons(
                              copy_loc(loc),
                              exp_node_Variable(
                                variable_FunctionParameter(
                                  strdup("declared_vmt")))))),
                        strdup("table_size")))))))))),
      statement_Return(
        copy_loc(loc),
        opt_some_container(makeIntLiteral(loc,IINT,0))),
      statement_Nop(copy_loc(loc))));
//   shift_vmt = declared_vmt - concrete_info->pvmt;
//     // 0 <= shift_vmt <= table_size
  statementsEnd.insertContainer(statement_Expression(copy_loc(loc),
    expression_cons(copy_loc(loc), exp_node_Assign(
      expression_cons(copy_loc(loc), exp_node_Variable(
        variable_Local(qualified_name_cons(NULL, strdup("shift_vmt"))))),
      expression_cons(copy_loc(loc), exp_node_Binary_operator(BOMINUS, AKRVALUE,
        expression_cons(copy_loc(loc), exp_node_Variable(
          variable_FunctionParameter(strdup("declared_vmt")))),
        expression_cons(copy_loc(loc), exp_node_FieldAccess(expression_cons(
          copy_loc(loc), exp_node_Dereference(expression_cons(copy_loc(loc),
            exp_node_Variable(variable_Local(qualified_name_cons(NULL,
              strdup("concrete_info"))))))), strdup("pvmt")))))))));
//   if (concrete_info == declared_info) {
//     *shift_object = 0;
//     return (target_info == declared_info);
//   };
  /* statement */ list ifThenBody = NULL;
  { ForwardReferenceList ifThenBodyEnd(ifThenBody);
    ifThenBodyEnd.insertContainer(
      statement_Expression(
        copy_loc(loc),
        expression_cons(
          copy_loc(loc),
          exp_node_Assign(
            expression_cons(
              copy_loc(loc),
              exp_node_Dereference(
                expression_cons(
                  copy_loc(loc),
                  exp_node_Variable(
                    variable_FunctionParameter(strdup("shift_object")))))),
            makeIntLiteral(loc,IINT,0)))));
    ifThenBodyEnd.insertContainer(statement_Return(copy_loc(loc),
      opt_some_container(expression_cons(copy_loc(loc),
        exp_node_Binary_operator(BOEQUAL, AKRVALUE,
          expression_cons(copy_loc(loc), exp_node_Variable(
            variable_FunctionParameter(strdup("target_info")))),
          expression_cons(copy_loc(loc), exp_node_Variable(
            variable_FunctionParameter(strdup("declared_info")))))))));
  };
  statementsEnd.insertContainer(statement_Condition(copy_loc(loc),
    cond_statement_CondExpression(expression_cons(copy_loc(loc),
      exp_node_Binary_operator(BOEQUAL, AKRVALUE,
        expression_cons(copy_loc(loc), exp_node_Variable(
          variable_Local(qualified_name_cons(NULL, strdup("concrete_info"))))),
        expression_cons(copy_loc(loc), exp_node_Variable(
          variable_FunctionParameter(strdup("declared_info"))))))),
    statement_Block(copy_loc(loc), ifThenBody),
    statement_Nop(copy_loc(loc))));
//   elaborated_shift_target = (target_info == concrete_info) ? 0 : -1;
  statementsEnd.insertContainer(
    statement_Expression(
      copy_loc(loc),
      expression_cons(
        copy_loc(loc),
        exp_node_Assign(
          expression_cons(
            copy_loc(loc),
            exp_node_Variable(
              variable_Local(
                qualified_name_cons(NULL, strdup("elaborated_shift_target"))))),
          expression_cons(
            copy_loc(loc),
            exp_node_Conditional(
              expression_cons(
                copy_loc(loc),
                exp_node_Binary_operator(
                  BOEQUAL, AKRVALUE,
                  expression_cons(
                    copy_loc(loc),
                    exp_node_Variable(
                      variable_FunctionParameter(strdup("target_info")))),
                  expression_cons(
                    copy_loc(loc),
                    exp_node_Variable(
                      variable_Local(
                        qualified_name_cons(NULL, strdup("concrete_info"))))))),
              makeIntLiteral(loc,IINT,0),
              expression_cons(
                copy_loc(loc),
                exp_node_Unary_operator(
                  uokind_UOOpposite(),
                  makeIntLiteral(loc,IINT,1)))))))));
//   cursor = concrete_info->base_classes;
  statementsEnd.insertContainer(statement_Expression(copy_loc(loc),
    expression_cons(copy_loc(loc), exp_node_Assign(
      expression_cons(copy_loc(loc), exp_node_Variable(variable_Local(
        qualified_name_cons(NULL, strdup("cursor"))))),
      expression_cons(copy_loc(loc), exp_node_FieldAccess(
        expression_cons(copy_loc(loc), exp_node_Dereference(
          expression_cons(copy_loc(loc), exp_node_Variable(variable_Local(
            qualified_name_cons(NULL, strdup("concrete_info"))))))),
          strdup("base_classes")))))));
//   number_of_bases = concrete_info->number_of_base_classes;
  statementsEnd.insertContainer(statement_Expression(copy_loc(loc),
    expression_cons(copy_loc(loc), exp_node_Assign(
      expression_cons(copy_loc(loc), exp_node_Variable(variable_Local(
        qualified_name_cons(NULL, strdup("number_of_bases"))))),
      expression_cons(copy_loc(loc), exp_node_FieldAccess(
        expression_cons(copy_loc(loc), exp_node_Dereference(
          expression_cons(copy_loc(loc), exp_node_Variable(variable_Local(
            qualified_name_cons(NULL, strdup("concrete_info"))))))),
          strdup("number_of_base_classes")))))));
  return statementsEnd.getBack() ? &statementsEnd.getBack()->next : NULL;
}

/* statement */ list*
RTTITable::insertRTTIAlgorithmsDoWhilePrelude(/* statement */ list*&
    statements, location loc) {
  ForwardReferenceList statementsEnd(*statements);
//   do { ...  } while (cursor_index < number_of_bases);
  statement doWhileBody = statement_Block(copy_loc(loc), NULL);
  statementsEnd.insertContainer(statement_DoWhile(copy_loc(loc),
    expression_cons(copy_loc(loc), exp_node_Binary_operator(BOLESS,
      AKRVALUE, expression_cons(copy_loc(loc), exp_node_Variable(variable_Local(
        qualified_name_cons(NULL, strdup("cursor_index"))))),
      expression_cons(copy_loc(loc), exp_node_Variable(variable_Local(
        qualified_name_cons(NULL, strdup("number_of_bases"))))))),
    doWhileBody, NULL));
  statements = statementsEnd.getBack() ? &statementsEnd.getBack()->next : NULL;
  return (/*statement */ list*) &doWhileBody->cons_statement.Block.instructions;
}

/* statement */ list*
RTTITable::insertRTTIAlgorithmsSecondWhilePrelude(/* statement */ list*&
    statements, location loc) {
//     while ((cursor_index < number_of_bases)
//         && (elaborated_shift_vmt+cursor->shift_vmt < shift_vmt))
//     { ... };
  ForwardReferenceList statementsEnd(*statements);
  statement whileBody = statement_Block(copy_loc(loc), NULL);
  statementsEnd.insertContainer(statement_While(copy_loc(loc),
    expression_cons(copy_loc(loc), exp_node_Binary_operator(BOLOGICALAND,
      AKRVALUE, expression_cons(copy_loc(loc), exp_node_Binary_operator(
        BOLESS, AKRVALUE, expression_cons(copy_loc(loc), exp_node_Variable(
          variable_Local(qualified_name_cons(NULL, strdup("cursor_index"))))),
        expression_cons(copy_loc(loc), exp_node_Variable(variable_Local(
          qualified_name_cons(NULL, strdup("number_of_bases"))))))),
      expression_cons(copy_loc(loc), exp_node_Binary_operator(BOLESS, AKRVALUE,
        expression_cons(copy_loc(loc), exp_node_Binary_operator(BOPLUS,
          AKRVALUE, expression_cons(copy_loc(loc), exp_node_Variable(
            variable_Local(qualified_name_cons(NULL,
              strdup("elaborated_shift_vmt"))))),
          expression_cons(copy_loc(loc), exp_node_FieldAccess(expression_cons(
            copy_loc(loc), exp_node_Dereference(expression_cons(copy_loc(loc),
              exp_node_Variable(variable_Local(qualified_name_cons(NULL,
                strdup("cursor"))))))), strdup("shift_vmt"))))),
        expression_cons(copy_loc(loc), exp_node_Variable(variable_Local(
          qualified_name_cons(NULL, strdup("shift_vmt"))))))))),
    whileBody, NULL /* annot */));
  statements = statementsEnd.getBack() ? &statementsEnd.getBack()->next : NULL;
  return (/* statement */ list*) &whileBody->cons_statement.Block.instructions;
}

void
RTTITable::insertRTTIAlgorithmsSecondWhileBodyPrelude(/* statement */ list*&
    statements, location loc) {
  ForwardReferenceList statementsEnd(*statements);
//       struct _frama_c_rtti_name_info_content* next_cursor
//         = (cursor_index < number_of_bases-1) ? (cursor+1)
//             : (struct _frama_c_rtti_name_info_content*) 0;
  statementsEnd.insertContainer(
    statement_VarDecl(
      copy_loc(loc),
      strdup("next_cursor"),
      qual_type_cons(
        NULL,
        typ_Pointer(
          pkind_PDataPointer(
            qual_type_cons(
              NULL,
              typ_Struct(
                qualified_name_cons(
                  NULL, strdup("_frama_c_rtti_name_info_content")),
                tkind_TStandard()))))),
      opt_some_container(
        init_expr_Single_init(
          expression_cons(
            copy_loc(loc),
            exp_node_Conditional(
              expression_cons(
                copy_loc(loc),
                exp_node_Binary_operator(
                  BOLESS, AKRVALUE,
                  expression_cons(
                    copy_loc(loc),
                    exp_node_Variable(
                      variable_Local(
                        qualified_name_cons(NULL, strdup("cursor_index"))))),
                  expression_cons(
                    copy_loc(loc),
                    exp_node_Binary_operator(
                      BOMINUS, AKRVALUE,
                      expression_cons(
                        copy_loc(loc),
                        exp_node_Variable(
                          variable_Local(
                            qualified_name_cons(
                              NULL, strdup("number_of_bases"))))),
                      makeIntLiteral(loc,IINT,1))))),
              expression_cons(
                copy_loc(loc),
                exp_node_Binary_operator(
                  BOPLUS, AKRVALUE,
                  expression_cons(
                    copy_loc(loc),
                    exp_node_Variable(
                      variable_Local(
                        qualified_name_cons(NULL, strdup("cursor"))))),
                  makeIntLiteral(loc,IINT,1))),
              makeNullPointer(
                loc,
                makeStructType(
                  qualified_name_cons(
                    NULL,strdup("_frama_c_rtti_name_info_content"))))))))));
//       if (next_cursor
//           && (elaborated_shift_vmt + next_cursor->shift_vmt <= shift_vmt)) {
//         cursor = next_cursor;
//         cursor_index = cursor_index + 1;
//       }
//       else
//         break;
  statement lastCondition =
    statement_Condition(
      copy_loc(loc),
      cond_statement_CondExpression(
        expression_cons(
          copy_loc(loc),
          exp_node_Binary_operator(
            BOLOGICALAND, AKRVALUE,
            expression_cons(
              copy_loc(loc),
              exp_node_Binary_operator(
                BODIFFERENT, AKRVALUE,
                expression_cons(
                  copy_loc(loc),
                  exp_node_Variable(
                    variable_Local(
                      qualified_name_cons(NULL, strdup("next_cursor"))))),
                makeNullPointer(
                  loc,
                  makeStructType(
                    qualified_name_cons(
                      NULL,strdup("_frama_c_rtti_name_info_content")))))),
            expression_cons(
              copy_loc(loc),
              exp_node_Binary_operator(
                BOLESSOREQUAL, AKRVALUE,
                expression_cons(
                  copy_loc(loc),
                  exp_node_Binary_operator(
                    BOPLUS, AKRVALUE,
                    expression_cons(
                      copy_loc(loc),
                      exp_node_Variable(
                        variable_Local(
                          qualified_name_cons(
                            NULL, strdup("elaborated_shift_vmt"))))),
                    expression_cons(
                      copy_loc(loc),
                      exp_node_FieldAccess(
                        expression_cons(
                          copy_loc(loc),
                          exp_node_Dereference(
                            expression_cons(
                              copy_loc(loc),
                              exp_node_Variable(
                                variable_Local(
                                  qualified_name_cons(
                                    NULL, strdup("next_cursor"))))))),
                        strdup("shift_vmt"))))),
                expression_cons(
                  copy_loc(loc),
                  exp_node_Variable(
                    variable_Local(
                      qualified_name_cons(NULL, strdup("shift_vmt")))))))))),
      statement_Block(copy_loc(loc), NULL), 
      statement_Break(copy_loc(loc)));

  ForwardReferenceList lastConditionThenBlock(lastCondition->cons_statement
    .Condition.then_instruction->cons_statement.Block.instructions);
  lastConditionThenBlock.insertContainer(statement_Expression(copy_loc(loc),
    expression_cons(copy_loc(loc), exp_node_Assign(
      expression_cons(copy_loc(loc), exp_node_Variable(
        variable_Local(qualified_name_cons(NULL, strdup("cursor"))))),
      expression_cons(copy_loc(loc), exp_node_Variable(variable_Local(
        qualified_name_cons(NULL, strdup("next_cursor")))))))));
  lastConditionThenBlock.insertContainer(
    statement_Expression(
      copy_loc(loc),
      expression_cons(
        copy_loc(loc),
        exp_node_Assign(
          expression_cons(
            copy_loc(loc),
            exp_node_Variable(
              variable_Local(
                qualified_name_cons(NULL, strdup("cursor_index"))))),
          expression_cons(
            copy_loc(loc),
            exp_node_Binary_operator(
              BOPLUS, AKRVALUE,
              expression_cons(
                copy_loc(loc),
                exp_node_Variable(
                  variable_Local(
                    qualified_name_cons(NULL, strdup("cursor_index"))))),
              makeIntLiteral(loc,IINT,1)))))));
  statementsEnd.insertContainer(lastCondition);
  statements = statementsEnd.getBack() ? &statementsEnd.getBack()->next : NULL;
}

/* statement */ list*
RTTITable::insertRTTIAlgorithmsSecondIfThenPrelude(/* statement */ list*&
    statements, location loc) {
  ForwardReferenceList statementsEnd(*statements);
//     if (cursor_index < number_of_bases) { ... };
  statement thenBlock = statement_Block(copy_loc(loc), NULL);
  statementsEnd.insertContainer(statement_Condition(copy_loc(loc),
    cond_statement_CondExpression(expression_cons(copy_loc(loc),
      exp_node_Binary_operator(BOLESS, AKRVALUE,
        expression_cons(copy_loc(loc), exp_node_Variable(variable_Local(
          qualified_name_cons(NULL, strdup("cursor_index"))))),
        expression_cons(copy_loc(loc), exp_node_Variable(variable_Local(
          qualified_name_cons(NULL, strdup("number_of_bases")))))))),
    thenBlock, statement_Nop(copy_loc(loc))));
  statements = statementsEnd.getBack() ? &statementsEnd.getBack()->next : NULL;
  return (/* statement */ list*) &thenBlock->cons_statement.Block.instructions;
}

void
RTTITable::insertRTTIAlgorithmsSecondIfThenBodyPrelude(/* statement */ list*&
    statements, location loc) {
  ForwardReferenceList statementsEnd(*statements);
//       elaborated_shift_vmt += cursor->shift_vmt;
  statementsEnd.insertContainer(statement_Expression(copy_loc(loc),
    expression_cons(copy_loc(loc), exp_node_Binary_operator(BOPLUS,
      AKASSIGN, expression_cons(copy_loc(loc), exp_node_Variable(
        variable_Local(qualified_name_cons(NULL,
          strdup("elaborated_shift_vmt"))))),
      expression_cons(copy_loc(loc), exp_node_FieldAccess(expression_cons(
        copy_loc(loc), exp_node_Dereference(expression_cons(copy_loc(loc),
          exp_node_Variable(variable_Local(qualified_name_cons(NULL,
            strdup("cursor"))))))), strdup("shift_vmt")))))));
//       elaborated_shift_object += cursor->shift_object;
  statementsEnd.insertContainer(statement_Expression(copy_loc(loc),
    expression_cons(copy_loc(loc), exp_node_Binary_operator(BOPLUS,
      AKASSIGN, expression_cons(copy_loc(loc), exp_node_Variable(
        variable_Local(qualified_name_cons(NULL,
          strdup("elaborated_shift_object"))))),
      expression_cons(copy_loc(loc), exp_node_FieldAccess(expression_cons(
        copy_loc(loc), exp_node_Dereference(expression_cons(copy_loc(loc),
          exp_node_Variable(variable_Local(qualified_name_cons(NULL,
            strdup("cursor"))))))), strdup("shift_object")))))));
//       if (cursor->value == target_info)
//         elaborated_shift_target = elaborated_shift_object;
  statementsEnd.insertContainer(
    statement_Condition(
      copy_loc(loc),
      cond_statement_CondExpression(
        expression_cons(
          copy_loc(loc),
          exp_node_Binary_operator(
            BOEQUAL, AKRVALUE,
            expression_cons(
              copy_loc(loc),
              exp_node_FieldAccess(
                expression_cons(
                  copy_loc(loc),
                  exp_node_Dereference(
                    expression_cons(
                      copy_loc(loc),
                      exp_node_Variable(
                        variable_Local(
                          qualified_name_cons(NULL, strdup("cursor"))))))),
                strdup("value"))),
            expression_cons(
              copy_loc(loc),
              exp_node_Variable(
                variable_FunctionParameter(strdup("target_info"))))))),
      statement_Expression(
        copy_loc(loc),
        expression_cons(
          copy_loc(loc),
          exp_node_Assign(
            expression_cons(
              copy_loc(loc),
              exp_node_Variable(
                variable_Local(
                  qualified_name_cons(
                    NULL, strdup("elaborated_shift_target"))))),
            expression_cons(
              copy_loc(loc),
              exp_node_Variable(
                variable_Local(
                  qualified_name_cons(
                    NULL, strdup("elaborated_shift_object")))))))),
      statement_Nop(copy_loc(loc))));
//       if (elaborated_shift_vmt == shift_vmt
//           && cursor->value == declared_info) {
//         if (elaborated_shift_target >= 0) {
//           *shift_object = elaborated_shift_target-elaborated_shift_object;
//           return 1;
//         };
//         break;
//       };
  /* statement */ list innerIfThenBody = NULL;
  ForwardReferenceList innerIfThenBodyEnd(innerIfThenBody);
  innerIfThenBodyEnd.insertContainer(statement_Expression(copy_loc(loc),
    expression_cons(copy_loc(loc), exp_node_Assign(
      expression_cons(copy_loc(loc), exp_node_Dereference(expression_cons(
        copy_loc(loc), exp_node_Variable(variable_FunctionParameter(
          strdup("shift_object")))))),
      expression_cons(copy_loc(loc), exp_node_Binary_operator(BOMINUS, AKRVALUE,
        expression_cons(copy_loc(loc), exp_node_Variable(variable_Local(
          qualified_name_cons(NULL, strdup("elaborated_shift_target"))))),
        expression_cons(copy_loc(loc), exp_node_Variable(variable_Local(
          qualified_name_cons(NULL, strdup("elaborated_shift_object")))))))))));
  innerIfThenBodyEnd.insertContainer(
    statement_Return(
      copy_loc(loc),
      opt_some_container(makeIntLiteral(loc,IINT,1))));

  /* statement */ list ifThenBody = NULL;
  ForwardReferenceList ifThenBodyEnd(ifThenBody);
  ifThenBodyEnd.insertContainer(
    statement_Condition(
      copy_loc(loc),
      cond_statement_CondExpression(
        expression_cons(
          copy_loc(loc),
          exp_node_Binary_operator(
            BOGREATEROREQUAL, AKRVALUE,
            expression_cons(
              copy_loc(loc),
              exp_node_Variable(
                variable_Local(
                  qualified_name_cons(
                    NULL, strdup("elaborated_shift_target"))))),
            makeIntLiteral(loc,IINT,0)))),
      statement_Block(copy_loc(loc), innerIfThenBody),
      statement_Nop(copy_loc(loc))));
  ifThenBodyEnd.insertContainer(statement_Break(copy_loc(loc)));

  statementsEnd.insertContainer(
    statement_Condition(
      copy_loc(loc),
      cond_statement_CondExpression(
        expression_cons(
          copy_loc(loc),
          exp_node_Binary_operator(
            BOLOGICALAND, AKRVALUE,
            expression_cons(
              copy_loc(loc),
              exp_node_Binary_operator(
                BOEQUAL,
                AKRVALUE,
                expression_cons(
                  copy_loc(loc),
                  exp_node_Variable(
                    variable_Local(
                      qualified_name_cons(
                        NULL, strdup("elaborated_shift_vmt"))))),
                expression_cons(
                  copy_loc(loc),
                  exp_node_Variable(
                    variable_Local(
                      qualified_name_cons(NULL, strdup("shift_vmt"))))))),
            expression_cons(
              copy_loc(loc),
              exp_node_Binary_operator(
                BOEQUAL, AKRVALUE,
                expression_cons(
                  copy_loc(loc),
                  exp_node_FieldAccess(
                    expression_cons(
                      copy_loc(loc),
                      exp_node_Dereference(
                        expression_cons(
                          copy_loc(loc),
                          exp_node_Variable(
                            variable_Local(
                              qualified_name_cons(NULL, strdup("cursor"))))))),
                    strdup("value"))),
                expression_cons(
                  copy_loc(loc),
                  exp_node_Variable(
                    variable_FunctionParameter(strdup("declared_info"))))))))),
      statement_Block(copy_loc(loc), ifThenBody),
      statement_Nop(copy_loc(loc))));

//       cursor = cursor->value->base_classes;
  statementsEnd.insertContainer(statement_Expression(copy_loc(loc),
    expression_cons(copy_loc(loc), exp_node_Assign(
      expression_cons(copy_loc(loc), exp_node_Variable(variable_Local(
        qualified_name_cons(NULL, strdup("cursor"))))),
      expression_cons(copy_loc(loc), exp_node_FieldAccess(
        expression_cons(copy_loc(loc), exp_node_Dereference(
          expression_cons(copy_loc(loc), exp_node_FieldAccess(
            expression_cons(copy_loc(loc), exp_node_Dereference(
              expression_cons(copy_loc(loc), exp_node_Variable(variable_Local(
                qualified_name_cons(NULL, strdup("cursor"))))))),
            strdup("value"))))),
        strdup("base_classes")))))));
//       number_of_bases = cursor->value->number_of_base_classes;
  statementsEnd.insertContainer(statement_Expression(copy_loc(loc),
    expression_cons(copy_loc(loc), exp_node_Assign(
      expression_cons(copy_loc(loc), exp_node_Variable(variable_Local(
        qualified_name_cons(NULL, strdup("number_of_bases"))))),
      expression_cons(copy_loc(loc), exp_node_FieldAccess(
        expression_cons(copy_loc(loc), exp_node_Dereference(
          expression_cons(copy_loc(loc), exp_node_FieldAccess(
            expression_cons(copy_loc(loc), exp_node_Dereference(
              expression_cons(copy_loc(loc), exp_node_Variable(variable_Local(
                qualified_name_cons(NULL, strdup("cursor"))))))),
            strdup("value"))))),
        strdup("number_of_base_classes")))))));
//       cursor_index = 0;
  statementsEnd.insertContainer(
    statement_Expression(
      copy_loc(loc),
      expression_cons(
        copy_loc(loc),
        exp_node_Assign(
          expression_cons(
            copy_loc(loc),
            exp_node_Variable(
              variable_Local(
                qualified_name_cons(NULL, strdup("cursor_index"))))),
          makeIntLiteral(loc,IINT,0)))));

  statements = statementsEnd.getBack() ? &statementsEnd.getBack()->next : NULL;
}

void
RTTITable::insertRTTIAlgorithmsLastPartPrelude(/* statement */ list*&
    statements, location loc) {
  ForwardReferenceList statementsEnd(*statements);
//   if (cursor_index >= number_of_bases)
//     return 0;
  statementsEnd.insertContainer(
    statement_Condition(
      copy_loc(loc),
      cond_statement_CondExpression(
        expression_cons(
          copy_loc(loc),
          exp_node_Binary_operator(
            BOGREATEROREQUAL, AKRVALUE,
            expression_cons(
              copy_loc(loc),
              exp_node_Variable(
                variable_Local(
                  qualified_name_cons(NULL, strdup("cursor_index"))))),
            expression_cons(
              copy_loc(loc),
              exp_node_Variable(
                variable_Local(
                  qualified_name_cons(NULL, strdup("number_of_bases")))))))),
      statement_Return(
        copy_loc(loc),
        opt_some_container(makeIntLiteral(loc,IINT,0))),
      statement_Nop(copy_loc(loc))));
//   // elaborated_shift_target == -1 && cursor->value == target_info
//   //   && elaborated_shift_vmt == shift_vmt
//   return _frama_c_find_dynamic_cast_aux(target_info,
//     concrete_info->base_classes,
//     concrete_info->number_of_base_classes,
//     elaborated_shift_object, shift_vmt, -1, shift_object, &distance);
  /* qual_type */ list parameters = NULL;
  ForwardReferenceList parametersEnd(parameters);
  parametersEnd.insertContainer(qual_type_cons(NULL, typ_Pointer(
    pkind_PDataPointer(qual_type_cons(NULL, typ_Struct(qualified_name_cons(
      NULL, strdup("_frama_c_rtti_name_info_node")), tkind_TStandard()))))));
  parametersEnd.insertContainer(qual_type_cons(NULL, typ_Pointer(
    pkind_PDataPointer(qual_type_cons(NULL, typ_Struct(qualified_name_cons(
      NULL, strdup("_frama_c_rtti_name_info_content")), tkind_TStandard()))))));
  parametersEnd.insertContainer(qual_type_cons(NULL, typ_Int(IINT)));
  parametersEnd.insertContainer(qual_type_cons(NULL, typ_Int(IINT)));
  parametersEnd.insertContainer(qual_type_cons(NULL, typ_Int(IINT)));
  parametersEnd.insertContainer(qual_type_cons(NULL, typ_Int(IINT)));
  parametersEnd.insertContainer(qual_type_cons(NULL, typ_Pointer(
    pkind_PDataPointer(qual_type_cons(NULL, typ_Int(IINT))))));
  parametersEnd.insertContainer(qual_type_cons(NULL, typ_Pointer(
    pkind_PDataPointer(qual_type_cons(NULL, typ_Int(IINT))))));

  /* expression */ list arguments = NULL;
  ForwardReferenceList argumentsEnd(arguments);
  argumentsEnd.insertContainer(expression_cons(copy_loc(loc), exp_node_Variable(
    variable_FunctionParameter(strdup("target_info")))));
  argumentsEnd.insertContainer(expression_cons(copy_loc(loc),
    exp_node_FieldAccess(expression_cons(copy_loc(loc), exp_node_Dereference(
      expression_cons(copy_loc(loc), exp_node_Variable(variable_Local(
        qualified_name_cons(NULL, strdup("concrete_info"))))))),
      strdup("base_classes"))));
  argumentsEnd.insertContainer(expression_cons(copy_loc(loc),
    exp_node_FieldAccess(expression_cons(copy_loc(loc), exp_node_Dereference(
      expression_cons(copy_loc(loc), exp_node_Variable(variable_Local(
        qualified_name_cons(NULL, strdup("concrete_info"))))))),
      strdup("number_of_base_classes"))));
  argumentsEnd.insertContainer(expression_cons(copy_loc(loc), exp_node_Variable(
    variable_Local(qualified_name_cons(NULL,
      strdup("elaborated_shift_object"))))));
  argumentsEnd.insertContainer(expression_cons(copy_loc(loc), exp_node_Variable(
    variable_Local(qualified_name_cons(NULL, strdup("shift_vmt"))))));
  argumentsEnd.insertContainer(
    expression_cons(
      copy_loc(loc),
      exp_node_Unary_operator(
        uokind_UOOpposite(),
        makeIntLiteral(loc,IINT,1))));
  argumentsEnd.insertContainer(expression_cons(copy_loc(loc), exp_node_Variable(
    variable_FunctionParameter(strdup("shift_object")))));
  argumentsEnd.insertContainer(expression_cons(copy_loc(loc), exp_node_Address(
    expression_cons(copy_loc(loc), exp_node_Variable(variable_Local(
      qualified_name_cons(NULL, strdup("distance"))))))));
  
  statementsEnd.insertContainer(
    statement_Return(
      copy_loc(loc),
      opt_some_container(
        expression_cons(
          copy_loc(loc),
          exp_node_Static_call(
            qualified_name_cons(NULL, strdup("_frama_c_find_dynamic_cast_aux")),
            signature_cons(
              qual_type_cons(NULL, typ_Int(IINT)), parameters, false),
            funkind_FKFunction(),
            arguments, tkind_TStandard(), false /* extern_c_call */)))));

  statements = statementsEnd.getBack() ? &statementsEnd.getBack()->next : NULL;
}

// int _frama_c_find_dynamic_cast(
//   struct _frama_c_rtti_name_info_node* declared_info,
//   struct _frama_c_vmt* declared_vmt, 
//   struct _frama_c_rtti_name_info_node* target_info,
//   int* shift_object)
// { struct _frama_c_rtti_name_info_node*
//     concrete_info = declared_vmt->rtti_info;
//   int shift_vmt, elaborated_shift_vmt = 0, elaborated_shift_object = 0,
//       elaborated_shift_target;
//   struct _frama_c_rtti_name_info_content* cursor;
//   int cursor_index = 0, number_of_bases;
//   int distance = -1;
//   if (concrete_info->pvmt > declared_vmt
//       || declared_vmt > concrete_info->pvmt + declared_vmt->table_size)
//     return 0;
//   shift_vmt = declared_vmt - concrete_info->pvmt;
//     // 0 <= shift_vmt <= table_size
//   if (concrete_info == declared_info) {
//     *shift_object = 0;
//     return (target_info == declared_info);
//   };
//   elaborated_shift_target = (target_info == concrete_info) ? 0 : -1;
//   cursor = concrete_info->base_classes;
//   number_of_bases = concrete_info->number_of_base_classes;
//   do {
//     while ((cursor_index < number_of_bases)
//         && (elaborated_shift_vmt+cursor->shift_vmt < shift_vmt))
//     { struct _frama_c_rtti_name_info_content* next_cursor
//         = (cursor_index < number_of_bases-1) ? (cursor+1)
//             : (struct _frama_c_rtti_name_info_content*) 0;
//       if (next_cursor
//           && (elaborated_shift_vmt + next_cursor->shift_vmt <= shift_vmt)) {
//         cursor = next_cursor;
//         cursor_index = cursor_index + 1;
//       }
//       else
//         break;
//     };
//     if (cursor_index < number_of_bases) {
//       elaborated_shift_vmt += cursor->shift_vmt;
//       elaborated_shift_object += cursor->shift_object;
//       if (cursor->value == target_info)
//         elaborated_shift_target = elaborated_shift_object;
//       if (elaborated_shift_vmt == shift_vmt
//           && cursor->value == declared_info) {
//         if (elaborated_shift_target >= 0) {
//           *shift_object = elaborated_shift_target-elaborated_shift_object;
//           return 1;
//         };
//         break;
//       };
//       cursor = cursor->value->base_classes;
//       number_of_bases = cursor->value->number_of_base_classes;
//       cursor_index = 0;
//     };
//   } while (cursor_index < number_of_bases);
//   if (cursor_index >= number_of_bases)
//     return 0;
//   // elaborated_shift_target == -1 && cursor->value == target_info
//   //   && elaborated_shift_vmt == shift_vmt
//   return _frama_c_find_dynamic_cast_aux(target_info,
//     concrete_info->base_classes,
//     concrete_info->number_of_base_classes,
//     elaborated_shift_object, shift_vmt, -1, shift_object, &distance);
// }

/* statement */ list*
RTTITable::insertRTTIAlgorithmsPrelude(ForwardReferenceList& globals,
    location loc) {
  /* statement */ list* functionBody = insertRTTIAlgorithmsDeclPrelude(
      globals, loc);
  functionBody = insertRTTIAlgorithmsFirstPartPrelude(functionBody,
      loc);
  /* statement */ list* loopDoBody = insertRTTIAlgorithmsDoWhilePrelude(
      functionBody, loc);
  /* statement */ list* loopSecondWhileBody
    = insertRTTIAlgorithmsSecondWhilePrelude(loopDoBody, loc);
  insertRTTIAlgorithmsSecondWhileBodyPrelude(loopSecondWhileBody, loc);
  /* statement */ list* loopSecondIfThenBody
    = insertRTTIAlgorithmsSecondIfThenPrelude(loopDoBody, loc);
  insertRTTIAlgorithmsSecondIfThenBodyPrelude(loopSecondIfThenBody,
      loc);
  insertRTTIAlgorithmsLastPartPrelude(functionBody, loc);
  return functionBody;
}

void
RTTITable::insertVMTAndRttiPrelude(ForwardReferenceList& globals, location loc)
{ // globals types
  insertVMTContentPrelude(globals, loc);

  struct _frama_c_rtti_name_info_node;
  { globals.insertContainer(
      translation_unit_decl_Compound(
        copy_loc(loc),
        decl_or_impl_name_Implementation(
          qualified_name_cons(NULL, strdup("_frama_c_rtti_name_info_node"))),
        CSTRUCT, opt_none(),
        opt_none(), false, tkind_TStandard(), false, false));
  };
  
  insertVMTTypePrelude(globals, loc);
  insertRTTIInfoPrelude(globals, loc);
}

void
RTTITable::insertRttiPrelude(ForwardReferenceList& globals, location loc) {
  insertRTTIAlgorithmsAuxPrelude(globals, loc);
  insertRTTIAlgorithmsPrelude(globals, loc);
}

expression
RTTITable::getPvmt(const Clang_utils& utils, const clang::CXXRecordDecl* source,
    expression arg) const {
  const ClassInfo* sourceInfo = getClassInfo(source);
  assert(sourceInfo);
  const InheritancePath* accessToPvmt =
      sourceInfo->hasPvmtAsFirstField()
    ? NULL : &sourceInfo->getPvmtField();
  if (accessToPvmt) {
    InheritancePath::const_reverse_iterator
        iterEnd = accessToPvmt->rend(), iter = accessToPvmt->rbegin();
    for (; iter != iterEnd; ++iter) {
      const clang::CXXRecordDecl* baseClass = iter->first;
      tkind baseTemplate = utils.makeTemplateKind(baseClass);
      arg = expression_cons(copy_loc(arg->eloc),
        exp_node_PointerCast(qual_type_cons(NULL,
          typ_Pointer(pkind_PDataPointer(qual_type_cons(NULL,
            typ_Struct(utils.makeQualifiedName(*baseClass),
              baseTemplate))))),
          reference_or_pointer_kind_RPKStaticBasePointer(),
          arg));
    };
  };
  return expression_cons(copy_loc(arg->eloc),
    exp_node_Dereference(expression_cons(copy_loc(arg->eloc),
      exp_node_PointerCast(qual_type_cons(NULL, typ_Pointer(pkind_PDataPointer(
        qual_type_cons(NULL, typ_Pointer(pkind_PDataPointer(
          qual_type_cons(NULL, typ_Struct(qualified_name_cons(NULL,
            strdup("_frama_c_vmt")), tkind_TStandard())))))))),
      reference_or_pointer_kind_RPKPointer(), arg))));
}

void
RTTITable::addPvmtSetter(const Clang_utils& utils,
    const clang::CXXRecordDecl* source, /* statement */ list& insertionPoint, 
    location loc) {
  //   this->pvmt = &...::_frama_c_vmt_header;
  // translated into
  //   *((_frama_c_vmt**) this) = &...::_frama_c_vmt_header;
  const clang::CXXRecordDecl* currentClass = _currentClass.empty() ? NULL
      : _currentClass.front();
  assert(!currentClass || currentClass == source);
  const ClassInfo* currentClassInfo;
  if (currentClass != source) {
    currentClass = source;
    std::map<const clang::CXXRecordDecl*, ClassInfo>::const_iterator
      found = _classInfoTable.find(source);
    assert(found != _classInfoTable.end());
    currentClassInfo = &found->second;
  }
  else
    currentClassInfo = &_currentClassInfo.front();

  const clang::ClassTemplateSpecializationDecl* currentTSD = llvm::dyn_cast
    <clang::ClassTemplateSpecializationDecl>(currentClass);
  qualified_name vmtName = utils.makeQualifiedName(*currentClass);
  { /* qualification */ list* endQualif = &vmtName->prequalification;
    while (*endQualif) endQualif = &(*endQualif)->next;
    if (currentTSD)
      *endQualif = cons_container(qualification_QTemplateInstance(
          const_cast<char*>(vmtName->decl_name), utils
            .getTemplateExtension(currentTSD)), NULL);
    else
      *endQualif = cons_container(qualification_QStructOrClass(
          const_cast<char*>(vmtName->decl_name)), NULL);
  };
  vmtName->decl_name = strdup("_frama_c_vmt_header");
  const InheritancePath* accessToPvmt =
      currentClassInfo->hasPvmtAsFirstField()
    ? NULL : &currentClassInfo->getPvmtField();
  expression startPvmt = expression_cons(copy_loc(loc), exp_node_Variable(
     variable_FunctionParameter(strdup("this"))));
  if (accessToPvmt) {
    InheritancePath::const_reverse_iterator
        iterEnd = accessToPvmt->rend(), iter = accessToPvmt->rbegin();
    for (; iter != iterEnd; ++iter) {
      const clang::CXXRecordDecl* baseClass = iter->first;
      tkind baseTemplate = utils.makeTemplateKind(baseClass);
      startPvmt = expression_cons(copy_loc(loc),
        exp_node_PointerCast(qual_type_cons(NULL,
          typ_Pointer(pkind_PDataPointer(qual_type_cons(NULL,
            typ_Struct(utils.makeQualifiedName(*baseClass),
              baseTemplate))))),
          reference_or_pointer_kind_RPKStaticBasePointer(),
          startPvmt));
    };
  };
  // *((_frama_c_vmt **)this) = & ...::_frama_c_vmt_header;
  insertionPoint = cons_container(
    statement_Expression(copy_loc(loc), expression_cons(copy_loc(loc),
      exp_node_Assign(
        expression_cons(copy_loc(loc), exp_node_Dereference(
          expression_cons(copy_loc(loc), exp_node_PointerCast(
            qual_type_cons(NULL, typ_Pointer(pkind_PDataPointer(
              qual_type_cons(NULL, typ_Pointer(pkind_PDataPointer(
                qual_type_cons(NULL, typ_Struct(qualified_name_cons(NULL,
                  strdup("_frama_c_vmt")), tkind_TStandard())))))))),
            reference_or_pointer_kind_RPKPointer(), startPvmt)))),
        expression_cons(copy_loc(loc), exp_node_Address(
          expression_cons(copy_loc(loc), exp_node_Variable(
            variable_Global(vmtName)))))))), insertionPoint);
  list* endInsertionPoint = &insertionPoint->next;

  InheritancePosition::const_iterator derivationIterEnd =
    currentClassInfo->_derivationsPosition.end();
  int oldPosition = 0;
  for (InheritancePosition::const_iterator
         derivationIter = currentClassInfo->_derivationsPosition.begin();
       derivationIter != derivationIterEnd; ++derivationIter) {
    if (derivationIter->second > oldPosition) {
      oldPosition = derivationIter->second;
      qualified_name vmtNameShift = qualified_name_dup(vmtName);
      { std::ostringstream tmp;
        tmp << "_frama_c_vmt_header_for_shift_"
            << derivationIter->second;
        free(const_cast<char*>(vmtNameShift->decl_name));
        vmtNameShift->decl_name = strdup(tmp.str().c_str());
      };
      // *((_frama_c_vmt **) & this->_frama_c_...)
      //    = & __::_frama_c_vmt_header_for_shift_...;
      qualified_name baseName = utils.makeQualifiedName(*derivationIter->first);
      tkind derived_kind = utils.makeTemplateKind(derivationIter->first);
      *endInsertionPoint = cons_container(
        statement_Expression(copy_loc(loc), expression_cons(copy_loc(loc),
          exp_node_Assign(
            expression_cons(copy_loc(loc), exp_node_Dereference(
              expression_cons(copy_loc(loc), exp_node_PointerCast(
                qual_type_cons(NULL, typ_Pointer(pkind_PDataPointer(
                  qual_type_cons(NULL, typ_Pointer(pkind_PDataPointer(
                    qual_type_cons(NULL, typ_Struct(qualified_name_cons(NULL,
                      strdup("_frama_c_vmt")), tkind_TStandard())))))))),
                reference_or_pointer_kind_RPKPointer(),
                expression_cons(copy_loc(loc), exp_node_PointerCast(
                  qual_type_cons(NULL, typ_Pointer(pkind_PDataPointer(
                    qual_type_cons(NULL, typ_Struct(baseName, derived_kind))))),
                  reference_or_pointer_kind_RPKStaticBasePointer(),
                  expression_cons(copy_loc(loc), exp_node_Variable(
                        variable_FunctionParameter(strdup("this")))))))))),
          expression_cons(copy_loc(loc), exp_node_Address(
            expression_cons(copy_loc(loc), exp_node_Variable(
              variable_Global(vmtNameShift)))))))), *endInsertionPoint);
      endInsertionPoint = &((*endInsertionPoint)->next);
    };
  };

  if (!currentClassInfo->_virtualDerivationsPosition.empty()) {
    VirtualInheritancePosition::const_iterator iterEnd =
      currentClassInfo->_virtualDerivationsPosition.end(), iter;
    int oldPosition = 0;
    std::vector<const clang::CXXRecordDecl*>::const_iterator
      virtualBaseIterEnd = currentClassInfo->_virtualBaseClassTable.end(),
      virtualBaseIter = currentClassInfo->_virtualBaseClassTable.begin();

    for (iter = currentClassInfo->_virtualDerivationsPosition.begin();
         iter != iterEnd; ++iter) {
      assert(virtualBaseIter != virtualBaseIterEnd);
      if (*iter > oldPosition) {
        oldPosition = *iter;
        qualified_name vmtNameShift = qualified_name_dup(vmtName);
        { std::ostringstream tmp;
          tmp << "_frama_c_vmt_header_for_shift_" << *iter;
          free(const_cast<char*>(vmtNameShift->decl_name));
          vmtNameShift->decl_name = strdup(tmp.str().c_str());
        };
        // *((_frama_c_vmt **) & this->_frama_c_...)
        //    = & __::_frama_c_vmt_header_for_shift_...;
        qualified_name baseName = utils.makeQualifiedName(**virtualBaseIter);
        tkind virtual_kind = utils.makeTemplateKind(*virtualBaseIter);
        *endInsertionPoint = cons_container(
          statement_Expression(copy_loc(loc), expression_cons(copy_loc(loc),
            exp_node_Assign(
              expression_cons(copy_loc(loc), exp_node_Dereference(
                expression_cons(copy_loc(loc), exp_node_PointerCast(
                  qual_type_cons(NULL, typ_Pointer(pkind_PDataPointer(
                    qual_type_cons(NULL, typ_Pointer(pkind_PDataPointer(
                      qual_type_cons(NULL, typ_Struct(qualified_name_cons(NULL,
                        strdup("_frama_c_vmt")), tkind_TStandard())))))))),
                  reference_or_pointer_kind_RPKPointer(),
                  expression_cons(copy_loc(loc), exp_node_PointerCast(
                    qual_type_cons(
                      NULL,
                      typ_Pointer(
                        pkind_PDataPointer(
                          qual_type_cons(
                            NULL, typ_Struct(baseName, virtual_kind))))),
                      reference_or_pointer_kind_RPKVirtualBasePointer(
                        *iter,
                        qual_type_cons(NULL, typ_Pointer(pkind_PDataPointer(
                          qual_type_cons(NULL,
                          typ_Struct(
                            utils.makeQualifiedName(*currentClass),
                            tkind_dup(virtual_kind)))))),
                        false /* noeffect */),
                    expression_cons(copy_loc(loc), exp_node_Variable(
                          variable_FunctionParameter(strdup("this")))))))))),
            expression_cons(copy_loc(loc), exp_node_Address(
              expression_cons(copy_loc(loc), exp_node_Variable(
                variable_Global(vmtNameShift)))))))), *endInsertionPoint);
        endInsertionPoint = &((*endInsertionPoint)->next);
      };
      ++virtualBaseIter;
    };
  }
}

void
RTTITable::addBarePvmtSetter(const Clang_utils& utils,
    const clang::CXXRecordDecl* source, /* statement */ list& insertionPoint, 
    location loc) {
  const clang::CXXRecordDecl* currentClass = _currentClass.empty() ? NULL
      : _currentClass.front();
  assert(!currentClass || currentClass == source);
  const ClassInfo* currentClassInfo;
  if (currentClass != source) {
    currentClass = source;
    std::map<const clang::CXXRecordDecl*, ClassInfo>::const_iterator
      found = _classInfoTable.find(source);
    assert(found != _classInfoTable.end());
    currentClassInfo = &found->second;
  }
  else
    currentClassInfo = &_currentClassInfo.front();

  //   this->pvmt = &...::_frama_c_vmt_header;
  // translated into
  //   *((_frama_c_vmt**) this) = &...::_frama_c_vmt_header;
  const clang::ClassTemplateSpecializationDecl* currentTSD = llvm::dyn_cast
    <clang::ClassTemplateSpecializationDecl>(currentClass);
  qualified_name vmtName = utils.makeQualifiedName(*currentClass);
  { /* qualification */ list* endQualif = &vmtName->prequalification;
    while (*endQualif)
      endQualif = &(*endQualif)->next;
    if (currentTSD)
      *endQualif = cons_container(qualification_QTemplateInstance(
          const_cast<char*>(vmtName->decl_name), utils
            .getTemplateExtension(currentTSD)), NULL);
    else
      *endQualif = cons_container(qualification_QStructOrClass(
          const_cast<char*>(vmtName->decl_name)), NULL);
  };
  vmtName->decl_name = strdup("_frama_c_vmt");
  const InheritancePath* accessToPvmt = currentClassInfo->hasPvmtAsFirstField()
    ? NULL : &currentClassInfo->getPvmtField();

  expression startPvmt = expression_cons(copy_loc(loc), exp_node_Variable(
     variable_FunctionParameter(strdup("this"))));
  if (accessToPvmt) {
    InheritancePath::const_reverse_iterator
        iterEnd = accessToPvmt->rend(), iter = accessToPvmt->rbegin();
    for (; iter != iterEnd; ++iter) {
      const clang::CXXRecordDecl* baseClass = iter->first;
      tkind baseTemplate;
      if (baseClass->getKind() == clang::Decl::ClassTemplateSpecialization) {
        const clang::ClassTemplateSpecializationDecl* TSD = llvm::dyn_cast
          <clang::ClassTemplateSpecializationDecl>(baseClass);
        baseTemplate = tkind_TTemplateInstance(utils.getTemplateExtension(TSD));
      }
      else
        baseTemplate = tkind_TStandard();
      startPvmt = expression_cons(copy_loc(loc),
        exp_node_PointerCast(qual_type_cons(NULL,
          typ_Pointer(pkind_PDataPointer(qual_type_cons(NULL,
            typ_Struct(utils.makeQualifiedName(*baseClass),
              baseTemplate))))),
          reference_or_pointer_kind_RPKStaticBasePointer(),
          startPvmt));
    };
  };
  startPvmt = expression_cons(copy_loc(loc), exp_node_Dereference(
    expression_cons(copy_loc(loc), exp_node_PointerCast(
      qual_type_cons(NULL, typ_Pointer(pkind_PDataPointer(
        qual_type_cons(NULL, typ_Pointer(pkind_PDataPointer(
          qual_type_cons(NULL, typ_Struct(qualified_name_cons(NULL,
            strdup("_frama_c_vmt")), tkind_TStandard())))))))),
      reference_or_pointer_kind_RPKPointer(), startPvmt))));
  // int frama_c_vmt_index;
  insertionPoint = cons_container(
    statement_VarDecl(copy_loc(loc), strdup("frama_c_vmt_index"),
      qual_type_cons(NULL, typ_Int(IINT)), opt_none()), insertionPoint);
  list* endInsertionPoint = &insertionPoint->next;
  // for (frama_c_vmt_index = 0;
  //     frama_c_vmt_index < currentClass::numberOfMethods();
  //     ++frama_c_vmt_index)
  *endInsertionPoint = cons_container(
    statement_For(copy_loc(loc),
      init_statement_IExpression(expression_cons(copy_loc(loc),
        exp_node_Assign(expression_cons(copy_loc(loc),
          exp_node_Variable(variable_Local(qualified_name_cons(NULL,
            strdup("frama_c_vmt_index"))))), expression_cons(copy_loc(loc),
          exp_node_Constant(compilation_constant_IntCst(
            IINT, ICLITERAL, 0)))))),
      opt_some_container(expression_cons(copy_loc(loc),
        exp_node_Binary_operator(BOLESS, AKRVALUE,
          expression_cons(copy_loc(loc),
            exp_node_Variable(variable_Local(qualified_name_cons(NULL,
              strdup("frama_c_vmt_index"))))),
          makeIntLiteral(copy_loc(loc),IINT,
            (int) currentClassInfo->numberOfMethods())))),
      incr_statement_CExpression(expression_cons(copy_loc(loc),
        exp_node_Unary_operator(uokind_UOPreInc(),
          expression_cons(copy_loc(loc),
            exp_node_Variable(variable_Local(qualified_name_cons(NULL,
              strdup("frama_c_vmt_index")))))))),
      NULL /* body */, NULL), *endInsertionPoint);

  //   if (vmt_name::frama_c_vmt[frama_c_vmt_index]
  //       .method_ptr != (char*) 0) { ... }
  statement& forBody = ((statement) (*endInsertionPoint)->element.container)
      ->cons_statement.For.instruction;
  endInsertionPoint = &((*endInsertionPoint)->next);
  forBody =
    statement_Condition(
      copy_loc(loc),
      cond_statement_CondExpression(
        expression_cons(
          copy_loc(loc),
          exp_node_Binary_operator(
            BODIFFERENT, AKRVALUE,
            expression_cons(
              copy_loc(loc),
              exp_node_PointerCast(
                qual_type_cons(
                  NULL,
                  typ_Pointer(
                    pkind_PDataPointer(
                      qual_type_cons(NULL, typ_Int(ICHAR))))),
                reference_or_pointer_kind_RPKPointer(),
                expression_cons(
                  copy_loc(loc),
                  exp_node_FieldAccess(
                    expression_cons(
                      copy_loc(loc),
                      exp_node_Dereference(
                        expression_cons(
                          copy_loc(loc),
                          exp_node_Binary_operator(
                            BOPLUS, AKRVALUE,
                            expression_cons(
                              copy_loc(loc),
                              exp_node_Variable(
                                variable_Global(qualified_name_dup(vmtName)))),
                            expression_cons(
                              copy_loc(loc),
                              exp_node_Variable(
                                variable_Local(
                                  qualified_name_cons(
                                    NULL, strdup("frama_c_vmt_index"))))))))),
                    strdup("method_ptr"))))),
            makeNullPointer(loc, qual_type_cons(NULL, typ_Int(ICHAR)))))),
      statement_Block(copy_loc(loc), NULL) /* then_instruction */,
      statement_Nop(copy_loc(loc)) /* else_instruction */);
  /* statement */ list& ifBody = forBody->cons_statement.Condition
    .then_instruction->cons_statement.Block.instructions;
  //     startPvmt->table[frama_c_vmt_index].method_ptr
  //       = vmt_name::frama_c_vmt[frama_c_vmt_index].method_ptr;
  //     startPvmt->table[frama_c_vmt_index].shift_this
  //       = vmt_name::frama_c_vmt[frama_c_vmt_index].shift_this;
  ifBody = cons_container(statement_Expression(copy_loc(loc),
    expression_cons(copy_loc(loc), exp_node_Assign(
      expression_cons(copy_loc(loc),
        exp_node_FieldAccess(expression_cons(copy_loc(loc),
          exp_node_Dereference(expression_cons(copy_loc(loc),
            exp_node_Binary_operator(BOPLUS, AKRVALUE,
              expression_cons(copy_loc(loc),
                exp_node_FieldAccess(expression_cons(copy_loc(loc),
                  exp_node_Dereference(startPvmt)), "table")),
              expression_cons(copy_loc(loc),
                exp_node_Variable(variable_Local(qualified_name_cons(NULL,
                  strdup("frama_c_vmt_index"))))))))),
          "shift_this")),
      expression_cons(copy_loc(loc),
        exp_node_FieldAccess(expression_cons(copy_loc(loc),
          exp_node_Dereference(expression_cons(copy_loc(loc),
            exp_node_Binary_operator(BOPLUS, AKRVALUE,
              expression_cons(copy_loc(loc), exp_node_Variable(
                variable_Global(qualified_name_dup(vmtName)))),
              expression_cons(copy_loc(loc),
                exp_node_Variable(variable_Local(qualified_name_cons(NULL,
                  strdup("frama_c_vmt_index"))))))))),
          "shift_this"))))), ifBody);
  ifBody = cons_container(statement_Expression(copy_loc(loc),
    expression_cons(copy_loc(loc), exp_node_Assign(
      expression_cons(copy_loc(loc),
        exp_node_FieldAccess(expression_cons(copy_loc(loc),
          exp_node_Dereference(expression_cons(copy_loc(loc),
            exp_node_Binary_operator(BOPLUS, AKRVALUE,
              expression_cons(copy_loc(loc),
                exp_node_FieldAccess(expression_cons(copy_loc(loc),
                  exp_node_Dereference(expression_dup(startPvmt))), "table")),
              expression_cons(copy_loc(loc),
                exp_node_Variable(variable_Local(qualified_name_cons(NULL,
                  strdup("frama_c_vmt_index"))))))))),
          "method_ptr")),
      expression_cons(copy_loc(loc),
        exp_node_FieldAccess(expression_cons(copy_loc(loc),
          exp_node_Dereference(expression_cons(copy_loc(loc),
            exp_node_Binary_operator(BOPLUS, AKRVALUE,
              expression_cons(copy_loc(loc), exp_node_Variable(
                variable_Global(qualified_name_dup(vmtName)))),
              expression_cons(copy_loc(loc),
                exp_node_Variable(variable_Local(qualified_name_cons(NULL,
                  strdup("frama_c_vmt_index"))))))))),
          "method_ptr"))))), ifBody);
         

  InheritancePosition::const_iterator derivationIterEnd =
    currentClassInfo->_derivationsPosition.end();
  int oldPosition = 0;
  for (InheritancePosition::const_iterator
         derivationIter = currentClassInfo->_derivationsPosition.begin();
       derivationIter != derivationIterEnd; ++derivationIter) {
    if (derivationIter->second > oldPosition) {
      oldPosition = derivationIter->second;
      qualified_name vmtNameShift = qualified_name_dup(vmtName);
      { std::ostringstream tmp;
        tmp << "_frama_c_vmt_header_for_shift_"
            << derivationIter->second;
        free(const_cast<char*>(vmtNameShift->decl_name));
        vmtNameShift->decl_name = strdup(tmp.str().c_str());
      };
      qualified_name vmtNameHeader = qualified_name_dup(vmtName);
      free(const_cast<char*>(vmtNameHeader->decl_name));
      vmtNameHeader->decl_name = strdup("_frama_c_vmt_header");
      // *((_frama_c_vmt **) & this->_frama_c_...)
      //    = *((_frama_c_vmt **) & this)
      //      + (& __::_frama_c_vmt_header_for_shift_...
      //         - & __::_frama_c_vmt_header);
      qualified_name baseName = utils.makeQualifiedName(*derivationIter->first);
      const clang::ClassTemplateSpecializationDecl* TSD
        = llvm::dyn_cast<clang::ClassTemplateSpecializationDecl>(
            derivationIter->first);
      *endInsertionPoint = cons_container(
        statement_Expression(copy_loc(loc), expression_cons(copy_loc(loc),
          exp_node_Assign(
            expression_cons(copy_loc(loc), exp_node_Dereference(
              expression_cons(copy_loc(loc), exp_node_PointerCast(
                qual_type_cons(NULL, typ_Pointer(pkind_PDataPointer(
                  qual_type_cons(NULL, typ_Pointer(pkind_PDataPointer(
                    qual_type_cons(NULL, typ_Struct(qualified_name_cons(NULL,
                      strdup("_frama_c_vmt")), tkind_TStandard())))))))),
                reference_or_pointer_kind_RPKPointer(),
                expression_cons(copy_loc(loc), exp_node_PointerCast(
                  qual_type_cons(NULL, typ_Pointer(pkind_PDataPointer(
                    qual_type_cons(NULL, typ_Struct(baseName, !TSD
                      ? tkind_TStandard()
                      : tkind_TTemplateInstance(
                          utils.getTemplateExtension(TSD))))))),
                  reference_or_pointer_kind_RPKStaticBasePointer(),
                  expression_cons(copy_loc(loc), exp_node_Variable(
                    variable_FunctionParameter(strdup("this")))))))))),
          expression_cons(copy_loc(loc), exp_node_Binary_operator(
            BOPLUS, AKRVALUE,
            expression_dup(startPvmt),
            expression_cons(copy_loc(loc), exp_node_Binary_operator(
              BOMINUS, AKRVALUE,
              expression_cons(copy_loc(loc), exp_node_Address(
                expression_cons(copy_loc(loc), exp_node_Variable(
                  variable_Global(vmtNameShift))))),
              expression_cons(copy_loc(loc), exp_node_Address(
                expression_cons(copy_loc(loc), exp_node_Variable(
                  variable_Global(vmtNameHeader)))))))))))),
        *endInsertionPoint);
      endInsertionPoint = &((*endInsertionPoint)->next);
    };
  };
}

void
RTTITable::addPvmtSetterForBare(const Clang_utils& utils,
    const clang::CXXRecordDecl* source, /* statement */ list& insertionPoint, 
    location loc) {
  const clang::CXXRecordDecl* currentClass = _currentClass.empty() ? NULL
      : _currentClass.front();
  assert(!currentClass || currentClass == source);
  const ClassInfo* currentClassInfo;
  if (currentClass != source) {
    currentClass = source;
    std::map<const clang::CXXRecordDecl*, ClassInfo>::const_iterator
      found = _classInfoTable.find(source);
    assert(found != _classInfoTable.end());
    currentClassInfo = &found->second;
  }
  else
    currentClassInfo = &_currentClassInfo.front();

  //   this->pvmt = &...::_frama_c_vmt_header;
  // translated into
  //   *((_frama_c_vmt**) this) = &...::_frama_c_vmt_header;
  const clang::ClassTemplateSpecializationDecl* currentTSD = llvm::dyn_cast
    <clang::ClassTemplateSpecializationDecl>(currentClass);
  qualified_name vmtName = utils.makeQualifiedName(*currentClass);
  { /* qualification */ list* endQualif = &vmtName->prequalification;
    while (*endQualif)
      endQualif = &(*endQualif)->next;
    if (currentTSD)
      *endQualif = cons_container(qualification_QTemplateInstance(
          const_cast<char*>(vmtName->decl_name), utils
            .getTemplateExtension(currentTSD)), NULL);
    else
      *endQualif = cons_container(qualification_QStructOrClass(
          const_cast<char*>(vmtName->decl_name)), NULL);
    vmtName->decl_name = NULL;
  };
  const InheritancePath* accessToPvmt = currentClassInfo->hasPvmtAsFirstField()
    ? NULL : &currentClassInfo->getPvmtField();

  expression startPvmt = expression_cons(copy_loc(loc), exp_node_Variable(
     variable_FunctionParameter(strdup("this"))));
  if (accessToPvmt) {
    InheritancePath::const_reverse_iterator
        iterEnd = accessToPvmt->rend(), iter = accessToPvmt->rbegin();
    for (; iter != iterEnd; ++iter) {
      const clang::CXXRecordDecl* baseClass = iter->first;
      tkind baseTemplate;
      if (baseClass->getKind() == clang::Decl::ClassTemplateSpecialization) {
        const clang::ClassTemplateSpecializationDecl* TSD = llvm::dyn_cast
          <clang::ClassTemplateSpecializationDecl>(baseClass);
        baseTemplate = tkind_TTemplateInstance(utils.getTemplateExtension(TSD));
      }
      else
        baseTemplate = tkind_TStandard();
      startPvmt = expression_cons(copy_loc(loc),
        exp_node_PointerCast(qual_type_cons(NULL,
          typ_Pointer(pkind_PDataPointer(qual_type_cons(NULL,
            typ_Struct(utils.makeQualifiedName(*baseClass),
              baseTemplate))))),
          reference_or_pointer_kind_RPKStaticBasePointer(),
          startPvmt));
    };
  };
  startPvmt = expression_cons(copy_loc(loc), exp_node_Dereference(
    expression_cons(copy_loc(loc), exp_node_PointerCast(
      qual_type_cons(NULL, typ_Pointer(pkind_PDataPointer(
        qual_type_cons(NULL, typ_Pointer(pkind_PDataPointer(
          qual_type_cons(NULL, typ_Struct(qualified_name_cons(NULL,
            strdup("_frama_c_vmt")), tkind_TStandard())))))))),
      reference_or_pointer_kind_RPKPointer(), startPvmt))));
  // int frama_c_vmt_index;
  insertionPoint = cons_container(
    statement_VarDecl(copy_loc(loc), strdup("frama_c_vmt_index"),
      qual_type_cons(NULL, typ_Int(IINT)), opt_none()), insertionPoint);
  list* endInsertionPoint = &insertionPoint->next;
  // struct _frama_c_vmt_content _frama_c_local_vmt[2];
  *endInsertionPoint = cons_container(
    statement_VarDecl(copy_loc(loc), strdup("_frama_c_local_vmt"),
      qual_type_cons(NULL, typ_Array(akind_cons(qual_type_cons(NULL,
        typ_Struct(qualified_name_cons(NULL, strdup("_frama_c_vmt_content")),
          tkind_TStandard())),
        opt_some_container(makeIntLiteral(copy_loc(loc), IINT,
          (int) currentClassInfo->numberOfMethods()))))),
      opt_none()), *endInsertionPoint);
  endInsertionPoint = &(*endInsertionPoint)->next;

  // struct _frama_c_vmt _frama_c_local_vmt_header = 
  // {.table = _frama_c_local_vmt,
  //  .table_size = currentClassInfo.numberOfMethods(),
  //  .rtti_info = & currentClass::_frama_c_rtti_name_info};
  vmtName->decl_name = strdup("_frama_c_rtti_name_info");
  *endInsertionPoint = cons_container(
    statement_VarDecl(copy_loc(loc), strdup("_frama_c_local_vmt_header"),
      qual_type_cons(NULL,
        typ_Struct(qualified_name_cons(NULL, strdup("_frama_c_vmt")),
          tkind_TStandard())),
      opt_some_container(init_expr_Compound_init(
        cons_container(
          init_expr_Single_init(expression_cons(copy_loc(loc),
            exp_node_Variable(variable_Local(
              qualified_name_cons(NULL, strdup("_frama_c_local_vmt")))))),
        cons_container(
          init_expr_Single_init(makeIntLiteral(copy_loc(loc), IINT,
            (int) currentClassInfo->numberOfMethods())),
        cons_container(
          init_expr_Single_init(expression_cons(copy_loc(loc),
            exp_node_Address(expression_cons(copy_loc(loc),
              exp_node_Variable(variable_Global(vmtName)))))),
          NULL)))))), *endInsertionPoint);
  endInsertionPoint = &(*endInsertionPoint)->next;

  // for (frama_c_vmt_index = 0;
  //     frama_c_vmt_index < sizeof(currentClass::numberOfMethods());
  //     ++frama_c_vmt_index)
  *endInsertionPoint = cons_container(
    statement_For(copy_loc(loc),
      init_statement_IExpression(expression_cons(copy_loc(loc),
        exp_node_Assign(expression_cons(copy_loc(loc),
          exp_node_Variable(variable_Local(qualified_name_cons(NULL,
            strdup("frama_c_vmt_index"))))), expression_cons(copy_loc(loc),
          exp_node_Constant(compilation_constant_IntCst(
            IINT, ICLITERAL, 0)))))),
      opt_some_container(expression_cons(copy_loc(loc),
        exp_node_Binary_operator(BOLESS, AKRVALUE,
          expression_cons(copy_loc(loc),
            exp_node_Variable(variable_Local(qualified_name_cons(NULL,
              strdup("frama_c_vmt_index"))))),
          makeIntLiteral(copy_loc(loc),IINT,
            (int) currentClassInfo->numberOfMethods())))),
      incr_statement_CExpression(expression_cons(copy_loc(loc),
        exp_node_Unary_operator(uokind_UOPreInc(),
          expression_cons(copy_loc(loc),
            exp_node_Variable(variable_Local(qualified_name_cons(NULL,
              strdup("frama_c_vmt_index")))))))),
      NULL /* body */, NULL), *endInsertionPoint);
  statement& forBody = ((statement) (*endInsertionPoint)->element.container)
      ->cons_statement.For.instruction;
  endInsertionPoint = &((*endInsertionPoint)->next);

  //   (_frama_c_local_vmt + frama_c_vmt_index)->method_ptr
  //     = currentClass::_frama_c_vmt[frama_c_vmt_index].method_ptr;
  //   (_frama_c_local_vmt + frama_c_vmt_index)->shift_this
  //     = currentClass::_frama_c_vmt[frama_c_vmt_index].shift_this;
  vmtName = qualified_name_dup(vmtName);
  free(const_cast<char*>(vmtName->decl_name));
  vmtName->decl_name = strdup("_frama_c_vmt");
  forBody = statement_Block(copy_loc(loc), NULL);

  forBody->cons_statement.Block.instructions
    = cons_container(statement_Expression(copy_loc(loc),
      expression_cons(copy_loc(loc), exp_node_Assign(
        expression_cons(copy_loc(loc),
          exp_node_FieldAccess(expression_cons(copy_loc(loc),
            exp_node_Dereference(expression_cons(copy_loc(loc),
              exp_node_Binary_operator(BOPLUS, AKRVALUE,
                expression_cons(copy_loc(loc),
                  exp_node_Variable(variable_Local(qualified_name_cons(NULL,
                    "_frama_c_local_vmt")))),
                expression_cons(copy_loc(loc),
                  exp_node_Variable(variable_Local(qualified_name_cons(NULL,
                    strdup("frama_c_vmt_index"))))))))),
            "shift_this")),
        expression_cons(copy_loc(loc),
          exp_node_FieldAccess(expression_cons(copy_loc(loc),
            exp_node_Dereference(expression_cons(copy_loc(loc),
              exp_node_Binary_operator(BOPLUS, AKRVALUE,
                expression_cons(copy_loc(loc), exp_node_Variable(
                  variable_Global(qualified_name_dup(vmtName)))),
                expression_cons(copy_loc(loc),
                  exp_node_Variable(variable_Local(qualified_name_cons(NULL,
                    strdup("frama_c_vmt_index"))))))))),
            "shift_this"))))), forBody->cons_statement.Block.instructions);
  forBody->cons_statement.Block.instructions
    = cons_container(statement_Expression(copy_loc(loc),
      expression_cons(copy_loc(loc), exp_node_Assign(
        expression_cons(copy_loc(loc),
          exp_node_FieldAccess(expression_cons(copy_loc(loc),
            exp_node_Dereference(expression_cons(copy_loc(loc),
              exp_node_Binary_operator(BOPLUS, AKRVALUE,
                expression_cons(copy_loc(loc),
                  exp_node_Variable(variable_Local(qualified_name_cons(NULL,
                    "_frama_c_local_vmt")))),
                expression_cons(copy_loc(loc),
                  exp_node_Variable(variable_Local(qualified_name_cons(NULL,
                    strdup("frama_c_vmt_index"))))))))),
            "method_ptr")),
        expression_cons(copy_loc(loc),
          exp_node_FieldAccess(expression_cons(copy_loc(loc),
            exp_node_Dereference(expression_cons(copy_loc(loc),
              exp_node_Binary_operator(BOPLUS, AKRVALUE,
                expression_cons(copy_loc(loc), exp_node_Variable(
                  variable_Global(qualified_name_dup(vmtName)))),
                expression_cons(copy_loc(loc),
                  exp_node_Variable(variable_Local(qualified_name_cons(NULL,
                    strdup("frama_c_vmt_index"))))))))),
            "method_ptr"))))), forBody->cons_statement.Block.instructions);
  // *((struct _frama_c_vmt **)this) = &_frama_c_local_vmt_header;
  *endInsertionPoint = cons_container(
    statement_Expression(copy_loc(loc), expression_cons(copy_loc(loc),
      exp_node_Assign(
        startPvmt,
        expression_cons(copy_loc(loc), exp_node_Address(
          expression_cons(copy_loc(loc), exp_node_Variable(variable_Local(
            qualified_name_cons(NULL, "_frama_c_local_vmt_header"))))))))),
    *endInsertionPoint);
  endInsertionPoint = &(*endInsertionPoint)->next;

  InheritancePosition::const_iterator derivationIterEnd =
    currentClassInfo->_derivationsPosition.end();
  int oldPosition = 0;
  for (InheritancePosition::const_iterator
         derivationIter = currentClassInfo->_derivationsPosition.begin();
       derivationIter != derivationIterEnd; ++derivationIter) {
    if (derivationIter->second > oldPosition) {
      oldPosition = derivationIter->second;

      // struct _frama_c_vmt_content* _frama_c_local_vmt_for_shift_index
      //   = &_frama_c_local_vmt[base_index];
      char* localVmtName;
      { std::ostringstream tmp;
        tmp << "_frama_c_local_vmt_for_shift_" << derivationIter->second;
        localVmtName = strdup(tmp.str().c_str());
      };
      *endInsertionPoint = cons_container(statement_VarDecl(copy_loc(loc),
        localVmtName,
        qual_type_cons(NULL, typ_Pointer(pkind_PDataPointer(
          qual_type_cons(NULL, typ_Struct(qualified_name_cons(NULL,
            strdup("_frama_c_vmt_content")), tkind_TStandard()))))),
        opt_some_container(init_expr_Single_init(expression_cons(copy_loc(loc),
          exp_node_Binary_operator(BOPLUS, AKRVALUE,
            expression_cons(copy_loc(loc), exp_node_Variable(variable_Local(
              qualified_name_cons(NULL, strdup("_frama_c_local_vmt"))))),
            makeIntLiteral(copy_loc(loc), IINT, derivationIter->second)))))),
        *endInsertionPoint);
      endInsertionPoint = &(*endInsertionPoint)->next;

      // struct _frama_c_vmt _frama_c_local_vmt_header_for_shift_index =
      // {.table = & _frama_c_local_vmt[base_index],
      //  .table_size = baseClass.numberOfMethods(),
      //  .rtti_info = & currentClass::_frama_c_rtti_name_info};
      { std::ostringstream tmp;
        tmp << "_frama_c_local_vmt_header_for_shift_" << derivationIter->second;
        localVmtName = strdup(tmp.str().c_str());
      };
      vmtName = qualified_name_dup(vmtName);
      free(const_cast<char*>(vmtName->decl_name));
      vmtName->decl_name = strdup("_frama_c_rtti_name_info");
      *endInsertionPoint = cons_container(statement_VarDecl(copy_loc(loc),
        localVmtName,
        qual_type_cons(NULL, typ_Struct(qualified_name_cons(NULL,
          strdup("_frama_c_vmt")), tkind_TStandard())),
        opt_some_container(init_expr_Compound_init(
          cons_container(
            init_expr_Single_init(expression_cons(copy_loc(loc),
              exp_node_Binary_operator(BOPLUS, AKRVALUE,
                expression_cons(copy_loc(loc), exp_node_Variable(
                 variable_Local(qualified_name_cons(NULL,
                   strdup("_frama_c_local_vmt"))))),
                makeIntLiteral(copy_loc(loc), IINT, derivationIter->second)))),
          cons_container(
            init_expr_Single_init(makeIntLiteral(copy_loc(loc), IINT,
              getClassInfo(derivationIter->first)->numberOfMethods())),
          cons_container(
            init_expr_Single_init(expression_cons(copy_loc(loc),
              exp_node_Address(expression_cons(copy_loc(loc),
                exp_node_Variable(variable_Global(vmtName)))))),
            NULL)))))), *endInsertionPoint);
      endInsertionPoint = &(*endInsertionPoint)->next;

      // *((struct _frama_c_vmt **)(& this->baseClassAccess))
      //   = &_frama_c_local_vmt_header_for_shift_index;
      const clang::ClassTemplateSpecializationDecl* TSD
        = llvm::dyn_cast<clang::ClassTemplateSpecializationDecl>(
            derivationIter->first);
      *endInsertionPoint = cons_container(statement_Expression(copy_loc(loc),
        expression_cons(copy_loc(loc), exp_node_Assign(
            getPvmt(utils, derivationIter->first,
              expression_cons(copy_loc(loc), exp_node_PointerCast(
                qual_type_cons(NULL, typ_Pointer(pkind_PDataPointer(
                  qual_type_cons(NULL, typ_Struct(
                    utils.makeQualifiedName(*derivationIter->first),
                    TSD ? tkind_TTemplateInstance(
                            utils.getTemplateExtension(TSD))
                        : tkind_TStandard()))))),
                reference_or_pointer_kind_RPKStaticBasePointer(),
                expression_cons(copy_loc(loc), exp_node_Variable(
                  variable_FunctionParameter(strdup("this"))))))),
          expression_cons(copy_loc(loc), exp_node_Address(
            expression_cons(copy_loc(loc), exp_node_Variable(
              variable_Local(qualified_name_cons(NULL,
                strdup(localVmtName)))))))))), *endInsertionPoint);
      endInsertionPoint = &(*endInsertionPoint)->next;
    };
  };
}

void
RTTITable::insertStaticVMTDeclaration(ForwardReferenceList& classContent,
    location classLoc) {
  // struct _frama_c_vmt_content _frama_c_vmt[];
  int size = _currentClassInfo.front().numberOfMethods();
  // Kernel won't like a 0-sized array;
  if (size == 0) size = 1;
  classContent.getFront() =
    cons_container(
      class_decl_CFieldDecl(
        copy_loc(classLoc),
        strdup("_frama_c_vmt"),
        qual_type_cons(
          cons_plain(STATIC, NULL),
          typ_Array(
            akind_cons(
              qual_type_cons(
                NULL,
                typ_Struct(
                  qualified_name_cons(
                    NULL, strdup("_frama_c_vmt_content")),
                  tkind_TStandard())),
              opt_some_container(makeIntLiteral(classLoc,IINT, size))))),
        opt_none(),
        false),
      classContent.getFront());
}


void
RTTITable::insertStaticBaseClassesDeclaration(
    ForwardReferenceList& classContent, location classLoc) {
  if (!_currentClassInfo.front()._derivationsPosition.empty()
      || !_currentClassInfo.front()._virtualDerivationsPosition.empty()) {
    // struct _frama_c_rtti_name_info_content _frama_c_base_classes[];
    expression size =
      makeIntLiteral(
        classLoc,
        IINT,
        _currentClassInfo.front()._virtualDerivationsPosition.size()
        + _currentClassInfo.front()._derivationsPosition.size());
    classContent.getFront() =
      cons_container(
        class_decl_CFieldDecl(
          copy_loc(classLoc),
          strdup("_frama_c_base_classes"),
          qual_type_cons(
            cons_plain(STATIC, NULL),
            typ_Array(
              akind_cons(
                qual_type_cons(
                  NULL,
                  typ_Struct(
                    qualified_name_cons(
                      NULL, strdup("_frama_c_rtti_name_info_content")),
                    tkind_TStandard())),
                opt_some_container(size)))),
          opt_none(),
          false),
        classContent.getFront());
  };
}

void
RTTITable::insertStaticRTTIDeclaration(ForwardReferenceList& classContent,
    location classLoc) {
    // struct _frama_c_rtti_name_info_node _frama_c_rtti_name_info;
    classContent.getFront() = cons_container(
      class_decl_CFieldDecl(
        copy_loc(classLoc),
        strdup("_frama_c_rtti_name_info"),
        qual_type_cons(
          cons_plain(STATIC, NULL),
          typ_Struct(
            qualified_name_cons(
              NULL,
              strdup("_frama_c_rtti_name_info_node")), tkind_TStandard())),
        opt_none(),
        false),
      classContent.getFront());
}

void
RTTITable::insertStaticVMTHeaderDeclaration(ForwardReferenceList& classContent,
    location classLoc) {
  if (!_currentClassInfo.front()._virtualDerivationsPosition.empty()) {
    VirtualInheritancePosition::const_reverse_iterator iterEnd
      = _currentClassInfo.front()._virtualDerivationsPosition.rend(), iter;
    for (iter =  _currentClassInfo.front()._virtualDerivationsPosition.rbegin();
        iter != iterEnd; ++iter) {
      // struct _frama_c_vmt _frama_c_vmt_header_for_shift_...;
      std::ostringstream vmtName;
      vmtName << "_frama_c_vmt_header_for_shift_" << *iter;
      classContent.getFront() =
        cons_container(
          class_decl_CFieldDecl(
            copy_loc(classLoc),
            copy_string(vmtName.str()),
            qual_type_cons(
              cons_plain(STATIC, NULL),
              typ_Struct(
                qualified_name_cons(NULL, strdup("_frama_c_vmt")),
                tkind_TStandard())),
            opt_none(),
            false),
        classContent.getFront());
    };
  };
  InheritancePath::const_reverse_iterator derivationIterEnd =
    _currentClassInfo.front()._derivationsPosition.rend();
  for (InheritancePath::const_reverse_iterator derivationIter =
         _currentClassInfo.front()._derivationsPosition.rbegin();
       derivationIter != derivationIterEnd;
       ++derivationIter) {
    if (derivationIter->second != 0) {
      // struct _frama_c_vmt _frama_c_vmt_header_for_shift_...;
      std::ostringstream vmtName;
      vmtName << "_frama_c_vmt_header_for_shift_"
              << derivationIter->second;
      classContent.getFront() = cons_container(
        class_decl_CFieldDecl(
          copy_loc(classLoc),
          copy_string(vmtName.str()),
          qual_type_cons(
            cons_plain(STATIC, NULL),
            typ_Struct(
              qualified_name_cons(NULL, strdup("_frama_c_vmt")),
              tkind_TStandard())),
          opt_none(),
          false),
        classContent.getFront());
    };
  };
  // struct _frama_c_vmt _frama_c_vmt_header;
  classContent.getFront() = cons_container(
    class_decl_CFieldDecl(
      copy_loc(classLoc),
      strdup("_frama_c_vmt_header"),
      qual_type_cons(
        cons_plain(STATIC, NULL),
        typ_Struct(
          qualified_name_cons(
            NULL, strdup("_frama_c_vmt")), tkind_TStandard())),
      opt_none(),
      false),
    classContent.getFront());
}

bool
RTTITable::retrieveStaticInheritancePathBetween(
    const clang::CXXRecordDecl* derived, const clang::CXXRecordDecl* base,
    RTTITable::InheritancePath& result, const Clang_utils& utils,
    RTTITable::VirtualInheritancePath* virtualResult) const {
  typedef clang::CXXRecordDecl::base_class_const_iterator base_iterator;
  typedef std::vector<std::pair<std::pair<base_iterator, int>, base_iterator> >
      path_t;
  path_t path;
  std::vector<std::pair<const clang::CXXRecordDecl*, int> > virtualPath;
  bool hasResult = false;
  // depth first visit of the hierarchy, store the current branch into path.
  // as soon as base is found, path is used to create result.
  path.push_back(std::make_pair(
    std::make_pair(derived->bases_begin(), 0), derived->bases_end()));
  while (true) {
    base_iterator* sonIterEnd = &path.back().second,
                 * sonIter = &path.back().first.first;
    bool doesContinue = (*sonIter != *sonIterEnd);
    if (doesContinue) { // descent to first son
      const clang::CXXRecordDecl* baseDecl = (*sonIter)->getType()
          .getTypePtr()->getAsCXXRecordDecl();
      if (!baseDecl) {
        ++(*sonIter);
        doesContinue = (*sonIter != *sonIterEnd);
      }
      else {
        bool isVirtual = (*sonIter)->isVirtual();
        int position =
          getBasePosition(
            path.size() > 1
              ? path[path.size()-2].first.first->getType().getTypePtr()
                  ->getAsCXXRecordDecl()
              : derived, baseDecl, isVirtual);
        if (isVirtual) {
          if (!virtualResult) {
             ++(*sonIter);
             doesContinue = (*sonIter != *sonIterEnd);
          }
          else
            virtualPath.push_back(std::make_pair(baseDecl, position));
        }
        else if (!baseDecl->isPolymorphic())
          position = 0; // instead of -1 or 0
        if (!isVirtual || virtualResult) {
          if (baseDecl == base) {
            if (!hasResult) {
              hasResult = true;
              path_t::const_iterator iterPathEnd = path.end(),
                                     iterPath = path.begin();
              const clang::CXXRecordDecl* virtualBase = virtualPath.empty()
                  ? NULL : virtualPath.back().first;
              bool hasFoundBase = virtualBase == NULL;
              for (; iterPath != iterPathEnd; ++iterPath) {
                const clang::CXXRecordDecl* base = iterPath->first.first
                    ->getType().getTypePtr()->getAsCXXRecordDecl();
                if (hasFoundBase)
                  result.push_back(std::make_pair(base,iterPath->first.second));
                else if (base == virtualBase)
                  hasFoundBase = true;
              };
              assert(hasFoundBase && (!virtualBase || virtualResult));
              if (virtualBase)
                *virtualResult = std::make_pair(virtualBase,
                    virtualPath.back().second);
            }
            else
              assert(false);
            ++(*sonIter);
            if (isVirtual)
              virtualPath.pop_back();
            doesContinue = (*sonIter != *sonIterEnd);
          }
          else
            path.push_back(std::make_pair(
              std::make_pair(baseDecl->bases_begin(), position /* 0 */),
              baseDecl->bases_end()));
        };
      };
    };
    if (!doesContinue) {
      // set to next uncle
      path.pop_back();
      if (hasResult)
        return true;
      if (path.empty())
        return false;
      sonIterEnd = &path.back().second;
      sonIter = &path.back().first.first;
      const clang::CXXRecordDecl* baseDecl =
        (*sonIter)->getType().getTypePtr()->getAsCXXRecordDecl();
      assert(baseDecl);
      if ((*sonIter)->isVirtual()) {
        assert(!virtualPath.empty());
        virtualPath.pop_back();
      };
      ++(*sonIter);
      if (*sonIter != *sonIterEnd) {
        const clang::CXXRecordDecl* baseDecl = (*sonIter)->getType()
            .getTypePtr()->getAsCXXRecordDecl();
        if (!baseDecl)
          ++(*sonIter);
        else {
          bool isVirtual = (*sonIter)->isVirtual();
          int position =
            getBasePosition(
              path.size() > 1
                ? path[path.size()-2].first.first->getType().getTypePtr()
                    ->getAsCXXRecordDecl()
                : derived, baseDecl, isVirtual);
          if (isVirtual) {
            if (!virtualResult)
              ++(*sonIter);
            else
              virtualPath.push_back(std::make_pair(baseDecl, position));
          }
          else if (!baseDecl->isPolymorphic())
            position = 0;
          if (!isVirtual || virtualResult) {
            path.back().first.second = position;
            if (baseDecl == base) {
              if (!hasResult) {
                hasResult = true;
                path_t::const_iterator iterPathEnd = path.end(),
                                       iterPath = path.begin();
                const clang::CXXRecordDecl* virtualBase = virtualPath.empty()
                    ? NULL : virtualPath.back().first;
                bool hasFoundBase = virtualBase == NULL;
                for (; iterPath != iterPathEnd; ++iterPath) {
                  const clang::CXXRecordDecl* base = iterPath->first.first
                      ->getType().getTypePtr()->getAsCXXRecordDecl();
                  if (hasFoundBase)
                    result.push_back(std::make_pair(base,
                          iterPath->first.second));
                  else if (base == virtualBase)
                    hasFoundBase = true;
                };
                assert(!virtualBase || virtualResult);
                if (virtualBase)
                  *virtualResult = std::make_pair(virtualBase,
                      virtualPath.back().second);
              }
              else
                assert(false);
              ++(*sonIter);
              if (isVirtual)
                virtualPath.pop_back();
            };
          }
        };
      };
    };
  };
}

void
RTTITable::retrieveInheritancePathBetween(const clang::CXXRecordDecl* derived,
    const clang::CXXRecordDecl* base, RTTITable::InheritancePath& result,
    RTTITable::VirtualInheritancePath& virtualResult,
    const Clang_utils& utils) const
{ std::map<const clang::CXXRecordDecl*, ClassInfo>::const_iterator
    found = _classInfoTable.find(derived);
  if (found != _classInfoTable.end() && found->second.hasVirtualBaseClasses())
  { std::vector<const clang::CXXRecordDecl*>::const_iterator
      iter = found->second._virtualBaseClassTable.begin(),
      iterEnd = found->second._virtualBaseClassTable.end();
    int index = -1;
    for (; iter != iterEnd; ++iter) {
      ++index;
      if (*iter == base) {
        virtualResult.first = base;
        virtualResult.second = found->second._virtualDerivationsPosition[index];
        return;
      };
      if (retrieveStaticInheritancePathBetween(*iter, base, result, utils)) {
        virtualResult.first = *iter;
        virtualResult.second = found->second._virtualDerivationsPosition[index];
        return;
      };
    }
  }
  
  bool ok = retrieveStaticInheritancePathBetween(derived, base, result, utils,
      &virtualResult);
  assert(ok);
}

qualified_name
RTTITable::insertStaticVMTDefinition(const Clang_utils& utils,
    ForwardReferenceList& globals, location classLoc) {
  // declaration of the static variable before the class
  // struct _frama_c_vmt_content ...::_frama_c_vmt[size] = { ... };
  qualified_name vmtName = specialMemberName(utils, "_frama_c_vmt");
  translation_unit_decl framaCVMTDeclaration;
  globals.insertContainer(
    framaCVMTDeclaration =
    translation_unit_decl_GlobalVarDecl(
      copy_loc(classLoc),
      decl_or_impl_name_Implementation(vmtName),
      qual_type_cons(
        NULL,
        typ_Array(
          akind_cons(
            qual_type_cons(
              NULL,
              typ_Struct(
                qualified_name_cons(
                  NULL, strdup("_frama_c_vmt_content")), tkind_TStandard())),
            opt_some_container(
              makeIntLiteral(
                classLoc,
                IINT,
                (int) _currentClassInfo.front().numberOfMethods()))))),
      opt_some_container(init_expr_Compound_init(NULL)), false,false));
  /* init_expr */ ForwardReferenceList framaCVMTInitializationEnd(
    *(/* init_expr */ list*) &framaCVMTDeclaration
      ->cons_translation_unit_decl.GlobalVarDecl.init->content.container);

  tkind frontTemplate = utils.makeTemplateKind(_currentClass.front());
  ClassInfo::MethodIterator iterEnd = _currentClassInfo.front().endOfMethods();
  // int numberOfMethods = 0;

  for (ClassInfo::MethodIterator iter = _currentClassInfo.front()
      .beginOfMethods(); iter != iterEnd; ++iter) {
    init_expr methodInitialization;
    framaCVMTInitializationEnd.insertContainer(methodInitialization
      = init_expr_Compound_init(NULL));
    /* init_expr */ ForwardReferenceList framaCMethodInitialization(
      *&methodInitialization->cons_init_expr.Compound_init.init_elts);
    if (iter->isMethod()) {
      const clang::CXXMethodDecl* def = iter->getMethod();
      // _frama_c_vmt[numberOfMethods].method_ptr
      //   = (void (*)()) &makeQualifiedName(*iter->getMethod());
      framaCMethodInitialization.insertContainer(init_expr_Single_init(
        expression_cons(copy_loc(classLoc), exp_node_PointerCast(
          qual_type_cons(NULL, typ_Pointer(pkind_PFunctionPointer(
            signature_cons(qual_type_cons(NULL, typ_Void()), NULL,
             true /* variadic */)))),
          reference_or_pointer_kind_RPKPointer(),
          expression_cons(
            copy_loc(classLoc),
            exp_node_Address(
              expression_cons(
                copy_loc(classLoc),
                exp_node_Variable(
                  variable_CodePointer(
                    utils.makeQualifiedName(*def),
                    utils.makeSignature(*def),
                    (def->getKind() == clang::Decl::CXXDestructor)
                    ? funkind_FKDestructor(true)
                    : utils.cv_meth(def),
                    false /* is_extern_c */,
                    tkind_TStandard())))))))));
    }
    else // iter->isVirtualBaseAccess()
      framaCMethodInitialization.insertContainer(
        init_expr_Single_init(
          expression_cons(
            copy_loc(classLoc),
            exp_node_PointerCast(
              qual_type_cons(
                NULL,
                typ_Pointer(
                  pkind_PFunctionPointer(
                    signature_cons(
                      qual_type_cons(NULL, typ_Void()), NULL, false)))),
              reference_or_pointer_kind_RPKPointer(),
              makeIntLiteral(classLoc,IINT,0)))));
    expression shiftToTableTarget = NULL;
    if (!iter->getInheritancePath().empty()
        || iter->hasVirtualInheritancePath()) {
      shiftToTableTarget =
        makeNullPointer(
          classLoc,
          qual_type_cons(
            NULL,
            typ_Struct(
              utils.makeQualifiedName(*_currentClass.front()),
              tkind_dup(frontTemplate))));

      if (iter->hasVirtualInheritancePath()) {
        const VirtualInheritancePath& path = iter->getVirtualInheritancePath();
        const clang::CXXRecordDecl* targetTableClass = path.first;
        tkind targetTemplate = utils.makeTemplateKind(targetTableClass);
        shiftToTableTarget = expression_cons(copy_loc(classLoc),
          exp_node_PointerCast(qual_type_cons(NULL,
            typ_Pointer(pkind_PDataPointer(qual_type_cons(NULL,
              typ_Struct(utils.makeQualifiedName(*targetTableClass),
                targetTemplate))))),
            reference_or_pointer_kind_RPKStaticBasePointer(),
            // reference_or_pointer_kind_RPKStaticVirtualBasePointer(
            //   path.second,
            //   qual_type_cons(NULL, typ_Struct(utils.makeQualifiedName
            //     (*_currentClass.front()), tkind_dup(frontTemplate)),
            //   true /* noeffect */)),
            shiftToTableTarget));
      };
      InheritancePath::const_reverse_iterator
          targetIterEnd = iter->getInheritancePath().rend(),
          targetIter = iter->getInheritancePath().rbegin();
      for (; targetIter != targetIterEnd; ++targetIter) {
        const clang::CXXRecordDecl* targetTableClass = targetIter->first;
        tkind targetTemplate = utils.makeTemplateKind(targetTableClass);
        // qual_type derivedType = NULL;
        shiftToTableTarget = expression_cons(copy_loc(classLoc),
          exp_node_PointerCast(qual_type_cons(NULL,
            typ_Pointer(pkind_PDataPointer(qual_type_cons(NULL,
              typ_Struct(utils.makeQualifiedName(*targetTableClass),
                targetTemplate))))),
            reference_or_pointer_kind_RPKStaticBasePointer(),
            shiftToTableTarget));
      };
    };

    bool isMethod = iter->isMethod();
    // _frama_c_vmt_content[numberOfMethods].shift_this
    //   = (void*) (((_currentClass*) 0)->_frama_c_sub target)
    //     - (void*) (((_currentClass*) 0)->_frama_c_sub iter)
    const clang::CXXRecordDecl* classMethod = isMethod
        ? iter->getMethod()->getParent() : NULL;
    if (isMethod &&
        classMethod->getDefinition() == _currentClass.front()->getDefinition())
    { if (!shiftToTableTarget)
        framaCMethodInitialization.insertContainer(
          init_expr_Single_init(makeIntLiteral(classLoc,IINT,0)));
      else
        framaCMethodInitialization.insertContainer(
          init_expr_Single_init(
            expression_cons(
              copy_loc(classLoc),
              exp_node_Binary_operator(
                BOMINUS, AKRVALUE,
                expression_cons(
                  copy_loc(classLoc),
                  exp_node_PointerCast(
                    qual_type_cons(NULL, utils.charPtrType()),
                    reference_or_pointer_kind_RPKPointer(),
                    shiftToTableTarget)),
                makeNullPointer(classLoc, utils.charQualType())))));
    }
    else {
      exp_node nodeResult;
      if (isMethod) {
        tkind methodClassTemplate = utils.makeTemplateKind(classMethod);
        InheritancePath inheritancePath;
        VirtualInheritancePath virtualInheritancePath(NULL, 0);
        retrieveInheritancePathBetween(_currentClass.front(), classMethod,
            inheritancePath, virtualInheritancePath, utils);
        int sizeInheritancePath = inheritancePath.size()-1;
        assert(sizeInheritancePath >= 0 || virtualInheritancePath.first);
        nodeResult =
          exp_node_PointerCast(
            qual_type_cons(
              NULL,
              typ_Pointer(
                pkind_PDataPointer(
                  qual_type_cons(
                    NULL,
                    typ_Struct(
                      utils.makeQualifiedName(*classMethod),
                      methodClassTemplate))))),
            reference_or_pointer_kind_RPKStaticBasePointer(),
            makeNullPointer(
              classLoc,
              qual_type_cons(
                NULL,
                typ_Struct(
                  utils.makeQualifiedName(*_currentClass.front()),
                  tkind_dup(frontTemplate)))));
        if (virtualInheritancePath.first  && sizeInheritancePath >= 0) {
          const clang::CXXRecordDecl *localBase = virtualInheritancePath.first;
          // const clang::CXXRecordDecl *localDerived = _currentClass.front();
          tkind base_kind = utils.makeTemplateKind(localBase);
          // tkind derived_kind = utils.makeTemplateKind(localDerived);
          qual_type localBaseType = qual_type_cons(NULL,
            typ_Pointer(pkind_PDataPointer(qual_type_cons(NULL,
              typ_Struct(utils.makeQualifiedName(*localBase), base_kind)))));
          // qual_type localDerivedType =
          //   qual_type_cons(
          //     NULL,
          //     typ_Pointer(
          //       pkind_PDataPointer(
          //         qual_type_cons(
          //           NULL,
          //           typ_Struct(
          //          utils.makeQualifiedName(*localDerived), derived_kind)))));
          exp_node tmpResult =
            exp_node_PointerCast(
              localBaseType,
              reference_or_pointer_kind_RPKStaticBasePointer(),
              expression_cons(copy_loc(classLoc), nodeResult));
          qual_type tmp = nodeResult->cons_exp_node.PointerCast.cast_type;
          nodeResult->cons_exp_node.PointerCast.cast_type
            = tmpResult->cons_exp_node.PointerCast.cast_type;
          tmpResult->cons_exp_node.PointerCast.cast_type = tmp;
          nodeResult = tmpResult;
        };
        for (int index = 0; index < sizeInheritancePath; ++index) {
          const clang::CXXRecordDecl
            *localBase = inheritancePath[index].first;
          // const clang::CXXRecordDecl
          //   *localDerived = inheritancePath[index+1].first;
          tkind base_kind = utils.makeTemplateKind(localBase);
          qual_type localBaseType = qual_type_cons(NULL,
            typ_Pointer(pkind_PDataPointer(qual_type_cons(NULL,
              typ_Struct(utils.makeQualifiedName(*localBase), base_kind)))));
          exp_node tmpResult = exp_node_PointerCast(
            localBaseType,
            reference_or_pointer_kind_RPKStaticBasePointer(),
            expression_cons(copy_loc(classLoc), nodeResult));
          qual_type tmp = nodeResult->cons_exp_node.PointerCast.cast_type;
          nodeResult->cons_exp_node.PointerCast.cast_type
            = tmpResult->cons_exp_node.PointerCast.cast_type;
          tmpResult->cons_exp_node.PointerCast.cast_type = tmp;
          nodeResult = tmpResult;
        };
      }
      else {
        nodeResult =
          makeNullPointer(
            classLoc,
            qual_type_cons(
              NULL,
              typ_Struct(
                utils.makeQualifiedName(*_currentClass.front()),
                tkind_dup(frontTemplate))))->econtent;
        if (!iter->getParentInheritancePath().empty()) {
          InheritancePath::const_reverse_iterator
            pathIterEnd = iter->getParentInheritancePath().rend(),
            pathIter = iter->getParentInheritancePath().rbegin();
          for (; pathIter != pathIterEnd; ++pathIter) {
            const clang::CXXRecordDecl
              *localBase = pathIter->first;
            const clang::ClassTemplateSpecializationDecl* TSD = llvm::
                dyn_cast<clang::ClassTemplateSpecializationDecl>(localBase);
            qual_type localBaseType = qual_type_cons(NULL,
              typ_Pointer(pkind_PDataPointer(qual_type_cons(NULL,
                typ_Struct(utils.makeQualifiedName(*localBase),
                  !TSD ? tkind_TStandard() : tkind_TTemplateInstance(utils
                    .getTemplateExtension(TSD)))))));
            nodeResult = exp_node_PointerCast(
              localBaseType,
              reference_or_pointer_kind_RPKStaticBasePointer(),
              expression_cons(copy_loc(classLoc), nodeResult));
          };
        };
      };

      if (!shiftToTableTarget)
        framaCMethodInitialization.insertContainer(
          init_expr_Single_init(
            expression_cons(
              copy_loc(classLoc),
              exp_node_Binary_operator(
                BOMINUS, AKRVALUE,
                makeNullPointer(classLoc,utils.charQualType()),
                expression_cons(
                  copy_loc(classLoc),
                  exp_node_PointerCast(
                    qual_type_cons(NULL, utils.charPtrType()),
                    reference_or_pointer_kind_RPKPointer(),
                    expression_cons(copy_loc(classLoc), nodeResult)))))));
      else // targetTableClass && external def
        framaCMethodInitialization.insertContainer(init_expr_Single_init(
          expression_cons(copy_loc(classLoc),
            exp_node_Binary_operator(BOMINUS, AKRVALUE,
              expression_cons(copy_loc(classLoc), exp_node_PointerCast(
                qual_type_cons(NULL, utils.charPtrType()),
                reference_or_pointer_kind_RPKPointer(), shiftToTableTarget)),
              expression_cons(copy_loc(classLoc), exp_node_PointerCast(
                qual_type_cons(NULL, utils.charPtrType()),
                reference_or_pointer_kind_RPKPointer(),
                expression_cons(copy_loc(classLoc), nodeResult)))))));
    };
    // ++numberOfMethods;
  };
  free_tkind(frontTemplate);
  return vmtName;
}

void
RTTITable::addBareToQualification(qualified_name& name) const {
  /* qualification */ list endQualif = name->prequalification;
  assert(endQualif);
  while (endQualif->next)
    endQualif = endQualif->next;
  const char** className = NULL;
  if (_currentClass.front()->getKind()
        != clang::Decl::ClassTemplateSpecialization) {
    assert(((qualification) endQualif->element.container)->tag_qualification
        == QSTRUCTORCLASS);
    className = &((qualification) endQualif->element.container)
      ->cons_qualification.QStructOrClass.name;
  }
  else {
    assert(((qualification) endQualif->element.container)->tag_qualification
        == QTEMPLATEINSTANCE);
    className = &((qualification) endQualif->element.container)
      ->cons_qualification.QTemplateInstance.name;
  };
  const char* suffix = "_frama_c_bare";
  int classNameLength = strlen(*className), suffixLength = strlen(suffix);
  char* newName = (char*) malloc(classNameLength+suffixLength+1);
  memcpy(newName, *className, classNameLength);
  memcpy(newName + classNameLength, suffix, suffixLength+1);
  free(const_cast<char*>(*className));
  *className = newName;
}

qualified_name
RTTITable::insertStaticBaseClassesDefinition(const Clang_utils& utils,
      ForwardReferenceList& globals, location classLoc) {
  if (_currentClassInfo.front()._derivationsPosition.empty()
      && _currentClassInfo.front()._virtualDerivationsPosition.empty())
    return NULL;
  // struct _frama_c_rtti_name_info_content _frama_c_base_classes[] = { ... };
  qualified_name nameBaseClasses =
    specialMemberName(utils,"_frama_c_base_classes");
  expression size =
    makeIntLiteral(
      classLoc,
      IINT,
      _currentClassInfo.front()._virtualDerivationsPosition.size()
      + _currentClassInfo.front()._derivationsPosition.size());
  translation_unit_decl framaCBaseClassesDeclaration =
    translation_unit_decl_GlobalVarDecl(
      copy_loc(classLoc), decl_or_impl_name_Implementation(nameBaseClasses),
      qual_type_cons(
        NULL,
        typ_Array(
          akind_cons(
            qual_type_cons(
              NULL,
              typ_Struct(
                qualified_name_cons(
                  NULL, strdup("_frama_c_rtti_name_info_content")),
                tkind_TStandard())),
            opt_some_container(size)))),
      opt_some_container(init_expr_Compound_init(NULL)), false, false);
  globals.insertContainer(framaCBaseClassesDeclaration);
  /* init_expr */ ForwardReferenceList framaCBaseClassesDeclarationEnd(
    *(/* init_expr */ list*) &framaCBaseClassesDeclaration
      ->cons_translation_unit_decl.GlobalVarDecl.init->content.container);
  tkind frontTemplate = utils.makeTemplateKind(_currentClass.front());
  InheritancePosition::const_iterator
    derivationIterEnd = _currentClassInfo.front()._derivationsPosition.end();
  for (InheritancePosition::const_iterator derivationIter =
         _currentClassInfo.front()._derivationsPosition.begin();
       derivationIter != derivationIterEnd; ++derivationIter) {
    // struct _frama_c_rtti_name_info_content {
    //   struct _frama_c_rtti_name_info_node* value;
    //   int shift_object; 
    //   int shift_vmt; 
    // };
    qualified_name nameBaseValue = utils.makeQualifiedName(
      *derivationIter->first);
    tkind templateParameters = utils.makeTemplateKind(derivationIter->first);
    /* qualification */ list* endQualif = &nameBaseValue->prequalification;
    while (*endQualif) endQualif = &(*endQualif)->next;
    if (templateParameters->tag_tkind == TSTANDARD)
      *endQualif =
        cons_container(
          qualification_QStructOrClass(
            const_cast<char*>(nameBaseValue->decl_name)), NULL);
    else {
      tkind temp = tkind_dup(templateParameters);
      assert(temp->tag_tkind == TTEMPLATEINSTANCE);
      *endQualif =
        cons_container(
          qualification_QTemplateInstance(
            const_cast<char*>(nameBaseValue->decl_name),
            temp->cons_tkind.TTemplateInstance.parameters), NULL);
      free(temp);
    };
    nameBaseValue->decl_name = strdup("_frama_c_rtti_name_info");
    init_expr baseClassInitialization;
    framaCBaseClassesDeclarationEnd.insertContainer(baseClassInitialization
      = init_expr_Compound_init(NULL));
    /* init_expr */ ForwardReferenceList framaCBaseClassInitialization(
      baseClassInitialization->cons_init_expr.Compound_init.init_elts);
    // _frama_c_base_classes[derivationIter].value = 
    //   &derivationIter->first::_frama_c_rtti_name_info
    framaCBaseClassInitialization.insertContainer(init_expr_Single_init(
      expression_cons(copy_loc(classLoc), exp_node_Address(
        expression_cons(copy_loc(classLoc), exp_node_Variable(variable_Global(
          nameBaseValue)))))));
    // _frama_c_base_classes[derivationIter].shift_object = 
    //   (void*) 0 - (void*) ((derivationIter->first*) (_currentClass*) 0)
    framaCBaseClassInitialization.insertContainer(
      init_expr_Single_init(
        expression_cons(
          copy_loc(classLoc),
          exp_node_Binary_operator(
            BOMINUS, AKRVALUE,
            makeNullPointer(classLoc, utils.charQualType()),
            expression_cons(
              copy_loc(classLoc),
              exp_node_PointerCast(
                qual_type_cons(NULL, utils.charPtrType()),
                reference_or_pointer_kind_RPKPointer(),
                expression_cons(
                  copy_loc(classLoc),
                  exp_node_PointerCast(
                    qual_type_cons(
                      NULL,
                      typ_Pointer(
                        pkind_PDataPointer(
                          qual_type_cons(
                            NULL,
                            typ_Struct(
                              utils.makeQualifiedName(*derivationIter->first),
                              templateParameters))))),
                    reference_or_pointer_kind_RPKStaticBasePointer(),
                    makeNullPointer(
                      classLoc,
                      qual_type_cons(
                        NULL,
                        typ_Struct(
                          utils.makeQualifiedName(*_currentClass.front()),
                          tkind_dup(frontTemplate))))))))))));
    framaCBaseClassInitialization.insertContainer(
      init_expr_Single_init(
        makeIntLiteral(classLoc,IINT,derivationIter->second)));
  };
  if (!_currentClassInfo.front()._virtualDerivationsPosition.empty()) {
    translation_unit_decl framaCBareBaseClassesDeclaration
      = translation_unit_decl_dup(framaCBaseClassesDeclaration);
    addBareToQualification(framaCBareBaseClassesDeclaration
        ->cons_translation_unit_decl.GlobalVarDecl.name
          ->cons_decl_or_impl_name.Implementation.name);
    globals.insertContainer(framaCBareBaseClassesDeclaration);

    VirtualInheritancePosition::const_iterator
      virtualDerivationIterEnd
        = _currentClassInfo.front()._virtualDerivationsPosition.end(),
      virtualDerivationIter
        = _currentClassInfo.front()._virtualDerivationsPosition.begin();
    int virtualIndex = 0;
    for (; virtualDerivationIter != virtualDerivationIterEnd;
        ++virtualDerivationIter) {
      // struct _frama_c_rtti_name_info_content {
      //   struct _frama_c_rtti_name_info_node* value;
      //   int shift_object; 
      //   int shift_vmt; 
      // };
      const clang::CXXRecordDecl* baseClass = _currentClassInfo.front()
        ._virtualBaseClassTable[virtualIndex];

      qualified_name nameBaseValue = utils.makeQualifiedName(*baseClass);
      tkind templateParameters = utils.makeTemplateKind(baseClass);
      /* qualification */ list* endQualif = &nameBaseValue->prequalification;
      while (*endQualif)
        endQualif = &(*endQualif)->next;
      if (templateParameters->tag_tkind == TSTANDARD)
        *endQualif =
          cons_container(
            qualification_QStructOrClass(
              const_cast<char*>(nameBaseValue->decl_name)), NULL);
      else {
        tkind temp = tkind_dup(templateParameters);
        assert(temp->tag_tkind == TTEMPLATEINSTANCE);
        *endQualif =
          cons_container(
            qualification_QTemplateInstance(
              const_cast<char*>(nameBaseValue->decl_name),
              temp->cons_tkind.TTemplateInstance.parameters),NULL);
        free(temp);
      };
      nameBaseValue->decl_name = strdup("_frama_c_rtti_name_info");
      init_expr baseClassInitialization;
      framaCBaseClassesDeclarationEnd.insertContainer(baseClassInitialization
        = init_expr_Compound_init(NULL));
      /* init_expr */ ForwardReferenceList framaCBaseClassInitialization(
        baseClassInitialization->cons_init_expr.Compound_init.init_elts);
      // _frama_c_base_classes[*virtualDerivationIter].value = 
      //   &derivationIter->first::_frama_c_rtti_name_info
      framaCBaseClassInitialization.insertContainer(init_expr_Single_init(
        expression_cons(copy_loc(classLoc), exp_node_Address(
          expression_cons(copy_loc(classLoc), exp_node_Variable(variable_Global(
            nameBaseValue)))))));
      // _frama_c_base_classes[*virtualDerivationIter].shift_object = 
      //   (void*) 0 - (void*) ((_virtualBaseClassTable[virtualIndex]*)
      //     (_currentClass*) 0)
      framaCBaseClassInitialization.insertContainer(
        init_expr_Single_init(
          expression_cons(
            copy_loc(classLoc),
            exp_node_Binary_operator(
              BOMINUS, AKRVALUE,
              makeNullPointer(classLoc,utils.charQualType()),
              expression_cons(
                copy_loc(classLoc),
                exp_node_PointerCast(
                  qual_type_cons(NULL, utils.charPtrType()),
                  reference_or_pointer_kind_RPKPointer(),
                  expression_cons(
                    copy_loc(classLoc),
                    exp_node_PointerCast(
                      qual_type_cons(
                        NULL,
                        typ_Pointer(
                          pkind_PDataPointer(
                            qual_type_cons(
                              NULL,
                              typ_Struct(
                                utils.makeQualifiedName(
                                  * _currentClassInfo.front()
                                  ._virtualBaseClassTable[virtualIndex]),
                                templateParameters))))),
                      reference_or_pointer_kind_RPKStaticBasePointer(),
                      makeNullPointer(
                        classLoc,
                        qual_type_cons(
                          NULL,
                          typ_Struct(
                            utils.makeQualifiedName(*_currentClass.front()),
                            tkind_dup(frontTemplate))))))))))));
      // _frama_c_base_classes[derivationIter].shift_vmt=*virtualDerivationIter;
      framaCBaseClassInitialization.insertContainer(
        init_expr_Single_init(
          makeIntLiteral(classLoc,IINT,*virtualDerivationIter)));
      ++virtualIndex;
    };
  };

  free_tkind(frontTemplate);
  return nameBaseClasses;
}

void
RTTITable::insertDeclStaticVMTHeaderDefinition(ForwardReferenceList& globals,
    location classLoc, qualified_name vmtName) {
  // struct _frama_c_vmt ...::_frama_c_vmt_header;
  qualified_name vmtHeaderName = qualified_name_dup(vmtName);
  free(const_cast<char*>(vmtHeaderName->decl_name));
  vmtHeaderName->decl_name = strdup("_frama_c_vmt_header");
  globals.insertContainer(
    translation_unit_decl_GlobalVarDecl(
      copy_loc(classLoc), decl_or_impl_name_Implementation(vmtHeaderName),
      qual_type_cons(
        NULL,
        typ_Struct(
          qualified_name_cons(NULL, strdup("_frama_c_vmt")),
          tkind_TStandard())),
      opt_none(), false, false));

  if (!_currentClassInfo.front()._virtualDerivationsPosition.empty()) {
    vmtHeaderName = qualified_name_dup(vmtName);
    free(const_cast<char*>(vmtHeaderName->decl_name));
    vmtHeaderName->decl_name = strdup("_frama_c_vmt_header");
    addBareToQualification(vmtHeaderName);
    globals.insertContainer(
      translation_unit_decl_GlobalVarDecl(
        copy_loc(classLoc), decl_or_impl_name_Implementation(vmtHeaderName),
        qual_type_cons(
          NULL,
          typ_Struct(
            qualified_name_cons(NULL, strdup("_frama_c_vmt")),
            tkind_TStandard())),
        opt_none(), false, false));
  };
}

void RTTITable::insertStaticEmptyRTTIDefinition(
  const Clang_utils& utils, ForwardReferenceList& globals, location classLoc) {
  qualified_name nameRtti = specialMemberName(utils, "_frama_c_rtti_name_info");
  const char* class_name =
    strdup(_currentClass.front()->getName().str().c_str());
  qual_type rttiInfo =
    qual_type_cons(
      NULL,
      typ_Struct(
        qualified_name_cons(NULL, strdup("_frama_c_rtti_name_info_node")),
        tkind_TStandard()));
  /* list is built in reverse order. */
  /* first field is pvmt */
  /* init_expr */ list rttiInit =
    cons_container(
      init_expr_Single_init(
        makeNullPointer(
          classLoc,
          makeStructType(qualified_name_cons(NULL,strdup("_frama_c_vmt"))))),
      NULL);
  /* number_of_base_classes */
  rttiInit =
    cons_container(
      init_expr_Single_init(makeIntLiteral(classLoc,IINT,0)),rttiInit);
  /* base_classes */
  rttiInit =
    cons_container(
      init_expr_Single_init(
        makeNullPointer(
          classLoc,
          makeStructType(
            qualified_name_cons(
              NULL,strdup("_frama_c_rtti_name_info_content"))))),
      rttiInit);
  /* name */
  rttiInit =
    cons_container(
      init_expr_Single_init(makeStringLiteral(classLoc, class_name)),rttiInit);
  
  translation_unit_decl rttiDef =
    translation_unit_decl_GlobalVarDecl(
      copy_loc(classLoc),
      decl_or_impl_name_Implementation(nameRtti),
      rttiInfo,
      opt_some_container(init_expr_Compound_init(rttiInit)),
      false, false);

  globals.insertContainer(rttiDef);
      
}

qualified_name
RTTITable::insertStaticRTTIDefinition(const Clang_utils& utils,
    ForwardReferenceList& globals, location classLoc,
    qualified_name vmtName, qualified_name nameBaseClasses) {
  // struct _frama_c_rtti_name_info_node _frama_c_rtti_name_info = { ... }
  qualified_name nameRtti = specialMemberName(utils,"_frama_c_rtti_name_info");
  const char* class_name =
    strdup(_currentClass.front()->getName().str().c_str());
  translation_unit_decl nameRttiInitialization =
    translation_unit_decl_GlobalVarDecl(
      copy_loc(classLoc),
      decl_or_impl_name_Implementation(nameRtti),
      qual_type_cons(
        NULL,
        typ_Struct(
          qualified_name_cons(NULL, strdup("_frama_c_rtti_name_info_node")),
          tkind_TStandard())),
      opt_some_container(init_expr_Compound_init(NULL)),
      false,
      false);
  globals.insertContainer(nameRttiInitialization);
  ForwardReferenceList framaCNameRttiInitialization(
    *(/* init_expr */ list*) &nameRttiInitialization
      ->cons_translation_unit_decl.GlobalVarDecl.init->content.container);
  // struct _frama_c_rtti_name_info_node {
  //   const char* name;
  //   struct _frama_c_rtti_name_info_content* base_classes;
  //   int number_of_base_classes;
  //   struct _frama_c_vmt* pvmt;
  // };

  // _frama_c_rtti_name_info.name = "nameRtti->decl_name";
  framaCNameRttiInitialization.insertContainer(
    init_expr_Single_init(makeStringLiteral(classLoc,class_name)));
  // _frama_c_rtti_name_info.base_classes
  //   = (struct _frama_c_rtti_name_info_content*) _frama_c_base_classes;
  if (!nameBaseClasses)
    framaCNameRttiInitialization.insertContainer(
      init_expr_Single_init(
        makeNullPointer(
          classLoc,
          makeStructType(
            qualified_name_cons(
              NULL, strdup("_frama_c_rtti_name_info_content"))))));
  else
    framaCNameRttiInitialization.insertContainer(init_expr_Single_init(
      expression_cons(copy_loc(classLoc), exp_node_PointerCast(
        qual_type_cons(NULL, typ_Pointer(pkind_PDataPointer(
          qual_type_cons(NULL, typ_Struct(qualified_name_cons(NULL,
            strdup("_frama_c_rtti_name_info_content")), tkind_TStandard()))))),
        reference_or_pointer_kind_RPKPointer(),
        expression_cons(copy_loc(classLoc), exp_node_Variable(
          variable_Global(qualified_name_dup(nameBaseClasses))))))));

  // _frama_c_rtti_name_info.number_of_base_classes
  //     = _currentClassInfo._derivationsPosition.size();
  //     + _currentClassInfo._virtualDerivationsPosition.size();
  framaCNameRttiInitialization.insertContainer(
    init_expr_Single_init(
      makeIntLiteral(
        classLoc,
        IINT,
        _currentClassInfo.front()._derivationsPosition.size()
        + _currentClassInfo.front()._virtualDerivationsPosition.size())));
  // _frama_c_rtti_name_info.pvmt = vmtHeaderName;
  qualified_name vmtHeaderName = qualified_name_dup(vmtName);
  free(const_cast<char*>(vmtHeaderName->decl_name));
  vmtHeaderName->decl_name = strdup("_frama_c_vmt_header");
  framaCNameRttiInitialization.insertContainer(init_expr_Single_init(
    expression_cons(copy_loc(classLoc), exp_node_Address(
      expression_cons(copy_loc(classLoc), exp_node_Variable(
        variable_Global(vmtHeaderName)))))));

  if (!_currentClassInfo.front()._virtualDerivationsPosition.empty()) {
    qualified_name bareNameRtti = qualified_name_dup(nameRtti);
    addBareToQualification(bareNameRtti);
    assert(nameBaseClasses);
    qualified_name bareNameBaseClasses = qualified_name_dup(nameBaseClasses);
    addBareToQualification(bareNameBaseClasses);
    nameRttiInitialization =
      translation_unit_decl_GlobalVarDecl(
        copy_loc(classLoc),
        decl_or_impl_name_Implementation(bareNameRtti),
        qual_type_cons(
          NULL,
          typ_Struct(
            qualified_name_cons(NULL, strdup("_frama_c_rtti_name_info_node")),
            tkind_TStandard())),
        opt_some_container(init_expr_Compound_init(NULL)),
        false,
        false);
    globals.insertContainer(nameRttiInitialization);
    ForwardReferenceList framaCNameRttiInitialization(
      *(/* init_expr */ list*) &nameRttiInitialization
        ->cons_translation_unit_decl.GlobalVarDecl.init->content.container);
    
    // _frama_c_rtti_name_info.name = "bareNameRtti->decl_name";
    framaCNameRttiInitialization.insertContainer(init_expr_Single_init(
      expression_cons(copy_loc(classLoc), exp_node_String(
        copy_string(std::string(class_name) + "_frama_c_bare")))));
    // _frama_c_rtti_name_info.base_classes
    //   = (struct _frama_c_rtti_name_info_content*) _frama_c_base_classes;
    framaCNameRttiInitialization.insertContainer(init_expr_Single_init(
      expression_cons(copy_loc(classLoc), exp_node_PointerCast(
        qual_type_cons(NULL, typ_Pointer(pkind_PDataPointer(
          qual_type_cons(NULL, typ_Struct(qualified_name_cons(NULL,
            strdup("_frama_c_rtti_name_info_content")), tkind_TStandard()))))),
        reference_or_pointer_kind_RPKPointer(),
        expression_cons(copy_loc(classLoc), exp_node_Variable(
          variable_Global(bareNameBaseClasses)))))));

    // _frama_c_rtti_name_info.number_of_base_classes
    //     = _currentClassInfo._derivationsPosition.size();
    framaCNameRttiInitialization.insertContainer(
      init_expr_Single_init(
        makeIntLiteral(
          classLoc,
          IINT,
          _currentClassInfo.front()._derivationsPosition.size())));
    // _frama_c_rtti_name_info.pvmt = vmtHeaderName;
    vmtHeaderName = qualified_name_dup(vmtName);
    free(const_cast<char*>(vmtHeaderName->decl_name));
    vmtHeaderName->decl_name = strdup("_frama_c_vmt_header");
    addBareToQualification(vmtHeaderName);
    framaCNameRttiInitialization.insertContainer(init_expr_Single_init(
      expression_cons(copy_loc(classLoc), exp_node_Address(
        expression_cons(copy_loc(classLoc), exp_node_Variable(
          variable_Global(vmtHeaderName)))))));
  };
  return nameRtti;
}

void
RTTITable::insertStaticVMTHeaderDefinition(const Clang_utils& utils,
    ForwardReferenceList& globals, location classLoc, qualified_name vmtName,
    qualified_name nameRtti) {
  // struct _frama_c_vmt ...::_frama_c_vmt_header = {
  //    (struct _frama_c_vmt_content*) _frama_c_vmt,
  //    _currentClassInfo.numberOfMethods(),
  //    &_frama_c_rtti_name_info
  // };
  qualified_name vmtHeaderName = qualified_name_dup(vmtName);
  free(const_cast<char*>(vmtHeaderName->decl_name));
  vmtHeaderName->decl_name = strdup("_frama_c_vmt_header");
  globals.insertContainer(
    translation_unit_decl_GlobalVarDecl(
      copy_loc(classLoc),
      decl_or_impl_name_Implementation(vmtHeaderName),
      qual_type_cons(
        NULL,
        typ_Struct(
          qualified_name_cons(NULL, strdup("_frama_c_vmt")),
          tkind_TStandard())),
      opt_some_container(
        init_expr_Compound_init(
          cons_container(
            init_expr_Single_init(
              expression_cons(
                copy_loc(classLoc),
                exp_node_PointerCast(
                  qual_type_cons(
                    NULL,
                    typ_Pointer(
                      pkind_PDataPointer(
                        qual_type_cons(
                          NULL,
                          typ_Struct(
                            qualified_name_cons(
                              NULL, strdup("_frama_c_vmt_content")),
                            tkind_TStandard()))))),
                  reference_or_pointer_kind_RPKPointer(),
                  expression_cons(
                    copy_loc(classLoc),
                    exp_node_Variable(
                      variable_Global(qualified_name_dup(vmtName))))))),
            cons_container(
              init_expr_Single_init(
                makeIntLiteral(
                  classLoc,
                  IINT,
                  _currentClassInfo.front().numberOfMethods())),
              cons_container(
                init_expr_Single_init(
                  expression_cons(
                    copy_loc(classLoc),
                    exp_node_Address(
                      expression_cons(
                        copy_loc(classLoc),
                        exp_node_Variable(
                          variable_Global(qualified_name_dup(nameRtti))))))),
                NULL))))),
      false,
      false));
  InheritancePath::const_iterator derivationIterEnd =
    _currentClassInfo.front()._derivationsPosition.end(), derivationIter;
  int shift = 0;
  for (derivationIter = _currentClassInfo.front()._derivationsPosition.begin();
       derivationIter != derivationIterEnd; ++derivationIter) {
    int previousShift = shift;
    shift = derivationIter->second;
    if (shift>previousShift) {
      qualified_name vmtHeaderShiftName = qualified_name_dup(vmtName);
      { std::ostringstream tmp;
        tmp << "_frama_c_vmt_header_for_shift_" << shift;
        free(const_cast<char*>(vmtHeaderShiftName->decl_name));
        vmtHeaderShiftName->decl_name = copy_string(tmp.str());
      };
      globals.insertContainer(
        translation_unit_decl_GlobalVarDecl(
          copy_loc(classLoc),
          decl_or_impl_name_Implementation(vmtHeaderShiftName),
          qual_type_cons(
            NULL,
            typ_Struct(
              qualified_name_cons(NULL, strdup("_frama_c_vmt")),
              tkind_TStandard())),
          opt_some_container(
            init_expr_Compound_init(
              cons_container(
                init_expr_Single_init(
                  expression_cons(
                    copy_loc(classLoc),
                    exp_node_Binary_operator(
                      BOPLUS, AKRVALUE,
                      expression_cons(
                        copy_loc(classLoc),
                        exp_node_PointerCast(
                          qual_type_cons(
                            NULL,
                            typ_Pointer(
                              pkind_PDataPointer(
                                qual_type_cons(
                                  NULL,
                                  typ_Struct(
                                    qualified_name_cons(
                                      NULL, strdup("_frama_c_vmt_content")),
                                    tkind_TStandard()))))),
                          reference_or_pointer_kind_RPKPointer(),
                          expression_cons(
                            copy_loc(classLoc),
                            exp_node_Variable(
                              variable_Global(qualified_name_dup(vmtName)))))),
                      makeIntLiteral(classLoc,IINT,shift)))),
                cons_container(
                  init_expr_Single_init(
                    makeIntLiteral(
                      classLoc,
                      IINT,
                      _currentClassInfo.front().numberOfMethods()-shift)),
                  cons_container(
                    init_expr_Single_init(
                      expression_cons(
                        copy_loc(classLoc),
                        exp_node_Address(
                          expression_cons(
                            copy_loc(classLoc),
                            exp_node_Variable(
                              variable_Global(
                                qualified_name_dup(nameRtti))))))),
                    NULL))))),
          false, false));
    };
  };
  if (!_currentClassInfo.front()._virtualDerivationsPosition.empty()) {
    shift = 0;
    VirtualInheritancePosition::const_iterator iterEnd =
      _currentClassInfo.front()._virtualDerivationsPosition.end(), iter;
    for (iter = _currentClassInfo.front()._virtualDerivationsPosition.begin();
         iter != iterEnd; ++iter) {
      int previousShift = shift;
      shift = *iter;
      if (shift>previousShift) {
        qualified_name vmtHeaderShiftName = qualified_name_dup(vmtName);
        { std::ostringstream tmp;
          tmp << "_frama_c_vmt_header_for_shift_" << shift;
          free(const_cast<char*>(vmtHeaderShiftName->decl_name));
          vmtHeaderShiftName->decl_name = copy_string(tmp.str());
        };
        globals.insertContainer(
          translation_unit_decl_GlobalVarDecl(
            copy_loc(classLoc),
            decl_or_impl_name_Implementation(vmtHeaderShiftName),
            qual_type_cons(
              NULL,
              typ_Struct(
                qualified_name_cons(NULL, strdup("_frama_c_vmt")),
                tkind_TStandard())),
            opt_some_container(init_expr_Compound_init(
              cons_container(
                init_expr_Single_init(
                  expression_cons(
                    copy_loc(classLoc),
                    exp_node_Binary_operator(
                      BOPLUS, AKRVALUE,
                      expression_cons(
                        copy_loc(classLoc),
                        exp_node_PointerCast(
                          qual_type_cons(
                            NULL,
                            typ_Pointer(
                              pkind_PDataPointer(
                                qual_type_cons(
                                  NULL,
                                  typ_Struct(
                                    qualified_name_cons(
                                      NULL, strdup("_frama_c_vmt_content")),
                                    tkind_TStandard()))))),
                          reference_or_pointer_kind_RPKPointer(),
                          expression_cons(
                            copy_loc(classLoc),
                            exp_node_Variable(
                              variable_Global(qualified_name_dup(vmtName)))))),
                      makeIntLiteral(classLoc,IINT,shift)))),
                cons_container(
                  init_expr_Single_init(
                    makeIntLiteral(
                      classLoc,
                      IINT,
                      _currentClassInfo.front().numberOfMethods()-shift)),
                  cons_container(
                    init_expr_Single_init(
                      expression_cons(
                        copy_loc(classLoc),
                        exp_node_Address(
                          expression_cons(
                            copy_loc(classLoc),
                            exp_node_Variable(
                              variable_Global(
                                qualified_name_dup(nameRtti))))))),
                    NULL))))),
            false, false));
      };
    };

    qualified_name bareVmtHeaderName = qualified_name_dup(vmtHeaderName);
    addBareToQualification(bareVmtHeaderName);
    qualified_name bareNameRtti = qualified_name_dup(nameRtti);
    addBareToQualification(bareNameRtti);
    globals.insertContainer(
      translation_unit_decl_GlobalVarDecl(
        copy_loc(classLoc),
        decl_or_impl_name_Implementation(bareVmtHeaderName),
        qual_type_cons(
          NULL,
          typ_Struct(
            qualified_name_cons(NULL, strdup("_frama_c_vmt")),
            tkind_TStandard())),
        opt_some_container(
          init_expr_Compound_init(
            cons_container(
              init_expr_Single_init(
                expression_cons(
                  copy_loc(classLoc),
                  exp_node_PointerCast(
                    qual_type_cons(
                      NULL,
                      typ_Pointer(
                        pkind_PDataPointer(
                          qual_type_cons(
                            NULL,
                            typ_Struct(
                              qualified_name_cons(
                                NULL, strdup("_frama_c_vmt_content")),
                              tkind_TStandard()))))),
                    reference_or_pointer_kind_RPKPointer(),
                    expression_cons(
                      copy_loc(classLoc),
                      exp_node_Variable(
                        variable_Global(qualified_name_dup(vmtName))))))),
              cons_container(
                init_expr_Single_init(
                  makeIntLiteral(
                    classLoc,
                    IINT,
                    _currentClassInfo.front().numberOfMethods())),
                cons_container(
                  init_expr_Single_init(
                    expression_cons(
                      copy_loc(classLoc),
                      exp_node_Address(
                        expression_cons(
                          copy_loc(classLoc),
                          exp_node_Variable(
                            variable_Global(bareNameRtti)))))),
                  NULL))))),
        false,
        false));
  };
}

void
RTTITable::exitClass(const Clang_utils& utils, ForwardReferenceList& content,
    ForwardReferenceList& globals, location classLoc) {
  assert(!_currentClass.empty());
  if (_currentClassInfo.front().hasVirtualMethods()
       || _currentClassInfo.front().hasVirtualBaseClasses()) {
    const clang::CXXRecordDecl::base_class_const_iterator base
      = _currentClass.front()->bases_begin();
    bool shouldInsertPVMT = _currentClassInfo.front().hasVirtualMethods();
    if (base != _currentClass.front()->bases_end()) {
      const clang::Type* type = base->getType().getTypePtr();
      const clang::CXXRecordDecl* baseClass = type->getAsCXXRecordDecl();
      if (baseClass)
        // If we already have a VMT as first field, just reuse it.
        shouldInsertPVMT &= !hasVirtualMethods(baseClass);
    };
    insertStaticVMTDeclaration(content, classLoc);
    insertStaticBaseClassesDeclaration(content, classLoc);
    insertStaticRTTIDeclaration(content, classLoc);
    insertStaticVMTHeaderDeclaration(content, classLoc);

    if (shouldInsertPVMT)
      content.getFront() = cons_container(
        class_decl_CFieldDecl(
          copy_loc(classLoc),
          strdup("pvmt"),
          qual_type_cons(
            NULL,
            typ_Pointer(
              pkind_PDataPointer(
                qual_type_cons(
                  NULL,
                  typ_Struct(
                    qualified_name_cons(
                      NULL, strdup("_frama_c_vmt")), tkind_TStandard()))))),
          opt_none(),
          false),
        content.getFront());
    std::vector<list*>::const_iterator pvmtInsertionIterEnd
      = _pvmtInsertionPoints.front().end();
    for (std::vector<list*>::const_iterator pvmtInsertionIter
           = _pvmtInsertionPoints.front().begin();
        pvmtInsertionIter != pvmtInsertionIterEnd; ++pvmtInsertionIter)
      addPvmtSetter(utils,_currentClass.front(), **pvmtInsertionIter, classLoc);
    if (!_hasInitRTTIFunctions) {
      insertRttiPrelude(globals, classLoc);
      _hasInitRTTIFunctions = true;
    };

    qualified_name vmtName = insertStaticVMTDefinition(utils, globals,
        classLoc);
    qualified_name nameBaseClasses = insertStaticBaseClassesDefinition(utils,
        globals, classLoc);
    insertDeclStaticVMTHeaderDefinition(globals, classLoc, vmtName);
    qualified_name nameRtti = insertStaticRTTIDefinition(utils, globals,
        classLoc, vmtName, nameBaseClasses);
    insertStaticVMTHeaderDefinition(utils, globals, classLoc, vmtName,
        nameRtti);

    if (!_delayedMethodCalls.empty()) {
      std::map<const clang::CXXRecordDecl*, DelayedMethodCalls>::iterator
        found = _delayedMethodCalls.find(_currentClass.front());
      if (found != _delayedMethodCalls.end()) {
        found->second.updateWith(utils, _currentClassInfo.front());
        _delayedMethodCalls.erase(found);
      };
    };

    std::pair<std::map<const clang::CXXRecordDecl*, ClassInfo>::iterator, bool>
      res = _classInfoTable.insert(std::make_pair(_currentClass.front(),
            ClassInfo()));
    assert(res.second);
    res.first->second.swap(_currentClassInfo.front());
  } else {
      /* class has neither base class nor virtual method. We nevertheless
         generate an empty Rtti structure so that it can be used by future
         classes that inherit from it. There are however two exceptions for
         which we know noone will inherit from the current class:
          - in extern "C" mode, we assume that structs will never 
          belong to the class hierarchy
          - an anonymous class (whose Identifier is NULL) can't be inherited.
      */
    if (!utils.isExternCContext(_currentClass.front())
        && _currentClass.front()->getIdentifier()) {
      insertStaticVMTDeclaration(content, classLoc);
      insertStaticBaseClassesDeclaration(content, classLoc);
      insertStaticRTTIDeclaration(content, classLoc);
      insertStaticVMTHeaderDeclaration(content, classLoc);
      insertStaticEmptyRTTIDefinition(utils, globals, classLoc);
    }
  };
  exitClass();
}

void
RTTITable::retrieveMethodIndex(const Clang_utils& utils,
    const clang::CXXRecordDecl* classCaller, clang::CXXMethodDecl* methodCalled,
    int64_t* methodIndex, /* inheritance */ list* shiftObject,
    /* inheritance */ list* shiftPvmt)
{ std::map<const clang::CXXRecordDecl*, ClassInfo>::const_iterator
    found = _classInfoTable.find(classCaller);
  if (found != _classInfoTable.end()) {
    const ClassInfo& methodTable = found->second;
    const InheritancePath* inheritancePath = NULL;
    const VirtualInheritancePath* virtualInheritancePath = NULL;
    *methodIndex = methodTable.getIndexOfMethod(methodCalled,
        inheritancePath, virtualInheritancePath);
    ForwardReferenceList shiftEnd(*shiftObject);
    if (virtualInheritancePath) {
      tkind templateParameters =
        utils.makeTemplateKind(virtualInheritancePath->first);
      shiftEnd.insertContainer(
        inheritance_cons(
          utils.makeQualifiedName(*virtualInheritancePath->first),
          templateParameters,
          PUBLIC, VVIRTUAL, virtualInheritancePath->second));
    };
    InheritancePath::const_iterator iterEnd = inheritancePath->end();
    for (InheritancePath::const_iterator iter = inheritancePath->begin();
        iter != iterEnd; ++iter) {
      tkind templateParameters = utils.makeTemplateKind(iter->first);
      shiftEnd.insertContainer(
        inheritance_cons(
          utils.makeQualifiedName(*iter->first),
          templateParameters,
          PUBLIC, VSTANDARD, iter->second));
    };
    if (!methodTable.hasPvmtAsFirstField()) {
      shiftEnd = ForwardReferenceList(*shiftPvmt);
      inheritancePath = &methodTable.getPvmtField();
      InheritancePath::const_reverse_iterator iterEnd = inheritancePath->rend(),
          iter = inheritancePath->rbegin();
      for (; iter != iterEnd; ++iter) {
        tkind templateParameters = utils.makeTemplateKind(iter->first);
        shiftEnd.insertContainer(
          inheritance_cons(
            utils.makeQualifiedName(*iter->first), templateParameters,
            PUBLIC, VSTANDARD, iter->second));
      };
    };
  }
  else {
    std::map<const clang::CXXRecordDecl*, DelayedMethodCalls>::iterator
      found = _delayedMethodCalls.find(classCaller);
    if (found == _delayedMethodCalls.end())
      found = _delayedMethodCalls.insert(std::make_pair(classCaller,
        DelayedMethodCalls())).first;
    found->second.addMethodCall(methodCalled, methodIndex, shiftObject,
        shiftPvmt);
  };
}

void
RTTITable::retrieveBaseIndex(const Clang_utils& utils,
    const clang::CXXRecordDecl* classCaller, clang::CXXRecordDecl* baseClass,
    int64_t* accessIndex)
{ std::map<const clang::CXXRecordDecl*, ClassInfo>::const_iterator
    found = _classInfoTable.find(classCaller);
  if (found != _classInfoTable.end()) {
    const ClassInfo& methodTable = found->second;
    bool isVirtual = false;
    *accessIndex = methodTable.getBasePosition(baseClass, isVirtual);
  }
  else {
    std::map<const clang::CXXRecordDecl*, DelayedMethodCalls>::iterator
      found = _delayedMethodCalls.find(classCaller);
    if (found == _delayedMethodCalls.end())
      found = _delayedMethodCalls.insert(std::make_pair(classCaller,
        DelayedMethodCalls())).first;
    found->second.addFieldAccess(baseClass, accessIndex);
  };
}

