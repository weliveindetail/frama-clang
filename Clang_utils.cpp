/**************************************************************************/
/*                                                                        */
/*  This file is part of Frama-Clang                                      */
/*                                                                        */
/*  Copyright (C) 2012-2018                                               */
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

// Implementations of the functions declared in Clang_utils.h

#include "Clang_utils.h"
#include "ClangVisitor.h"

extern "C" {

void free_type(qual_type obj) {
  { list elt = (*obj).qualifier;
    while(elt) {
      list tmp=elt->next;
      free(elt);
      elt=tmp;
    }
  }
  if ((*obj).plain_type)
    free_typ((*obj).plain_type);
  free(obj);
}

} // end of extern "C"

bool is_same_qualification(list l1, list l2) {
  while(l1 && l2) {
    if (!qualification_equal(
          (qualification)l1->element.container,
          (qualification)l2->element.container))
      return false;
    l1 = l1->next;
    l2 = l2->next;
  }
  if (l1 || l2) return false;
  return true;
}

int compare_qualification(list l1, list l2);

int
compare_qualified_name(qualified_name n1, qualified_name n2) {
  int result = compare_qualification(n1->prequalification,
      n2->prequalification);
  if (result == 0)
    result = strcmp(n1->decl_name, n2->decl_name);
  return result;
}

int compare_template_parameter(template_parameter tp1, template_parameter tp2);

int
compare_typ(typ t1, typ t2) {
  int result = 0;
  if (t1->tag_typ != t2->tag_typ)
    result = (t1->tag_typ < t2->tag_typ) ? -1 : 1;
  else {
    switch (t1->tag_typ) {
      case VOID: result = 0; break;
      case INT:
        result = (t1->cons_typ.Int.kind < t2->cons_typ.Int.kind) ? -1
          : ((t1->cons_typ.Int.kind > t2->cons_typ.Int.kind) ? 1 : 0);
        break;
      case ENUM:
        result = compare_qualified_name(t1->cons_typ.Enum.kind->body,
            t2->cons_typ.Enum.kind->body);
        break;
      case FLOAT:
        result = (t1->cons_typ.Float.kind < t2->cons_typ.Float.kind) ? -1
          : ((t1->cons_typ.Float.kind > t2->cons_typ.Float.kind) ? 1 : 0);
        break;
      case POINTER:
      case LVREFERENCE:
      case RVREFERENCE:
        { pkind pk1 =
            (t1->tag_typ == POINTER)
            ? t1->cons_typ.Pointer.kind
            : (t1->tag_typ == LVREFERENCE
               ? t1->cons_typ.LVReference.kind
               : t1->cons_typ.RVReference.kind);
          pkind pk2 =
            (t2->tag_typ == POINTER)
            ? t2->cons_typ.Pointer.kind
            : (t2->tag_typ == LVREFERENCE
               ? t2->cons_typ.LVReference.kind
               : t2->cons_typ.RVReference.kind);
          if (pk1->tag_pkind != pk2->tag_pkind)
            result = (pk1->tag_pkind < pk2->tag_pkind) ? -1 : 1;
          else if (pk1->tag_pkind == PDATAPOINTER)
            result = compare_typ(pk1->cons_pkind.PDataPointer.subtype
              ->plain_type, pk2->cons_pkind.PDataPointer.subtype->plain_type);
        };
        break;
      case ARRAY:
        result = compare_typ(t1->cons_typ.Array.kind->subtype->plain_type,
            t2->cons_typ.Array.kind->subtype->plain_type);
        if (result == 0)
          result = (t1->cons_typ.Array.kind->dimension < t2->cons_typ.Array
            .kind->dimension) ? -1 : ((t1->cons_typ.Array.kind->dimension
                > t2->cons_typ.Array.kind->dimension) ? 1 : 0);
        break;
      case STRUCT:
      case UNION:
        if (t1->tag_typ == STRUCT)
          result = compare_qualified_name(t1->cons_typ.Struct.body,
              t2->cons_typ.Struct.body);
        else
          result = compare_qualified_name(t1->cons_typ.Union.body,
              t2->cons_typ.Union.body);
        if (result == 0) {
          tkind tk1 = (t1->tag_typ == STRUCT)
              ? t1->cons_typ.Struct.template_kind
              : t1->cons_typ.Union.template_kind;
          tkind tk2 = (t2->tag_typ == STRUCT)
              ? t2->cons_typ.Struct.template_kind
              : t2->cons_typ.Union.template_kind;
          if (tk1->tag_tkind != tk2->tag_tkind)
            result = (tk1->tag_tkind < tk2->tag_tkind) ? -1 : 1;
          else if (tk1->tag_tkind == TTEMPLATEINSTANCE) {
            /* template_parameter */ list fstInstParam = tk1->cons_tkind
                .TTemplateInstance.parameters;
            /* template_parameter */ list sndInstParam = tk2->cons_tkind
                .TTemplateInstance.parameters;
            while (fstInstParam && sndInstParam && result == 0) {
              template_parameter fstTempParam = (template_parameter)
                  fstInstParam->element.container;
              template_parameter sndTempParam = (template_parameter)
                  sndInstParam->element.container;
              result = compare_template_parameter(fstTempParam, sndTempParam);
              fstInstParam = fstInstParam->next;
              sndInstParam = sndInstParam->next;
            }
            if (result == 0)
              result = (fstInstParam || sndInstParam) ? (fstInstParam?1:-1) : 0;
          };
        };
        break;
      case NAMED:
        result = compare_qualified_name(t1->cons_typ.Named.name,
            t2->cons_typ.Named.name);
        break;
    }
  };
  return result;
}

int
compare_compilation_constant(compilation_constant cc1, compilation_constant cc2)
{ int result = 0;
  if (cc1->tag_compilation_constant != cc2->tag_compilation_constant)
    result = (cc1->tag_compilation_constant < cc2->tag_compilation_constant)
      ? -1 : 1;
  else if (cc1->tag_compilation_constant == INTCST)
    result = (cc1->cons_compilation_constant.IntCst.value
          < cc2->cons_compilation_constant.IntCst.value)
      ? -1 : ((cc1->cons_compilation_constant.IntCst.value
          > cc2->cons_compilation_constant.IntCst.value)
      ? 1 : 0);
  else if (cc1->tag_compilation_constant == ENUMCST)
    result =
      (cc1->cons_compilation_constant.EnumCst.value <
       cc2->cons_compilation_constant.EnumCst.value )
      ? -1 :
      ((cc1->cons_compilation_constant.EnumCst.value >
        cc2->cons_compilation_constant.EnumCst.value )
       ? 1 : 0);
  else if (cc1->tag_compilation_constant == TYPECST)
    result = compare_typ(cc1->cons_compilation_constant.TypeCst.arg,
        cc2->cons_compilation_constant.TypeCst.arg);
  return result;
}

int
compare_template_parameter(template_parameter tp1, template_parameter tp2) {
  int result = 0;
  if (tp1->tag_template_parameter !=
      tp2->tag_template_parameter)
    result = (tp1->tag_template_parameter < tp2->tag_template_parameter)?-1:1;
  else if (tp1->tag_template_parameter == TPSTRUCTORCLASS)
    result = compare_qualified_name(tp1->cons_template_parameter.TPStructOrClass
        .name, tp2->cons_template_parameter.TPStructOrClass.name);
  else if (tp1->tag_template_parameter == TPTYPENAME)
    result = compare_typ(tp1->cons_template_parameter.TPTypename.value
      ->plain_type, tp2->cons_template_parameter.TPTypename.value->plain_type);
  else if (tp1->tag_template_parameter == TPCONSTANT)
    result = compare_compilation_constant(tp1->cons_template_parameter
      .TPConstant.value, tp2->cons_template_parameter.TPConstant.value);
  else if (tp1->tag_template_parameter == TPDECLARATION)
    result = compare_qualified_name(tp1->cons_template_parameter.TPDeclaration
      .value, tp2->cons_template_parameter.TPDeclaration.value);
  else
    assert(false);
  return result;
}

int
compare_qualification(/* qualification */ list l1, /* qualification */ list l2)
{ int result = 0;
  while(l1 && l2 && result == 0) {
    qualification fst = (qualification)l1->element.container,
                  snd = (qualification)l2->element.container;
    if (fst->tag_qualification != snd->tag_qualification)
      result = (fst->tag_qualification < snd->tag_qualification) ? -1 : 1;
    else if (fst->tag_qualification == QNAMESPACE)
      result = strcmp(fst->cons_qualification.QNamespace.name,
          snd->cons_qualification.QNamespace.name);
    else if (fst->tag_qualification == QSTRUCTORCLASS)
      result = strcmp(fst->cons_qualification.QStructOrClass.name,
          snd->cons_qualification.QStructOrClass.name);
    else if (fst->tag_qualification == QTEMPLATEINSTANCE) {
      result = strcmp(fst->cons_qualification.QTemplateInstance.name,
          snd->cons_qualification.QTemplateInstance.name);
      if (result == 0) {
        /* template_parameter */ list fstInstParam = fst->cons_qualification
            .QTemplateInstance.parameters;
        /* template_parameter */ list sndInstParam = snd->cons_qualification
            .QTemplateInstance.parameters;
        while (fstInstParam && sndInstParam && result == 0) {
          template_parameter fstTempParam = (template_parameter)
              fstInstParam->element.container;
          template_parameter sndTempParam = (template_parameter)
              sndInstParam->element.container;
          result = compare_template_parameter(fstTempParam, sndTempParam);
          fstInstParam = fstInstParam->next;
          sndInstParam = sndInstParam->next;
        }
        if (result == 0)
          result = (fstInstParam || sndInstParam) ? (fstInstParam ? 1:-1) : 0;
      };
    }
    else
      assert(false);
    l1 = l1->next;
    l2 = l2->next;
  }
  return result ? result : ((l1 || l2) ? (l1 ? 1:-1) : 0);
}

namespace Acsl {

int
GlobalContext::TemplateQualification::compare(const NestedContext& c) const
{ assert(c.isTemplateQualification());
  int result = 0;
  /* template_parameter */ list l1 = _parameters;
  /* template_parameter */ list l2= c.asTemplateQualification()._parameters;
  while(l1 && l2 && result == 0) {
    template_parameter param1 = (template_parameter) l1->element.container,
                       param2 = (template_parameter) l2->element.container;
    result = compare_template_parameter(param1, param2);
    l1 = l1->next;
    l2 = l2->next;
  }
  return result ? result : ((l1 || l2) ? (l1 ? 1:-1) : 0);
}

GlobalContext::TemplateQualification*
GlobalContext::Qualification::findInstance(
    /* template_parameter */ list parameters) const
{ TemplateQualification locate(NULL);
  locate._parameters = parameters;
  NestedContext::SonsSet::iterator found = mSons.find(&locate);
  locate._parameters = NULL;
  GlobalContext::NestedContext* result
      = (found != mSons.end()) ? *found : NULL;
  if (result)
    assert(result->isTemplateQualification());
  return result ? &result->asTemplateQualification() : NULL;
}

void
GlobalContext::init() { // add Utf8_logic::boolean
  Qualification* qualification = new Qualification("Utf8_logic", QNAMESPACE);
  _logicTable.insert(qualification);
  LogicType* type =
    new LogicType(
      "boolean",
      logic_type_info_cons(
        qualified_name_cons(
          cons_container(qualification_QNamespace(strdup("Utf8_logic")), NULL),
          strdup("boolean")),
        true, // we are linking to standard ACSL booleans here.
        NULL /* string list */, opt_none()));
  qualification->ssons()->insert(type);
  type->setParent(qualification);
}

GlobalContext::NestedContext*
GlobalContext::find(const std::string& identifier, NestedContext* start) const {
  const NestedContext::SonsSet* sons = NULL;
  if (start) {
    sons = start->ssons();
    if (!sons) {
      sons = start->sparent() ? start->sparent()->ssons() : &_logicTable;
      assert(sons);
      start = start->sparent();
    };
  }
  else
    sons = &_logicTable;
  while (sons) {
    NestedContext locateIdentifier(identifier);
    NestedContext::SonsSet::const_iterator found
      = sons->find(&locateIdentifier);
    if (found != sons->end())
      return *found;
    if (start) {
      if (start->isTemplateQualification()) {
         start = start->sparent();
         assert(start);
      };
      NestedContext* parent = start->sparent();
      sons = parent ? parent->ssons() : &_logicTable;
      assert(sons);
      start = parent;
    }
    else
      sons = NULL;
  };
  return NULL;
}

GlobalContext::NestedContext*
GlobalContext::find(qualified_name identifier, NestedContext* start) const {
  /* qualification */ list prequalification = identifier->prequalification;
  if (!prequalification)
    return find(identifier->decl_name, start);
  std::string name;
  qualification qualif = (qualification) prequalification->element.container;
  if (qualif->tag_qualification == QNAMESPACE)
    name = qualif->cons_qualification.QNamespace.name;
  else if (qualif->tag_qualification == QSTRUCTORCLASS)
    name = qualif->cons_qualification.QStructOrClass.name;
  else if (qualif->tag_qualification == QTEMPLATEINSTANCE)
    name = qualif->cons_qualification.QTemplateInstance.name;
  else
    { assert(false); }
  NestedContext* current = find(name, start);
  if (!current)
    return NULL;
  prequalification = prequalification->next;
  while (prequalification) {
    const NestedContext::SonsSet* sons = current->ssons();
    if (!sons)
      return NULL;
    qualif = (qualification) prequalification->element.container;
    if (qualif->tag_qualification == QNAMESPACE)
      name = qualif->cons_qualification.QNamespace.name;
    else if (qualif->tag_qualification == QSTRUCTORCLASS)
      name = qualif->cons_qualification.QStructOrClass.name;
    else if (qualif->tag_qualification == QTEMPLATEINSTANCE)
      name = qualif->cons_qualification.QTemplateInstance.name;
    else
      { assert(false); }
    NestedContext locateName(name);
    NestedContext::SonsSet::iterator found = sons->find(&locateName);
    if (found == sons->end())
      return NULL;
    if (qualif->tag_qualification == QTEMPLATEINSTANCE) {
      TemplateQualification locateInstance(NULL);
      locateInstance._parameters = qualif->cons_qualification
          .QTemplateInstance.parameters;
      NestedContext::SonsSet::iterator foundInstance = (*found)->ssons()
          ->find(&locateInstance);
      locateInstance._parameters = NULL;
      if (foundInstance == (*found)->ssons()->end())
        return NULL;
      current = *foundInstance;
    }
    else
      current = *found;
    prequalification = prequalification->next;
  };
  const NestedContext::SonsSet* sons = current->ssons();
  if (!sons)
    return NULL;
  NestedContext locateName(identifier->decl_name);
  NestedContext::SonsSet::iterator found = sons->find(&locateName);
  return (found != sons->end()) ? *found : NULL;
}

GlobalContext::NestedContext*
GlobalContext::findAbsolute(qualified_name identifier) const {
  /* qualification */ list prequalification = identifier->prequalification;
  if (!prequalification) {
    NestedContext locateName(identifier->decl_name);
    NestedContext::SonsSet::iterator found = _logicTable.find(&locateName);
    return (found != _logicTable.end()) ? *found : NULL;
  };
  NestedContext* current = NULL;
  while (prequalification) {
    const NestedContext::SonsSet* sons = current
        ? current->ssons() : &_logicTable;
    if (!sons)
      return NULL;
    std::string name;
    qualification qualif = (qualification) prequalification->element.container;
    if (qualif->tag_qualification == QNAMESPACE)
      name = qualif->cons_qualification.QNamespace.name;
    else if (qualif->tag_qualification == QSTRUCTORCLASS)
      name = qualif->cons_qualification.QStructOrClass.name;
    else if (qualif->tag_qualification == QTEMPLATEINSTANCE)
      name = qualif->cons_qualification.QTemplateInstance.name;
    else
      { assert(false); }
    NestedContext locateName(name);
    NestedContext::SonsSet::iterator found = sons->find(&locateName);
    if (found == sons->end())
      return NULL;
    if (qualif->tag_qualification == QTEMPLATEINSTANCE) {
      TemplateQualification locateInstance(NULL);
      locateInstance._parameters = qualif->cons_qualification
          .QTemplateInstance.parameters;
      NestedContext::SonsSet::iterator foundInstance = (*found)->ssons()
          ->find(&locateInstance);
      locateInstance._parameters = NULL;
      if (foundInstance == (*found)->ssons()->end())
        return NULL;
      current = *foundInstance;
    }
    else
      current = *found;
    prequalification = prequalification->next;
  };
  NestedContext::SonsSet* sons = current->ssons();
  if (!sons)
    return NULL;
  NestedContext locateName(identifier->decl_name);
  NestedContext::SonsSet::iterator found = sons->find(&locateName);
  return (found != sons->end()) ? *found : NULL;
}
  
qualified_name
GlobalContext::Qualification::makeRecordName() const {
  /* qualification */ list qualifier = NULL;
  NestedContext* parent = sparent();
  while (parent) {
    if (parent->isQualification()) {
      qualifier = cons_container(((const Qualification&) *parent)
          .getQualification(), qualifier);
      parent = parent->sparent();
    }
    else if (parent->isTemplateQualification()) {
      NestedContext* rightParent = parent->sparent();
      assert(rightParent && parent->isQualification());
      qualifier = cons_container(((const TemplateQualification&)
          *parent).getQualification(strdup(((const Qualification&) *rightParent)
            .getName().c_str())), qualifier);
      parent = rightParent->sparent();
    }
    else
      assert(false);
  };
  return qualified_name_cons(qualifier, strdup(getName().c_str()));
}

/* qualification */ list
GlobalContext::Qualification::makeQualificationList() const {
  /* qualification */ list result = cons_container(getQualification(), NULL);
  NestedContext* parent = sparent();
  while (parent) {
    if (parent->isQualification()) {
      result = cons_container(((const Qualification&) *parent)
          .getQualification(), result);
      parent = parent->sparent();
    }
    else if (parent->isTemplateQualification()) {
      NestedContext* rightParent = parent->sparent();
      assert(rightParent && parent->isQualification());
      result = cons_container(((const TemplateQualification&)
          *parent).getQualification(strdup(((const Qualification&) *rightParent)
            .getName().c_str())), result);
      parent = rightParent->sparent();
    }
    else
      assert(false);
  };
  return result;
}

/* qualification */ list
GlobalContext::TemplateQualification::makeQualificationList() const {
  NestedContext* parent = sparent();
  assert(parent && parent->isQualification());
  /* qualification */ list result = cons_container(
      getQualification(strdup(((const Qualification&) *parent)
          .getName().c_str())), NULL);
  parent = parent->sparent();
  while (parent) {
    if (parent->isQualification()) {
      result = cons_container(((const Qualification&) *parent)
          .getQualification(), result);
      parent = parent->sparent();
    }
    else if (parent->isTemplateQualification()) {
      NestedContext* rightParent = parent->sparent();
      assert(rightParent && parent->isQualification());
      result = cons_container(((const TemplateQualification&)
          *parent).getQualification(strdup(((const Qualification&) *rightParent)
            .getName().c_str())), result);
      parent = rightParent->sparent();
    }
    else
      assert(false);
  };
  return result;
}

} // end of namespace Acsl

expression Intermediate_ast::makeFloatConstant(
  const location loc, fkind k, const char* repr) {
  return
    expression_cons(
      copy_loc(loc),
      exp_node_Constant(
        compilation_constant_FloatCst(k,strdup(repr))));
}

expression Intermediate_ast::makeIntLiteral(
  const location loc, ikind k, long value) {
  return expression_cons(
    copy_loc(loc),
    exp_node_Constant(compilation_constant_IntCst(k,ICLITERAL,value)));
}

expression Intermediate_ast::makeStringLiteral(
  const location loc, const char* str) {
  return expression_cons(copy_loc(loc), exp_node_String(strdup(str))); }

expression Intermediate_ast::makeFloatZero(const location loc, fkind k) {
  const char* r;
  switch (k) {
    case FFLOAT: r = "0.0f"; break;
    case FDOUBLE: r = "0.0"; break;
    case FLONGDOUBLE: r = "0.0l"; break;
  }
  return makeFloatConstant(loc,k,r);
}

expression Intermediate_ast::makeNullPointer(
  const location loc, qual_type pointee) {
  return
    expression_cons(
      copy_loc(loc),
      exp_node_PointerCast(
        qual_type_cons(NULL, typ_Pointer(pkind_PDataPointer(pointee))),
        reference_or_pointer_kind_RPKPointer(),
        makeIntLiteral(loc, IINT, 0)));
}

qual_type Intermediate_ast::makeStructType(qualified_name struct_name) {
  return qual_type_cons(NULL, typ_Struct(struct_name, tkind_TStandard()));
}


location
Clang_utils::makeLocation(clang::SourceRange const& locs) const
{ clang::SourceLocation loc_start = locs.getBegin();
  clang::SourceLocation loc_end = locs.getEnd();
  clang::SourceManager const& sources = _context->getSourceManager();
  clang::PresumedLoc ploc_start = sources.getPresumedLoc(loc_start);
  clang::PresumedLoc ploc_end = sources.getPresumedLoc(loc_end);
  const char* file1;
  unsigned line1;
  unsigned col1;
  if (ploc_start.isValid()) {
    file1 = strdup(ploc_start.getFilename());
    line1 = ploc_start.getLine();
    col1 = ploc_start.getColumn();
  } else {
    file1 = strdup("<unknown>");
    line1 = 0;
    col1 = 0;
  }
  const char* file2;
  unsigned line2;
  unsigned col2;
  if (ploc_end.isValid()) {
    file2 = strdup(ploc_end.getFilename());
    line2 = ploc_end.getLine();
    col2 = ploc_end.getColumn();
  } else {
    file2 = strdup("<unknown>");
    line2 = 0;
    col2 = 0;
  }
  return cons_location(file1, line1,col1, file2,line2,col2);
}

location
Clang_utils::makeSingleLocation(clang::SourceLocation const& loc) const
{ clang::SourceManager const& sources = _context->getSourceManager();
  clang::PresumedLoc ploc = sources.getPresumedLoc(loc);
  const char* fileb = ploc.getFilename();
  const char* file = strdup(fileb?fileb:"<unknown>");
  unsigned line = fileb ? ploc.getLine() : 0;
  unsigned col = fileb ? ploc.getColumn() : 0;
  return cons_location(file, line,col, strdup(file),line,col);
}

location
Clang_utils::makeDeclLocation(clang::Decl const& decl) const
{ return makeLocation(decl.getSourceRange()); }

location
Clang_utils::makeExprLocation(clang::Expr const& expr) const
{ return makeLocation(expr.getSourceRange()); }

const clang::TemplateArgumentList*
Clang_utils::findInstanceArguments(const clang::Decl* templateDecl) const {
  typedef std::vector<std::pair<const clang::Decl*,
      const clang::TemplateArgumentList*> > container;
  container::const_reverse_iterator iterEnd = _defaultTemplateInstances.rend();
  const clang::TemplateArgumentList* result = NULL;
  for (container::const_reverse_iterator iter = _defaultTemplateInstances
      .rbegin(); !result && iter != iterEnd; ++iter) {
    if (iter->first == templateDecl)
      result = iter->second;
  };
  return result;
}

const clang::TemplateArgument*
Clang_utils::findTemplateArgument(const std::string& name,
    const clang::NamedDecl*& templateParameter) const {
  typedef std::vector<std::pair<const clang::Decl*,
      const clang::TemplateArgumentList*> > container;
  container::const_reverse_iterator iterEnd = _defaultTemplateInstances.rend();
  const clang::TemplateArgument* result = NULL;
  for (container::const_reverse_iterator iter = _defaultTemplateInstances
      .rbegin(); !result && iter != iterEnd; ++iter) {
    const clang::TemplateDecl* TD = llvm::dyn_cast<clang::TemplateDecl>(
        iter->first);
    assert(TD && TD->getTemplateParameters());
    clang::TemplateParameterList::const_iterator paramEnd
        = TD->getTemplateParameters()->end();
    int index = 0;
    for (clang::TemplateParameterList::const_iterator
        param = TD->getTemplateParameters()->begin();
        !result && param != paramEnd; ++param) {
      if ((*param)->getNameAsString() == name) {
        int sizeArguments = iter->second->size();
        if (index < sizeArguments) {
          result = &(*iter->second)[index];
          templateParameter = *param;
        };
      };
      ++index;
    };
  };
  return result;
}

Acsl::GlobalContext::NestedContext*
Clang_utils::queryDeclLogicScope(const clang::DeclContext* clangScope) const {
  typedef Acsl::GlobalContext::NestedContext NestedContext;
  NestedContext* result = NULL;
  std::list<const clang::DeclContext*> clangHierarchy;
  while (clangScope->getParent()) {
    if (clangScope->isRecord() || clangScope->isNamespace())
      clangHierarchy.push_front(clangScope);
    clangScope = clangScope->getParent();
  };

  std::list<const clang::DeclContext*>::iterator endIter = clangHierarchy.end();
  for (std::list<const clang::DeclContext*>::iterator
      iter = clangHierarchy.begin(); iter != endIter; ++iter) {
    NestedContext::SonsSet*
      current = result ? result->ssons() : &_acslContext.logicTable();
    assert(current);
    std::string name;
    tag_qualification tag;
    /* template_parameter */ list templateParameters = NULL;
    if ((*iter)->isRecord()) {
      name = static_cast<const clang::RecordDecl*>(*iter)->getName().str();
      const clang::CXXRecordDecl*
        RD = llvm::dyn_cast<clang::CXXRecordDecl>(*iter);
      const clang::ClassTemplateSpecializationDecl* TSD = NULL;
      if (RD->getKind() == clang::Decl::ClassTemplateSpecialization)
        TSD = llvm::dyn_cast<clang::ClassTemplateSpecializationDecl>(RD);
      if (RD && TSD /* RD->getTemplateSpecializationKind()
            >= clang::TSK_ImplicitInstantiation */) {
        const clang::ClassTemplateSpecializationDecl* inst =
          llvm::dyn_cast<clang::ClassTemplateSpecializationDecl>(RD);
        assert (inst);
        templateParameters = getTemplateExtension(inst);
        tag = QTEMPLATEINSTANCE;
      }
      else if (RD && RD->getDescribedClassTemplate()
          && (RD->getDescribedClassTemplate()->getTemplatedDecl() == RD)) {
        const clang::TemplateArgumentList* defaultTemplateArgs
            = findInstanceArguments(RD->getDescribedClassTemplate());
        assert(defaultTemplateArgs);
        templateParameters = getTemplateExtension(RD->getLocation(),
          *defaultTemplateArgs);
        tag = QTEMPLATEINSTANCE;
      }
      else
        tag = QSTRUCTORCLASS;
    } else {
      assert((*iter)->isNamespace());
      name = static_cast<const clang::NamespaceDecl*>(*iter)->getName().str();
      tag = QNAMESPACE;
    };
    NestedContext locateContext(name);
    NestedContext::SonsSet::iterator found = current->find(&locateContext);
    if (found != current->end()) {
      result = *found;
      if (tag == QTEMPLATEINSTANCE) {
        assert(result->getType() == NestedContext::TQualification
          && ((const Acsl::GlobalContext::Qualification&) *result)
               .hasTemplateRecordType());
        Acsl::GlobalContext::TemplateQualification* localInstance =
          ((const Acsl::GlobalContext::Qualification&) *result)
            .findInstance(templateParameters);
        if (localInstance)
          result = localInstance;
        else {
          current = result->ssons();
          assert(current);
          Acsl::GlobalContext::TemplateQualification* newScopeResult
            = new Acsl::GlobalContext::TemplateQualification(templateParameters);
          current->insert(newScopeResult);
          newScopeResult->setParent(result);
          result = newScopeResult;
        };
      };
    }
    else {
      Acsl::GlobalContext::Qualification* scopeResult
        = new Acsl::GlobalContext::Qualification(name,tag);
      current->insert(scopeResult);
      scopeResult->setParent(result);
      result = scopeResult;
      if (tag == QTEMPLATEINSTANCE) {
        current = scopeResult->ssons();
        Acsl::GlobalContext::TemplateQualification* newScopeResult
          = new Acsl::GlobalContext::TemplateQualification(templateParameters);
        current->insert(newScopeResult);
        newScopeResult->setParent(result);
        result = newScopeResult;
      };
    };
  };
  return result;
}

const clang::NamedDecl*
Clang_utils::findAnonymousDecl(const std::string& name) const {
  std::map<const clang::Decl*, std::string>::const_iterator
    iterEnd = _anonymousMap.end();
  for (std::map<const clang::Decl*, std::string>::const_iterator
      iter = _anonymousMap.begin(); iter != iterEnd; ++iter) {
    if (iter->second == name) {
      assert(llvm::dyn_cast<clang::NamedDecl>(iter->first));
      return static_cast<const clang::NamedDecl*>(iter->first);
    };
  };
  return NULL;
}

std::string
Clang_utils::findAnonymousName(const clang::NamedDecl* decl) const {
  std::map<const clang::Decl*, std::string>::const_iterator
    found = _anonymousMap.find(decl);
  std::string result;
  if (found != _anonymousMap.end())
    result = found->second;
  return result;
}

qualified_name
Clang_utils::makeQualifiedName(const clang::NamedDecl& decl,
      bool doesAcceptInstanceFail) const {
  const clang::DeclContext *Ctx = decl.getDeclContext();
  const char* name = NULL;
  if (decl.getDeclName())
    name=copy_string(decl.getDeclName().getAsString());
  else {
    static std::map<const clang::NamedDecl*, qualified_name> anonymousTable;
    std::map<const clang::NamedDecl*, qualified_name>::iterator
        found = anonymousTable.find(&decl);
    if (found != anonymousTable.end())
      return qualified_name_dup(found->second);
    else {
      std::ostringstream nameResult;
      nameResult << "anonymous_variable_" << anonymousTable.size();
      qualified_name result = makeQualifiedName(Ctx,
          strdup(nameResult.str().c_str()), &decl);
      anonymousTable.insert(std::make_pair(&decl, result));
      return qualified_name_dup(result);
    };

    std::cerr << "No name to qualify !!!!" << std::endl;
    exit(2);
  }
  qualified_name result = makeQualifiedName(Ctx,name,&decl,NULL,
      doesAcceptInstanceFail);
  if (!result && doesAcceptInstanceFail)
    return NULL;
  assert(result);
  if (strlen(result->decl_name) == 0) {
    assert(result->prequalification);
    list className = result->prequalification;
    while (className->next)
      className = className->next;
    qualification name = (qualification) className->element.container;
    if (name->tag_qualification == QSTRUCTORCLASS)
      result->decl_name = strdup(name->cons_qualification.QStructOrClass.name);
    else if (name->tag_qualification == QTEMPLATEINSTANCE)
      result->decl_name = strdup(name->cons_qualification.QTemplateInstance
          .name);
    else
      assert(false);
  };
  return result;
}

qualified_name
Clang_utils::makeQualifiedName( const clang::DeclContext* Ctx, const char* name,
    const clang::NamedDecl* decl, tkind* templateParameters,
    bool doesAcceptInstanceFail) const {
  if (Ctx->isFunctionOrMethod()) {
    if (templateParameters && !*templateParameters)
      *templateParameters = tkind_TStandard();
    return qualified_name_cons(NULL, name);
  };

  list prefix = NULL;
  while (Ctx && llvm::isa<clang::NamedDecl>(Ctx)) {
    if (const clang::ClassTemplateSpecializationDecl *
        Spec = llvm::dyn_cast<clang::ClassTemplateSpecializationDecl>(Ctx)) {
      std::string name = Spec->getName().str();
      prefix =
        cons_container(
          qualification_QTemplateInstance(
            copy_string(name), getTemplateExtension(Spec)),
          prefix);
    }
    else if (const clang::NamespaceDecl *
              ND = llvm::dyn_cast<clang::NamespaceDecl>(Ctx)) {
      if (ND->isAnonymousNamespace()) {
        std::map<const clang::Decl*, std::string>::iterator
            found = _anonymousMap.find(ND->getOriginalNamespace());
        if (found == _anonymousMap.end()) {
          ++_anonymousIdent;
          std::ostringstream out;
          out << "anonymous_namespace_" << _anonymousIdent;
          found = _anonymousMap.insert(
              std::pair<const clang::Decl*, std::string>(
                  ND->getOriginalNamespace(), out.str())).first;
        };
        prefix = cons_container(qualification_QNamespace(
            copy_string(found->second.c_str())), prefix);
      }
      else
        prefix = cons_container(qualification_QNamespace(strdup(
            ND->getName().str().c_str())), prefix);
    }
    else if (const clang::RecordDecl *
              RD = llvm::dyn_cast<clang::RecordDecl>(Ctx)) {
      const clang::CXXRecordDecl *CXXRD = llvm::dyn_cast<clang::CXXRecordDecl>(RD);
      bool isTemplateInstance = CXXRD && CXXRD->getDescribedClassTemplate()
          && (CXXRD->getDescribedClassTemplate()->getTemplatedDecl() == CXXRD);
      if (!RD->getIdentifier()) {
        std::map<const clang::Decl*, std::string>::iterator
            found = _anonymousMap.find(RD->getDefinition());
        if (found == _anonymousMap.end()) {
          ++_anonymousIdent;
          std::ostringstream out;
          if (RD->getTagKind() == clang::TTK_Union)
            out << "anonymous_union_" << _anonymousIdent;
          else
            out << "anonymous_class_" << _anonymousIdent;
          found = _anonymousMap.insert(
              std::pair<const clang::Decl*, std::string>(RD->getDefinition(),
                  out.str())).first;
        };
        if (!isTemplateInstance)
          prefix = cons_container(qualification_QStructOrClass(
              copy_string(found->second.c_str())), prefix);
        else {
          const clang::TemplateArgumentList* defaultTemplateArgs
              = findInstanceArguments(CXXRD->getDescribedClassTemplate());
          assert(defaultTemplateArgs);
          prefix = cons_container(qualification_QTemplateInstance(
              copy_string(found->second.c_str()),
              getTemplateExtension(CXXRD->getLocation(), *defaultTemplateArgs)),
            prefix);
        };
      }
      else {
        if (!isTemplateInstance)
          prefix = cons_container(qualification_QStructOrClass(
              strdup(RD->getName().str().c_str())), prefix);
        else {
          const clang::TemplateArgumentList* defaultTemplateArgs
              = findInstanceArguments(CXXRD->getDescribedClassTemplate());
          assert(defaultTemplateArgs || doesAcceptInstanceFail);
          if (!defaultTemplateArgs) {
            // clang sometimes omits to specialize intermediate classes
            return NULL;
          }
          prefix = cons_container(qualification_QTemplateInstance(
              strdup(RD->getName().str().c_str()),
              getTemplateExtension(CXXRD->getLocation(), *defaultTemplateArgs)),
            prefix);
        };
      };
    }
    else if (/*const clang::EnumDecl *ED = */
             llvm::dyn_cast<clang::EnumDecl>(Ctx)) {
      // do nothing => avoid default break
    }
    else if (/*const clang::FunctionDecl *FD = */
             llvm::dyn_cast<clang::FunctionDecl>(Ctx)) {
      break;
      // const FunctionProtoType *FT = 0;
      // if (FD->hasWrittenPrototype())
      //   FT = dyn_cast<FunctionProtoType>(
      //     FD->getType()->castAs<FunctionType>());
      // list arguments = NULL;
      // if (FT) {
      //   unsigned NumParams = FD->getNumParams();
      //   for (unsigned i = 0; i < NumParams; ++i)
      //     arguments = cons_container(makeType(FD->getParamDecl(i)
      //         ->getType()), arguments);
      // }
      // if (FT->isVariadic())
      //   arguments = cons_container(make_variadic_type(), arguments);
      // prefix = cons_container(qualification_QFunction(
      //     strdup(FD->getName().str().c_str()), arguments), prefix);
    }
    else {
      break;
      // prefix = cons_container(qualification_QUnknown(strdup(cast<NamedDecl>
      //     (Ctx)->getName().str().c_str())), prefix);
    }
    Ctx = Ctx->getParent();
  };

  if (!name) {
    if (!decl) {
     std::cerr <<
      "Anonymous name with an empty declaration." <<
      "Can't generate appropriate name, aborting.";
     exit(2);
    }
    if (templateParameters && !*templateParameters)
      *templateParameters = tkind_TStandard();
    std::map<const clang::Decl*, std::string>::iterator found;
    if (llvm::isa<clang::RecordDecl>(decl)) {
     const clang::RecordDecl* record =
       static_cast<const clang::RecordDecl*>(decl);
     name=get_aggregate_name(record, templateParameters);
     return qualified_name_cons(prefix,name);
    }
    else {
     found = _anonymousMap.find(decl);
     if (found == _anonymousMap.end()) {
      ++_anonymousIdent;
      std::ostringstream out;
      out << "anonymous_other" << _anonymousIdent;
      found =
        _anonymousMap.insert(
         std::pair<const clang::Decl*, std::string>(decl, out.str())).first;
     };
    };
    return qualified_name_cons(prefix, copy_string(found->second));
  }
  if (templateParameters && !*templateParameters)
    *templateParameters = tkind_TStandard();
  return qualified_name_cons(prefix, name);
}

signature
Clang_utils::makeSignature(const clang::FunctionDecl& function) const {
  clang::SourceLocation loc = function.getLocation();
  qual_type resultType = makeType(loc,function.getReturnType());
  bool is_variadic = function.isVariadic();
  clang::FunctionDecl::param_const_iterator argEnd = function.param_end();
  list /* type */ parameters = NULL;
  ForwardReferenceList parametersList(parameters);
  for (clang::FunctionDecl::param_const_iterator
      argIter = function.param_begin();
      argIter < argEnd; ++argIter) {
    qual_type argType =
      makeType((*argIter)->getLocation(), (*argIter)->getType());
    parametersList.insertContainer(argType);
  };
  return signature_cons(resultType, parameters, is_variadic);
}

const char* Clang_utils::get_field_name(const clang::NamedDecl* decl) const{
  if (decl->getName().empty()) {
   std::map<const clang::Decl*, std::string>::iterator found =
    _anonymousMap.find(decl);
   if (found == _anonymousMap.end()) {
    ++_anonymousIdent;
    std::ostringstream out;
    out << "anonymous_" << _anonymousIdent;
    found = _anonymousMap.insert(
      std::pair<const clang::Decl*, std::string>(decl, out.str())).first;
   };
   return copy_string(found->second);
  }
  else
   return strdup(decl->getName().str().c_str());
}

template_parameter
Clang_utils::getTemplateExtension(
  const clang::SourceLocation& loc,
  const clang::TemplateArgument& argument,
  /* template_parameter */ ForwardReferenceList& argumentsList)
    const
{ switch (argument.getKind()) {
    case clang::TemplateArgument::Null:
      // an empty template argument, e.g., one that has not been deduced
      assert(false);
      break;
    case clang::TemplateArgument::Type: // argument is a type.
      return
        template_parameter_TPTypename(makeType(loc, argument.getAsType()));
    case clang::TemplateArgument::Declaration:
      // { clang::NamedDecl *ND = llvm::cast<clang::NamedDecl>(
      //       argument.getAsDecl());
      //   std::cerr << "Unsupported instance of template declaration: " 
      //     << ND->getName().str()
      //     << "\nAborting\n";
      //   //TODO: raise exception and try to continue with rest of file.
      //   exit(2);
      // };

      // argument is a declaration that was provided for a pointer,
      // reference, or pointer to member non-type template parameter.
      { qualified_name result = makeQualifiedName(*argument.getAsDecl());
        return template_parameter_TPDeclaration(result);
      };
    case clang::TemplateArgument::NullPtr:
      // argument is a null pointer or null pointer to member that
      // was provided for a non-type template parameter.
      return template_parameter_TPConstant(
        compilation_constant_IntCst(
          //opt_some_container(qualified_name_cons(NULL, strdup("nullptr"))),
          ILONG, ICSTATICCONST, 0));
    case clang::TemplateArgument::Integral:
      // argument is an integral value stored in an llvm::APSInt
      // that was provided for an integral non-type template parameter. 
      { const llvm::APSInt& val = argument.getAsIntegral();
        return template_parameter_TPConstant(
          compilation_constant_IntCst(
            //opt_some_container(qualified_name_cons(NULL, "")),
            IINT, ICLITERAL, (int64_t)val.getLimitedValue(UINT64_MAX)));
      };
    case clang::TemplateArgument::Template:
      // argument is a template name that was provided for a 
      // template template parameter.
      { qualified_name result = makeQualifiedName(*argument.getAsTemplate().getAsTemplateDecl());
        return template_parameter_TPDeclaration(result);
      };
      // description = "clang::TemplateArgument::Template";
      // break;
    case clang::TemplateArgument::TemplateExpansion:
      // argument is a pack expansion of a template name that was 
      // provided for a template template parameter.
      break;
    case clang::TemplateArgument::Expression:
      // argument is a value- or type-dependent expression
      // stored in an Expr*.
      break;
    case clang::TemplateArgument::Pack:
      // argument is actually a parameter pack. Arguments are stored
      // in the Args struct.
      { clang::TemplateArgument::pack_iterator iter = argument.pack_begin(),
          iterEnd = argument.pack_end();
        for (; iter != iterEnd; ++iter) {
          template_parameter parameter
            = getTemplateExtension(loc, *iter, argumentsList);
          if (parameter)
            argumentsList.insertContainer(parameter);
        };
      }
      return NULL;
  };
  std::cerr << "Unsupported instance of template declaration\n";
  //TODO: raise exception and try to continue with rest of file.
  return
    template_parameter_TPConstant(
      compilation_constant_IntCst(IINT, ICSTATICCONST, 0));
}

/* template_parameter */ list
Clang_utils::getTemplateExtension(
  const clang::SourceLocation& loc,
  const clang::TemplateArgumentList& parameters)
    const {
  int numberOfParameters = parameters.size();
  /* template_parameter */ list result = NULL;
  ForwardReferenceList parametersList(result);
  for (int paramIndex = 0; paramIndex < numberOfParameters; ++paramIndex) {
    const clang::TemplateArgument& argument = parameters[paramIndex];
    template_parameter parameter = getTemplateExtension(loc, argument,
      parametersList);
    if (parameter)
      parametersList.insertContainer(parameter);
  };
  return result;
}

const char*
Clang_utils::get_aggregate_name(const clang::RecordDecl* decl,
    tkind* templateParameters) const
{ const clang::CXXRecordDecl *RD = llvm::dyn_cast<clang::CXXRecordDecl>(decl);
  const clang::ClassTemplateSpecializationDecl* TSD = NULL;
  if (decl->getKind() == clang::Decl::ClassTemplateSpecialization)
    // do not handle partial specialization !
    TSD = llvm::dyn_cast<clang::ClassTemplateSpecializationDecl>(decl);
  if (RD && TSD /* RD->getTemplateSpecializationKind()
        >= clang::TSK_ImplicitInstantiation */) {
    const clang::ClassTemplateSpecializationDecl* inst = 
      llvm::dyn_cast<clang::ClassTemplateSpecializationDecl>(RD);
    assert(inst);
    if (templateParameters)
      *templateParameters = tkind_TTemplateInstance(getTemplateExtension(inst));
  }
  else if (templateParameters)
    *templateParameters = tkind_TStandard();
  if (decl->getName().empty()) {
   std::map<const clang::Decl*, std::string>::iterator found =
    _anonymousMap.find(decl);
   if (found == _anonymousMap.end()) {
     ++_anonymousIdent;
     std::ostringstream out;
     std::string kind = "";
     switch (decl->getTagKind()) {
       case clang::TTK_Struct: 
       case clang::TTK_Class: { kind = "class_"; break; }
       case clang::TTK_Union: { kind = "union_"; break; }
       default: break;
     }
     out << "anonymous_" << kind << _anonymousIdent;
     found = _anonymousMap.insert(
       std::pair<const clang::Decl*, std::string>(decl, out.str())).first;
    };
    return copy_string(found->second);
  };
  return strdup(decl->getName().str().c_str());
}

tkind
Clang_utils::makeTemplateKind(const clang::RecordDecl* decl) const
{ const clang::CXXRecordDecl *RD = llvm::dyn_cast<clang::CXXRecordDecl>(decl);
  const clang::ClassTemplateSpecializationDecl* TSD = NULL;
  if (decl->getKind() == clang::Decl::ClassTemplateSpecialization)
    // do not handle partial specialization !
    TSD = llvm::dyn_cast<clang::ClassTemplateSpecializationDecl>(decl);
  if (RD && TSD /* RD->getTemplateSpecializationKind()
        >= clang::TSK_ImplicitInstantiation */) {
    const clang::ClassTemplateSpecializationDecl* inst =
      llvm::dyn_cast<clang::ClassTemplateSpecializationDecl>(RD);
    return tkind_TTemplateInstance(getTemplateExtension(inst));
  }
  return tkind_TStandard();
}

bool
Clang_utils::isIntegralType(clang::BuiltinType const* typ) const {
  clang::BuiltinType::Kind kind = typ->getKind();
  return (kind >= clang::BuiltinType::Bool
      && kind <= clang::BuiltinType::Int128);
}

bool
Clang_utils::isSignedType(clang::BuiltinType const* typ) const {
  clang::BuiltinType::Kind kind = typ->getKind();
  return (kind >= clang::BuiltinType::Char_S
    && kind <= clang::BuiltinType::Int128);
}

bool
Clang_utils::isArithmeticType(clang::BuiltinType const* typ) const {
  clang::BuiltinType::Kind kind = typ->getKind();
  return (kind >= clang::BuiltinType::Bool
    && kind <= clang::BuiltinType::LongDouble);
}

bool
Clang_utils::isFloatingType(clang::BuiltinType const* typ) const {
  clang::BuiltinType::Kind kind = typ->getKind();
  return (kind >= clang::BuiltinType::Half
    && kind <= clang::BuiltinType::LongDouble);
}

typ Clang_utils::makeBuiltinType(
  clang::SourceLocation const& loc, clang::BuiltinType const* typ) const {
  switch(typ->getKind()) {
    case clang::BuiltinType::Void: return typ_Void();
    case clang::BuiltinType::Bool: return typ_Int(IBOOL);
    case clang::BuiltinType::Char_U:
      return typ_Int(ICHAR_U); /* char = unsigned char */
    case clang::BuiltinType::Char_S:
      return typ_Int(ICHAR_S); /* char = signed char */
    case clang::BuiltinType::WChar_U:
      return typ_Int(IWCHAR_U); /* wchar_t = unsigned */
    case clang::BuiltinType::WChar_S:
      return typ_Int(IWCHAR_S); /* wchar_t = signed */
    case clang::BuiltinType::UChar: return typ_Int(IUCHAR);
    case clang::BuiltinType::SChar: return typ_Int(ISCHAR);
    case clang::BuiltinType::Char16:  return typ_Int(ICHAR16);
    case clang::BuiltinType::Char32: return typ_Int(ICHAR32);
    case clang::BuiltinType::Short: return typ_Int(ISHORT);
    case clang::BuiltinType::UShort: return typ_Int(IUSHORT);
    case clang::BuiltinType::Int: return typ_Int(IINT);
    case clang::BuiltinType::UInt: return typ_Int(IUINT);
    case clang::BuiltinType::Long: return typ_Int(ILONG);
    case clang::BuiltinType::ULong: return typ_Int(IULONG);
    case clang::BuiltinType::LongLong: return typ_Int(ILONGLONG);
    case clang::BuiltinType::ULongLong: return typ_Int(IULONGLONG);
    case clang::BuiltinType::Float: return typ_Float(FFLOAT);
    case clang::BuiltinType::Double: return typ_Float(FDOUBLE);
    case clang::BuiltinType::LongDouble: return typ_Float(FLONGDOUBLE);
    case clang::BuiltinType::Int128: return typ_Int(ILONG);
    case clang::BuiltinType::UInt128: return typ_Int(IULONG);
    case clang::BuiltinType::NullPtr:
      return
        typ_Pointer(pkind_PDataPointer(qual_type_cons(NULL,typ_Void())));
    default:
     std::cerr 
       << loc_as_string(loc)
       << "Unsupported Builtin-type: " 
       << typ->getName(_context->getPrintingPolicy()).str()
       << "\nAborting\n";
     //TODO: raise exception and try to continue with rest of file.
     exit(2);
  }
}

typ Clang_utils::charType() const {
  if (_context->getLangOpts().CharIsSigned)
    return typ_Int(ICHAR_S);
  else
    return typ_Int(ICHAR_U);
}

typ Clang_utils::charPtrType() const {
  return typ_Pointer(pkind_PDataPointer(qual_type_cons(NULL,charType())));
}

logic_type
Clang_utils::makeBuiltinLogicType(
  clang::SourceLocation const& loc, clang::BuiltinType const* typ) const {
  switch(typ->getKind()) {
    case clang::BuiltinType::Void: return logic_type_Lvoid();
    case clang::BuiltinType::Bool:
      { 
        return logic_type_Lint(IBOOL);
      };
    case clang::BuiltinType::Char_U:
      return logic_type_Lint(ICHAR_U); /* char = unsigned char */
    case clang::BuiltinType::Char_S:
      return logic_type_Lint(ICHAR_S); /* char = signed char */
    case clang::BuiltinType::WChar_U:
      return logic_type_Lint(IWCHAR_U); /* wchar_t = unsigned */
    case clang::BuiltinType::WChar_S:
      return logic_type_Lint(IWCHAR_S); /* wchar_t = signed */
    case clang::BuiltinType::UChar: return logic_type_Lint(IUCHAR);
    case clang::BuiltinType::SChar: return logic_type_Lint(ISCHAR);
    case clang::BuiltinType::Char16: return logic_type_Lint(ICHAR16);
    case clang::BuiltinType::Char32: return logic_type_Lint(ICHAR32);
    case clang::BuiltinType::Short: return logic_type_Lint(ISHORT);
    case clang::BuiltinType::UShort: return logic_type_Lint(IUSHORT);
    case clang::BuiltinType::Int: return logic_type_Lint(IINT);
    case clang::BuiltinType::UInt: return logic_type_Lint(IUINT);
    case clang::BuiltinType::Long: return logic_type_Lint(ILONG);
    case clang::BuiltinType::ULong: return logic_type_Lint(IULONG);
    case clang::BuiltinType::LongLong: return logic_type_Lint(ILONGLONG);
    case clang::BuiltinType::ULongLong: return logic_type_Lint(IULONGLONG);
    case clang::BuiltinType::Float: return logic_type_Lfloat(FFLOAT);
    case clang::BuiltinType::Double: return logic_type_Lfloat(FDOUBLE);
    case clang::BuiltinType::LongDouble: return logic_type_Lfloat(FLONGDOUBLE);
    case clang::BuiltinType::Int128: return logic_type_Lint(ILONG);
    case clang::BuiltinType::UInt128: return logic_type_Lint(IULONG);
    case clang::BuiltinType::NullPtr:
      return logic_type_Lpointer(logic_type_Lvoid());
    default:
      std::cerr
        << loc_as_string(loc)
        << "Unsupported Builtin-type: " 
        << typ->getName(_context->getPrintingPolicy()).str()
        << "\nAborting\n";
     //TODO: raise exception and try to continue with rest of file.
     exit(2);
  }
}

bool Clang_utils::is_lambda(const clang::RecordDecl* rec) const {
  auto cxx_rec = llvm::dyn_cast<const clang::CXXRecordDecl>(rec);
  return cxx_rec && cxx_rec->isLambda();
}

/* capture */ list Clang_utils::make_capture_list(
  clang::CXXRecordDecl::capture_const_range captures) const {
  list lam_closure = NULL;
  auto cap = captures.end();
  auto end = captures.begin();
  while (cap != end) {
    cap--;
    switch (cap->getCaptureKind()) {
      case clang::LCK_This:
        lam_closure = cons_container(capture_Cap_this(true), lam_closure);
        break;
      case clang::LCK_StarThis:
        lam_closure = cons_container(capture_Cap_this(false), lam_closure);
        break;
      case clang::LCK_ByCopy:
      case clang::LCK_ByRef: {
        auto byref = cap->getCaptureKind() == clang::LCK_ByRef;
        auto var = cap->getCapturedVar();
        auto name = var->getNameAsString();
        auto typ = makeType(var->getLocation(), var->getType());
        lam_closure =
          cons_container(
            capture_Cap_id(copy_string(name), typ, byref), lam_closure);
        break;
      }
      case clang::LCK_VLAType: {
        std::cout << "Unsupported capture of VLA Type in Lambda Object";
        exit(2);
      }
    }
  }
  return lam_closure;
}

typ Clang_utils::make_lambda_type(
    clang::SourceLocation const& loc, clang::RecordDecl const* record,
    VirtualDeclRegistration* declRegistration) const
{
  auto cxx_rec = llvm::dyn_cast<const clang::CXXRecordDecl>(record);
  auto oper = cxx_rec->getLambdaCallOperator();
  auto sig = makeSignature(*oper);
  auto cap = make_capture_list(cxx_rec->captures());
  return typ_Lambda(sig,cap);
}

typ
Clang_utils::makePlainType(
  clang::SourceLocation const & loc,
  clang::QualType const& qt,
  VirtualDeclRegistration* declRegistration, bool isPOD) const {
  const clang::Type* type = qt.getTypePtr();
  std::string unsupported_kind;
  switch(type->getTypeClass()) {
    case clang::Type::Builtin:
      { assert(llvm::dyn_cast<const clang::BuiltinType>(type));
      return makeBuiltinType(loc,static_cast<clang::BuiltinType const*>(type));
      };
    case clang::Type::Pointer:
      { assert(llvm::dyn_cast<const clang::PointerType>(type));
        const clang::PointerType*
          pointerType = static_cast<clang::PointerType const*>(type);
        clang::QualType subPointerType = pointerType->getPointeeType();
        list/*<specifier>*/ subspec = make_specifier_list(subPointerType);
        typ subtype =
          makePlainType(
            loc,
            subPointerType,
            declRegistration ? declRegistration->getNameRegistration() : NULL,
            isPOD);
        if (subtype->tag_typ == LVREFERENCE || subtype->tag_typ == RVREFERENCE)
          subtype->tag_typ = POINTER;
        else {
          pkind pointerKind = pkind_PDataPointer(
              qual_type_cons(subspec, subtype));
          subtype = typ_Pointer(pointerKind);
        }
        return subtype;
      };
    case clang::Type::LValueReference:
      { const clang::LValueReferenceType* referenceType =
          llvm::dyn_cast<const clang::LValueReferenceType>(type);
        assert(referenceType);
        clang::QualType subReferenceType = referenceType->getPointeeType();
        list/*<specifier>*/ subspec = make_specifier_list(subReferenceType);
        assert(!isPOD);
        typ subtype =
          makePlainType(
            loc,
            subReferenceType,
            declRegistration ? declRegistration->getNameRegistration() : NULL,
            false);
        pkind referenceKind = pkind_PDataPointer(
            qual_type_cons(subspec, subtype));
        return typ_LVReference(referenceKind);
      };
    case clang::Type::RValueReference:
      { const clang::RValueReferenceType* referenceType =
          llvm::dyn_cast<const clang::RValueReferenceType>(type);
        assert(referenceType);
        clang::QualType subReferenceType = referenceType->getPointeeType();
        list/*<specifier>*/ subspec = make_specifier_list(subReferenceType);
        assert(!isPOD);
        typ subtype =
          makePlainType(
            loc,
            subReferenceType,
            declRegistration ? declRegistration->getNameRegistration() : NULL,
            false);
        pkind referenceKind = pkind_PDataPointer(
            qual_type_cons(subspec, subtype));
        return typ_RVReference(referenceKind);
      };
    case clang::Type::MemberPointer:
      // see FunctionProto for the method pointers
      { assert(llvm::dyn_cast<const clang::MemberPointerType>(type));
        const clang::MemberPointerType* memberPointerType =
          static_cast<clang::MemberPointerType const*>(type);
        clang::QualType pointee = memberPointerType->getPointeeType();
        typ tpointee =
          makePlainType(
            loc,
            pointee,
            declRegistration?declRegistration->getNameRegistration():NULL,
            isPOD);
        clang::QualType thisType =
          clang::QualType(memberPointerType->getClass(),0U);
        qual_type arg_this =
          qual_type_cons(
            NULL,
            typ_Pointer(
              pkind_PDataPointer(
                qual_type_cons(
                  NULL,
                  makePlainType(
                    loc,
                    thisType,
                    declRegistration?
                    declRegistration->getNameRegistration():NULL,isPOD)))));
        if (memberPointerType->isMemberFunctionPointer()) {
          // pointed type is already a function type, just add the
          // this pointer as first argument.
          assert(
            tpointee->tag_typ==LVREFERENCE &&
            tpointee->cons_typ.LVReference.kind->tag_pkind == PFUNCTIONPOINTER);
          // TODO: this should be a PStandardMethodPointer
          // or a PVirtualMethodPointer
          list* args =
            &tpointee->cons_typ.LVReference.kind->
               cons_pkind.PFunctionPointer.decl->parameter;
          *args = cons_container(arg_this,*args);
          tpointee->tag_typ = POINTER;
          return tpointee;
        }
        // pointed type is a standard datatype. We'll treat that as
        // a function from the class to the type.
        signature sig =
          signature_cons(
            qual_type_cons(NULL,tpointee),
            cons_container(arg_this,NULL),
            false);
        return typ_Pointer(pkind_PFunctionPointer(sig));
      };


    case clang::Type::ConstantArray:
      { assert(llvm::dyn_cast<const clang::ConstantArrayType>(type));
        const clang::ConstantArrayType*
          arrayType = static_cast<clang::ConstantArrayType const*>(type);
        clang::QualType subArrayType = arrayType->getElementType();
        list/*<specifier>*/ subspec = make_specifier_list(subArrayType);
        typ subtype = makePlainType(loc, subArrayType, declRegistration, isPOD);
        akind arrayKind =
          akind_cons(
            qual_type_cons(subspec, subtype),
            opt_some_container(
              makeIntLiteral(
                makeLocation(loc),
                IINT,
                (int64_t) arrayType->getSize().getLimitedValue(UINT64_MAX))));
        return typ_Array(arrayKind);
      };
    case clang::Type::IncompleteArray:
      { assert (llvm::dyn_cast<const clang::IncompleteArrayType>(type));
        const clang::IncompleteArrayType*
          arrayType = static_cast<clang::IncompleteArrayType const*>(type);
        clang::QualType subArrayType = arrayType->getElementType();
        list/*<specifier>*/subspec = make_specifier_list(subArrayType);
        typ subtype = makePlainType(loc, subArrayType, declRegistration, isPOD);
        akind arrayKind =
          akind_cons(qual_type_cons(subspec,subtype),opt_none());
        return typ_Array(arrayKind);
      }
    case clang::Type::FunctionProto:
      { assert(llvm::dyn_cast<const clang::FunctionProtoType>(type));
        const clang::FunctionProtoType* functionType =
          static_cast<clang::FunctionProtoType const*>(type);
        bool is_variadic = functionType->isVariadic();
        clang::QualType functionResultType = functionType->getReturnType();
        qual_type resultType =
          qual_type_cons(
            make_specifier_list(functionResultType),
            makePlainType(
              loc,
              functionResultType,
              declRegistration? declRegistration->getNameRegistration() : NULL,
              isPOD));
        clang::FunctionProtoType::param_type_iterator argEnd =
          functionType->param_type_end();
        list /* parameter */ parameters = NULL;
        ForwardReferenceList forwardParameters(parameters);
        for (
             clang::FunctionProtoType::param_type_iterator argIter =
             functionType->param_type_begin();
            argIter < argEnd; ++argIter) {
          qual_type argType =
            qual_type_cons(
              make_specifier_list(*argIter),
              makePlainType(
                loc,
                *argIter,
                declRegistration?declRegistration->getNameRegistration():NULL,
                isPOD));
          forwardParameters.insertContainer(argType);
        };
        return
          typ_LVReference(
           pkind_PFunctionPointer(
            signature_cons(resultType, parameters, is_variadic)));
      };
    case clang::Type::FunctionNoProto:
      std::cerr << "Unsupported K&R Declaration Function Type:"
          << qt.getAsString ()
          << "\nAborting\n";
      exit(2);
    case clang::Type::Record:
      { assert(llvm::dyn_cast<const clang::RecordType>(type));
        const clang::RecordType*
          recordType = static_cast<clang::RecordType const*>(type);
        const clang::RecordDecl* record = recordType->getDecl();
        if (is_lambda(record))
          return make_lambda_type(loc,record,declRegistration);
        if (declRegistration && declRegistration->doesRegisterDecl())
          declRegistration->registerDecl(record);
        clang::RecordDecl::TagKind tagKind = record->getTagKind();
        tkind templateParameters = NULL;
        const char* dec_name = get_aggregate_name(record, &templateParameters);
        const clang::DeclContext* ctx = record->getDeclContext();
        qualified_name name;
        if (!isExternCContext(ctx))
          name = makeQualifiedName(ctx,dec_name,record);
        else
          name = qualified_name_cons(NULL, dec_name);
        switch (tagKind) {
          case clang::TTK_Struct:
          case clang::TTK_Class:
            return typ_Struct(name, templateParameters);
          case clang::TTK_Union:
            return typ_Union(name, templateParameters);
          default:
            if (templateParameters)
              free_tkind(templateParameters);
            std::cerr << "Unsupported Record Type:"
                << qt.getAsString ()
                << "\nAborting\n";
            exit(2);
        };
      };
    case clang::Type::Enum:
      { assert(llvm::dyn_cast<const clang::EnumType>(type));
        const clang::EnumType*
          enumType = static_cast<clang::EnumType const*>(type);
        if (declRegistration && declRegistration->doesRegisterDecl())
          declRegistration->registerDecl(enumType->getDecl());
        qualified_name name;
        if (!isPOD || !Clang_utils::isExternCContext(enumType->getDecl()))
          name = makeQualifiedName(*enumType->getDecl());
        else
          name = qualified_name_cons(NULL,
            copy_string(enumType->getDecl()->getName().str()));
        return typ_Enum(ekind_cons(name));
      };
    case clang::Type::Auto: {
        assert(llvm::dyn_cast<const clang::AutoType>(type));
        const clang::AutoType* autotype =
           static_cast<clang::AutoType const*>(type);
        if (autotype->isDeduced()) {
          return
            makePlainType(
              loc,
              autotype->getDeducedType(),
              declRegistration,
              isPOD);
        } else { 
          unsupported_kind = "unresolved auto type"; break; 
        }
    }
    case clang::Type::SubstTemplateTypeParm:
      { assert(llvm::dyn_cast<const clang::SubstTemplateTypeParmType>(type));
        const clang::SubstTemplateTypeParmType* replacementType
            = static_cast<clang::SubstTemplateTypeParmType const*>(type);
        assert(!isPOD);
        return
          makePlainType(
            loc,
            replacementType->getReplacementType(),
            declRegistration, false);
      };
    case clang::Type::TemplateSpecialization:
      { const clang::TemplateSpecializationType* sp_type =
          llvm::dyn_cast<clang::TemplateSpecializationType const>(type);
        assert(sp_type && !isPOD);
        if (sp_type->isSugared())
          return
            makePlainType(loc, sp_type->desugar(), declRegistration, isPOD);
        else if (sp_type->isTypeAlias())
          // template alias using 'using' directive
          return
            makePlainType(loc,sp_type->getAliasedType(),declRegistration,isPOD);
        else {
          unsupported_kind = "uninstantiated template specialization";
          break;
        }
      }
    case clang::Type::Typedef:
      { assert(llvm::dyn_cast<const clang::TypedefType>(type));
        const clang::TypedefType* replacementType =
            static_cast<clang::TypedefType const*>(type);
        if (declRegistration && declRegistration->doesRegisterDecl())
          declRegistration->registerDecl(replacementType->getDecl());
        clang::Decl::Kind parentKind = replacementType->getDecl()
          ->getDeclContext()->getDeclKind();
        if (parentKind >= clang::Decl::firstFunction
            && parentKind <= clang::Decl::lastFunction)
          return
            makePlainType(
              loc,
              replacementType->getDecl()->getUnderlyingType(),
              declRegistration,
              isPOD);
        qualified_name name;
        if (!isPOD) {
          name = makeQualifiedName(*replacementType->getDecl(), true);
          if (name == NULL) {
            // sometimes clang does not specialize intermediate templates
            return
              makePlainType(
                loc,
                replacementType->getDecl()->getUnderlyingType(),
                declRegistration,
                isPOD);
          };
        }
        else
          name = qualified_name_cons(NULL, copy_string(
              replacementType->getDecl()->getName().str()));
        return typ_Named(name, isExternCContext(
            replacementType->getDecl()->getDeclContext()));
      };
    case clang::Type::Decayed:
    case clang::Type::Adjusted:
      { assert(llvm::dyn_cast<const clang::AdjustedType>(type));
        const clang::AdjustedType* adjustedType =
           static_cast<clang::AdjustedType const*>(type);
        // Note that we do not use the adjusted type because of some mangling
        //   problems. Frama-C know how to translate the original type into
        //   the adjusted type.
        return
          makePlainType(
            loc,adjustedType->getOriginalType(), declRegistration, isPOD);
      };

    case clang::Type::Paren:
      { assert(llvm::dyn_cast<const clang::ParenType>(type));
        const clang::ParenType* parentype =
            static_cast<clang::ParenType const*>(type);
        return
          makePlainType(
            loc,parentype->getInnerType(), declRegistration, isPOD);
      };
    case clang::Type::Elaborated: {
        assert(llvm::dyn_cast<const clang::ElaboratedType>(type));
        const clang::ElaboratedType* elaborated =
           static_cast<clang::ElaboratedType const*>(type);
        if (elaborated->isSugared()) {
           return
             makePlainType(loc, elaborated->desugar(), declRegistration, isPOD);
        } else {
           unsupported_kind="unresolved elaborated type";
           break;
        }
    }
    case clang::Type::Decltype:
      { assert(llvm::dyn_cast<const clang::DecltypeType>(type));
        const clang::DecltypeType* decltypeType =
           static_cast<clang::DecltypeType const*>(type);
        if (decltypeType->isSugared()) {
           return
             makePlainType(
               loc, decltypeType->desugar(), declRegistration, isPOD);
        } else {
           unsupported_kind="unresolved decltype type";
           break;
        }
      }
    case clang::Type::TypeOfExpr:
      { const clang::TypeOfExprType* t =
          static_cast<clang::TypeOfExprType const*>(type);
        return makePlainType(loc,t->desugar(), declRegistration, isPOD);
      }

    case clang::Type::TypeOf:
      { const clang::TypeOfType* t =
          static_cast<clang::TypeOfType const*>(type);
        return makePlainType(loc,t->desugar(), declRegistration, isPOD);
      }

    case clang::Type::Attributed: 
        unsupported_kind = "attributed type:"; break;
    case clang::Type::Atomic: unsupported_kind = "atomic"; break;
    case clang::Type::VariableArray:
      { assert (llvm::dyn_cast<const clang::VariableArrayType>(type));
        const clang::VariableArrayType*
          arrayType = static_cast<clang::VariableArrayType const*>(type);
        clang::QualType subArrayType = arrayType->getElementType();
        list/*<specifier>*/subspec = make_specifier_list(subArrayType);
        typ subtype = makePlainType(loc, subArrayType, declRegistration, isPOD);
        akind arrayKind =
          akind_cons(
            qual_type_cons(subspec,subtype),
            opt_some_container(
              _caller->makeLocExpression(arrayType->getSizeExpr())));
        return typ_Array(arrayKind);
      }
    case clang::Type::Vector:
      { assert (llvm::dyn_cast<const clang::VectorType>(type));
        const clang::VectorType*
          arrayType = static_cast<clang::VectorType const*>(type);
        clang::QualType subArrayType = arrayType->getElementType();
        list/*<specifier>*/subspec = make_specifier_list(subArrayType);
        typ subtype = makePlainType(loc, subArrayType, declRegistration, isPOD);
        akind arrayKind =
          akind_cons(
            qual_type_cons(subspec,subtype),
            opt_some_container(
              expression_cons(makeLocation(loc),
                exp_node_Constant(compilation_constant_IntCst(
                  IINT,ICLITERAL,arrayType->getNumElements())))));
        return typ_Array(arrayKind);
      }
    case clang::Type::BlockPointer:
        unsupported_kind = "block pointer"; break;
    case clang::Type::Complex:
        unsupported_kind = "complex"; break;
    case clang::Type::TemplateTypeParm:
        unsupported_kind = "template parameter"; break;
    case clang::Type::SubstTemplateTypeParmPack:
        unsupported_kind = "template parameter instance packed"; break;
    default: break;
  }
  // all successful cases have already returned.
  if (unsupported_kind.length() == 0) {
     std::stringstream buf;
     buf << "unknown kind (" << type->getTypeClass() << ")";
     unsupported_kind = buf.str();
  };
  std::cerr
    << loc_as_string(loc)
    << ": Unsupported Type (" << unsupported_kind << "):"
    << qt.getAsString ()
    << "\nAborting\n";
  exit(2);
}

ikind Clang_utils::makePlainIntConstantType(const clang::Type* type) const {
  switch(type->getTypeClass()) {
    case clang::Type::Builtin:
      switch(static_cast<const clang::BuiltinType*>(type)->getKind()) {
        case clang::BuiltinType::Bool: return IBOOL;
        case clang::BuiltinType::Char_U:
          return ICHAR_U; /* char = unsigned char */
        case clang::BuiltinType::Char_S:
          return ICHAR_S; /* char = signed char */
        case clang::BuiltinType::WChar_U:
          return IWCHAR_U; /* wchar_t = unsigned */
        case clang::BuiltinType::WChar_S:
          return IWCHAR_S; /* wchar_t = signed */
        case clang::BuiltinType::UChar: return IUCHAR;
        case clang::BuiltinType::SChar: return ISCHAR;
        case clang::BuiltinType::Char16: return ICHAR16;
        case clang::BuiltinType::Char32: return ICHAR32;
        case clang::BuiltinType::Short: return ISHORT;
        case clang::BuiltinType::UShort: return IUSHORT;
        case clang::BuiltinType::Int: return IINT;
        case clang::BuiltinType::UInt: return IUINT;
        case clang::BuiltinType::Long: return ILONG;
        case clang::BuiltinType::ULong: return IULONG;
        case clang::BuiltinType::Int128: return ILONG;
        case clang::BuiltinType::UInt128: return IULONG;
        case clang::BuiltinType::LongLong: return ILONGLONG;
        case clang::BuiltinType::ULongLong: return IULONGLONG;
        case clang::BuiltinType::Void:
        case clang::BuiltinType::Float:
        case clang::BuiltinType::Double:
        case clang::BuiltinType::LongDouble:
        default:
          std::cerr << "Not an integral Builtin-type: "
            << static_cast<const clang::BuiltinType*>(type)->
                 getName(_context->getPrintingPolicy()).str()
            << "\nAborting\n";
          //TODO: raise exception and try to continue with rest of file.
          exit(2);
      }
    case clang::Type::Enum: {
        const clang::EnumType* enumType =
          llvm::dyn_cast<const clang::EnumType>(type);
        clang::QualType integerType = enumType->getDecl()->getIntegerType();
        return makeIntConstantType(integerType.getTypePtr());
    };
    default: {
      clang::QualType qt(type, 0U);
      std::cerr << "Unsupported Type:" << qt.getAsString () << "\nAborting\n";
      exit(2);
    };
  }
}

fkind Clang_utils::makeFloatConstantType(clang::BuiltinType const* type)
  const {
  switch(type->getKind()) {
    case clang::BuiltinType::Float: return FFLOAT;
    case clang::BuiltinType::Double: return FDOUBLE;
    case clang::BuiltinType::LongDouble: return FLONGDOUBLE;
    default: {
      std::cerr
        << "Expected a floating-point type, got "
        << type->getName(_context->getPrintingPolicy()).str()
        << "\nAborting\n";
      exit(2);
    }
  }
}

template <typename T, class Op>
T Clang_utils::makeSpecificType(const Op* op, const clang::Type* type) const {
  switch(type->getTypeClass()) {
    case clang::Type::Enum: {
      const clang::EnumType* et = llvm::dyn_cast<const clang::EnumType>(type);
      assert(et);
      return
        makeSpecificType<T,Op>(op,et->getDecl()->getIntegerType().getTypePtr());
    }
    case clang::Type::Auto:
      { assert(llvm::dyn_cast<const clang::AutoType>(type));
        const clang::AutoType*
          autotype = static_cast<clang::AutoType const*>(type);
        return
          autotype->isDeduced()
          ? makeSpecificType<T,Op>(op, autotype->getDeducedType().getTypePtr())
          : op->null;
      }
    case clang::Type::SubstTemplateTypeParm:
      { assert(llvm::dyn_cast<const clang::SubstTemplateTypeParmType>(type));
        const clang::SubstTemplateTypeParmType* replacementType
          = static_cast<clang::SubstTemplateTypeParmType const*>(type);
        return
          makeSpecificType<T,Op>(
            op, replacementType->getReplacementType().getTypePtr());
      };
    case clang::Type::TemplateSpecialization:
      { const clang::TemplateSpecializationType* sp_type =
          llvm::dyn_cast<const clang::TemplateSpecializationType>(type);
        assert(sp_type);
        clang::QualType t;
        if (sp_type->isSugared()) t = sp_type->desugar();
        else if (sp_type->isTypeAlias()) t = sp_type->getAliasedType();
        else return op->null;
        return makeSpecificType<T,Op>(op,t.getTypePtr());
      }
    case clang::Type::Typedef:
      { assert(llvm::dyn_cast<const clang::TypedefType>(type));
        const clang::TypedefType* replacementType =
           static_cast<clang::TypedefType const*>(type);
        return
          replacementType->isSugared()
          ? makeSpecificType<T,Op>(op, replacementType->desugar().getTypePtr())
          : op->null;
      };
    case clang::Type::Elaborated:
      { assert(llvm::dyn_cast<const clang::ElaboratedType>(type));
        const clang::ElaboratedType* elaborated =
            static_cast<clang::ElaboratedType const*>(type);
        return
          elaborated->isSugared()
          ? makeSpecificType<T,Op>(op, elaborated->desugar().getTypePtr())
          : op->null;
      }
    default: return (*op)(type);
  }
  return op->null;
}

bool
Clang_utils::isIntegralType(const clang::Type* type) const
{ liftBuiltinType<bool,&Clang_utils::isIntegralType> op(this, false);
  return makeSpecificType<bool>(&op, type); }

typ
Clang_utils::makeArithmeticType(const clang::Type* type) const
  {
    liftBuiltinType<typ,&Clang_utils::makeBuiltinTypeNoLoc> op(this, NULL);
    return makeSpecificType<typ>(&op,type);
  }

bool
Clang_utils::isSignedType(const clang::Type* type) const
  { liftBuiltinType<bool,&Clang_utils::isSignedType> op(this, false); 
      return makeSpecificType<bool>(&op,type); }

bool
Clang_utils::isArithmeticType(const clang::Type* type) const
  { liftBuiltinType<bool,&Clang_utils::isArithmeticType> op(this, false);
    return makeSpecificType<bool>(&op, type); }

bool
Clang_utils::isFloatingType(const clang::Type* type) const
  { liftBuiltinType<bool,&Clang_utils::isFloatingType> op(this, false);
    return makeSpecificType<bool>(&op, type); }

bool
Clang_utils::isPlainPointer(const clang::Type* type) const {
  switch(type->getTypeClass()) {
    case clang::Type::Pointer:
    case clang::Type::MemberPointer:
      return true;
    default: return false;
  }
}

bool Clang_utils::isPointerType(const clang::Type* type) const {
  liftType<bool,&Clang_utils::isPlainPointer> op(this, false);
  return makeSpecificType<bool>(&op,type);
}

ikind Clang_utils::makeIntConstantType(const clang::Type* type) const {
  liftType<ikind,&Clang_utils::makePlainIntConstantType> op(this,IINT);
  return makeSpecificType<ikind>(&op, type);
}

fkind Clang_utils::makeFloatConstantType(const clang::Type* type) const {
  liftBuiltinType<fkind,&Clang_utils::makeFloatConstantType> op(this,FDOUBLE);
  return makeSpecificType<fkind>(&op,type);
}

bool
Clang_utils::isPlainReference(const clang::Type* type) const {
  switch(type->getTypeClass()) {
    case clang::Type::LValueReference:
    case clang::Type::RValueReference:
      return true;
    default: return false;
  }
}

bool
Clang_utils::isReferenceType(const clang::Type* type) const {
  liftType<bool,&Clang_utils::isPlainReference> op(this,false);
  return makeSpecificType<bool>(&op, type);
}

bool
Clang_utils::isPlainArray(const clang::Type* type) const {
  switch(type->getTypeClass()) {
    case clang::Type::ConstantArray:
    case clang::Type::IncompleteArray:
    case clang::Type::VariableArray:
    case clang::Type::DependentSizedArray:
      return true;
    default:
      return false;
  }
}

bool
Clang_utils::isArrayType(const clang::Type* type) const {
  liftType<bool,&Clang_utils::isPlainReference> op(this, false);
  return makeSpecificType<bool>(&op, type);
}

bool
Clang_utils::lvalHasRefType(const clang::Expr* expr) const {
  if (!expr->isLValue()) return false;
  const clang::ValueDecl* decl = NULL;
  switch (expr->getStmtClass()) {
    case clang::Stmt::DeclRefExprClass: {
      const auto dexpr = llvm::dyn_cast<const clang::DeclRefExpr>(expr);
      if (dexpr) decl = dexpr->getDecl();
      break;
    }
    case clang::Stmt::MemberExprClass: {
      const auto mexpr = llvm::dyn_cast<const clang::MemberExpr>(expr);
      if (mexpr) decl = mexpr->getMemberDecl();
      break;
    }
      // TODO: maybe there are other cases.
      // Note however, that there can't be any array of or pointer to
      // references, which slightly limits the possibilities.
    default: return false;
  }
  if (decl) {
    return isReferenceType(decl->getType().getTypePtr());
  } else return false;
}

bool Clang_utils::isFunctionReferenceType(typ type) const {
  switch (type->tag_typ) {
    case LVREFERENCE:
      return type->cons_typ.LVReference.kind->tag_pkind != PDATAPOINTER;
    case RVREFERENCE:
      return type->cons_typ.RVReference.kind->tag_pkind != PDATAPOINTER;
    default: return false;
  }
}

bool Clang_utils::isObjectReferenceType(typ type) const {
  switch (type->tag_typ) {
    case LVREFERENCE:
      return type->cons_typ.LVReference.kind->tag_pkind == PDATAPOINTER;
    case RVREFERENCE:
      return type->cons_typ.RVReference.kind->tag_pkind == PDATAPOINTER;
    default: return false;
  }
}

qual_type Clang_utils::getObjectReferenceType(typ type) const {
  pkind k = NULL;
  switch (type->tag_typ) {
    case LVREFERENCE: k = type->cons_typ.LVReference.kind; break;
    case RVREFERENCE: k = type->cons_typ.RVReference.kind; break;
    default: return NULL;
  }
  if (k->tag_pkind != PDATAPOINTER) return NULL;
  return k->cons_pkind.PDataPointer.subtype;
}

const clang::ConstantArrayType*
Clang_utils::isConstantArrayType(const clang::Type* type) const {
  switch(type->getTypeClass()) {
    case clang::Type::ConstantArray:
      return static_cast<const clang::ConstantArrayType*>(type);
    case clang::Type::IncompleteArray:
    case clang::Type::VariableArray:
    case clang::Type::DependentSizedArray:
      return NULL;
    case clang::Type::Auto:
      { assert(llvm::dyn_cast<const clang::AutoType>(type));
        const clang::AutoType*
          autotype = static_cast<clang::AutoType const*>(type);
        return autotype->isDeduced()
            ? isConstantArrayType(autotype->getDeducedType().getTypePtr())
            : NULL;
      }
    case clang::Type::SubstTemplateTypeParm:
      { assert(llvm::dyn_cast<const clang::SubstTemplateTypeParmType>(type));
        const clang::SubstTemplateTypeParmType* replacementType
          = static_cast<clang::SubstTemplateTypeParmType const*>(type);
        return isConstantArrayType(replacementType->getReplacementType()
            .getTypePtr());
      };
    case clang::Type::TemplateSpecialization:
      { assert(llvm::dyn_cast<const clang::TemplateSpecializationType>(type));
        const clang::TemplateSpecializationType* sp_type =
           static_cast<clang::TemplateSpecializationType const*>(type);
        return sp_type->isSugared()
          ? isConstantArrayType(sp_type->desugar().getTypePtr())
          : NULL;
      }
    case clang::Type::Typedef:
      { assert(llvm::dyn_cast<const clang::TypedefType>(type));
        const clang::TypedefType* replacementType =
           static_cast<clang::TypedefType const*>(type);
        return replacementType->isSugared()
            ? isConstantArrayType(replacementType->desugar().getTypePtr())
            : NULL;
      };
    case clang::Type::Elaborated:
      { assert(llvm::dyn_cast<const clang::ElaboratedType>(type));
        const clang::ElaboratedType* elaborated =
            static_cast<clang::ElaboratedType const*>(type);
        return elaborated->isSugared()
          ? isConstantArrayType(elaborated->desugar().getTypePtr())
          : NULL;
      }
    default: break;
  }
  return NULL;
}

logic_type
Clang_utils::makePointedType(
  clang::SourceLocation const& loc, clang::Type const* type) const {
  switch(type->getTypeClass()) {
    case clang::Type::Pointer:
      { assert(llvm::dyn_cast<const clang::PointerType>(type));
        const clang::PointerType*
          pointerType = static_cast<clang::PointerType const*>(type);
        clang::QualType subPointerType = pointerType->getPointeeType();
        return makeLogicType(loc, subPointerType.getTypePtr());
      };
    case clang::Type::MemberPointer:
      { assert(llvm::dyn_cast<const clang::MemberPointerType>(type));
        const clang::MemberPointerType*
          pointerType = static_cast<clang::MemberPointerType const*>(type);
        clang::QualType subPointerType = pointerType->getPointeeType();
        return makeLogicType(loc, subPointerType.getTypePtr());
      };
    case clang::Type::Auto:
      { assert(llvm::dyn_cast<const clang::AutoType>(type));
        const clang::AutoType*
          autotype = static_cast<clang::AutoType const*>(type);
        assert(autotype->isDeduced());
        return makePointedType(loc, autotype->getDeducedType().getTypePtr());
      }
    case clang::Type::SubstTemplateTypeParm:
      { assert(llvm::dyn_cast<const clang::SubstTemplateTypeParmType>(type));
        const clang::SubstTemplateTypeParmType* replacementType
          = static_cast<clang::SubstTemplateTypeParmType const*>(type);
        return
          makePointedType(loc, replacementType->getReplacementType().getTypePtr());
      };
    case clang::Type::TemplateSpecialization:
      { assert(llvm::dyn_cast<const clang::TemplateSpecializationType>(type));
        const clang::TemplateSpecializationType* sp_type =
           static_cast<clang::TemplateSpecializationType const*>(type);
        assert(sp_type->isSugared());
        return makePointedType(loc, sp_type->desugar().getTypePtr());
      }
    case clang::Type::Typedef:
      { assert(llvm::dyn_cast<const clang::TypedefType>(type));
        const clang::TypedefType* replacementType =
           static_cast<clang::TypedefType const*>(type);
        assert(replacementType->isSugared());
        return makePointedType(loc, replacementType->desugar().getTypePtr());
      };
    case clang::Type::Elaborated:
      { assert(llvm::dyn_cast<const clang::ElaboratedType>(type));
        const clang::ElaboratedType* elaborated =
            static_cast<clang::ElaboratedType const*>(type);
        assert(elaborated->isSugared());
        return makePointedType(loc, elaborated->desugar().getTypePtr());
      }
    default: break;
  }
  assert(false);
  return NULL;
}

logic_type
Clang_utils::makeReferencedType(
  clang::SourceLocation const& loc, clang::Type const* type) const {
  switch(type->getTypeClass()) {
    case clang::Type::LValueReference:
    case clang::Type::RValueReference:
      { assert(llvm::dyn_cast<const clang::ReferenceType>(type));
        const clang::ReferenceType*
          referenceType = static_cast<clang::ReferenceType const*>(type);
        clang::QualType subPointerType = referenceType->getPointeeType();
        return makeLogicType(loc, subPointerType.getTypePtr());
      };
    case clang::Type::MemberPointer:
      { assert(llvm::dyn_cast<const clang::MemberPointerType>(type));
        const clang::MemberPointerType*
          pointerType = static_cast<clang::MemberPointerType const*>(type);
        clang::QualType subPointerType = pointerType->getPointeeType();
        return makeLogicType(loc, subPointerType.getTypePtr());
      };
    case clang::Type::Auto:
      { assert(llvm::dyn_cast<const clang::AutoType>(type));
        const clang::AutoType*
          autotype = static_cast<clang::AutoType const*>(type);
        assert(autotype->isDeduced());
        return makeReferencedType(loc, autotype->getDeducedType().getTypePtr());
      }
    case clang::Type::SubstTemplateTypeParm:
      { assert(llvm::dyn_cast<const clang::SubstTemplateTypeParmType>(type));
        const clang::SubstTemplateTypeParmType* replacementType
          = static_cast<clang::SubstTemplateTypeParmType const*>(type);
        return
          makeReferencedType(loc, replacementType->getReplacementType().getTypePtr());
      };
    case clang::Type::TemplateSpecialization:
      { assert(llvm::dyn_cast<const clang::TemplateSpecializationType>(type));
        const clang::TemplateSpecializationType* sp_type =
           static_cast<clang::TemplateSpecializationType const*>(type);
        assert(sp_type->isSugared());
        return makeReferencedType(loc, sp_type->desugar().getTypePtr());
      }
    case clang::Type::Typedef:
      { assert(llvm::dyn_cast<const clang::TypedefType>(type));
        const clang::TypedefType* replacementType =
           static_cast<clang::TypedefType const*>(type);
        assert(replacementType->isSugared());
        return makeReferencedType(loc, replacementType->desugar().getTypePtr());
      };
    case clang::Type::Elaborated:
      { assert(llvm::dyn_cast<const clang::ElaboratedType>(type));
        const clang::ElaboratedType* elaborated =
            static_cast<clang::ElaboratedType const*>(type);
        assert(elaborated->isSugared());
        return makeReferencedType(loc, elaborated->desugar().getTypePtr());
      }
    default: break;
  }
  assert(false);
  return NULL;
}

logic_type
Clang_utils::makeElementArrayType(
  clang::SourceLocation const& loc, clang::Type const* type) const {
  switch(type->getTypeClass()) {
    case clang::Type::ConstantArray:
    case clang::Type::IncompleteArray:
    case clang::Type::VariableArray:
    case clang::Type::DependentSizedArray:
      { assert(llvm::dyn_cast<const clang::ArrayType>(type));
        const clang::ArrayType*
          arrayType = static_cast<clang::ArrayType const*>(type);
        clang::QualType subArrayType = arrayType->getElementType();
        return makeLogicType(loc, subArrayType.getTypePtr());
      };
    case clang::Type::Auto:
      { assert(llvm::dyn_cast<const clang::AutoType>(type));
        const clang::AutoType*
          autotype = static_cast<clang::AutoType const*>(type);
        assert(autotype->isDeduced());
        return makeElementArrayType(loc, autotype->getDeducedType().getTypePtr());
      }
    case clang::Type::SubstTemplateTypeParm:
      { assert(llvm::dyn_cast<const clang::SubstTemplateTypeParmType>(type));
        const clang::SubstTemplateTypeParmType* replacementType
          = static_cast<clang::SubstTemplateTypeParmType const*>(type);
        return
          makeElementArrayType(loc, replacementType->getReplacementType().getTypePtr());
      };
    case clang::Type::TemplateSpecialization:
      { assert(llvm::dyn_cast<const clang::TemplateSpecializationType>(type));
        const clang::TemplateSpecializationType* sp_type =
           static_cast<clang::TemplateSpecializationType const*>(type);
        assert(sp_type->isSugared());
        return makeElementArrayType(loc, sp_type->desugar().getTypePtr());
      }
    case clang::Type::Typedef:
      { assert(llvm::dyn_cast<const clang::TypedefType>(type));
        const clang::TypedefType* replacementType =
           static_cast<clang::TypedefType const*>(type);
        assert(replacementType->isSugared());
        return makeElementArrayType(loc, replacementType->desugar().getTypePtr());
      };
    case clang::Type::Elaborated:
      { assert(llvm::dyn_cast<const clang::ElaboratedType>(type));
        const clang::ElaboratedType* elaborated =
            static_cast<clang::ElaboratedType const*>(type);
        assert(elaborated->isSugared());
        return makeElementArrayType(loc, elaborated->desugar().getTypePtr());
      }
    default: break;
  }
  assert(false);
  return NULL;
}

qualified_name
Clang_utils::makeCompoundType(const clang::Type* type, tkind* templateKind)
    const {
  switch(type->getTypeClass()) {
    case clang::Type::Record:
      { assert(llvm::dyn_cast<const clang::RecordType>(type));
        const clang::RecordType*
          recordType = static_cast<clang::RecordType const*>(type);
        if (templateKind)
          *templateKind = makeTemplateKind(recordType->getDecl());
        return makeQualifiedName(*recordType->getDecl());
      }
    case clang::Type::LValueReference:
    case clang::Type::RValueReference:
      { assert(llvm::dyn_cast<const clang::ReferenceType>(type));
        const clang::ReferenceType*
          referenceType = static_cast<clang::ReferenceType const*>(type);
        return makeCompoundType(referenceType->getPointeeType().getTypePtr(),
          templateKind);
      }
    case clang::Type::Auto:
      { assert(llvm::dyn_cast<const clang::AutoType>(type));
        const clang::AutoType*
          autotype = static_cast<clang::AutoType const*>(type);
        return autotype->isDeduced()
            ? makeCompoundType(autotype->getDeducedType().getTypePtr(),
                templateKind)
            : NULL;
      }
    case clang::Type::SubstTemplateTypeParm:
      { assert(llvm::dyn_cast<const clang::SubstTemplateTypeParmType>(type));
        const clang::SubstTemplateTypeParmType* replacementType
          = static_cast<clang::SubstTemplateTypeParmType const*>(type);
        return makeCompoundType(replacementType->getReplacementType()
            .getTypePtr(), templateKind);
      };
    case clang::Type::TemplateSpecialization:
      { assert(llvm::dyn_cast<const clang::TemplateSpecializationType>(type));
        const clang::TemplateSpecializationType* sp_type =
           static_cast<clang::TemplateSpecializationType const*>(type);
        return sp_type->isSugared()
          ? makeCompoundType(sp_type->desugar().getTypePtr(), templateKind)
          : NULL;
      }
    case clang::Type::Typedef:
      { assert(llvm::dyn_cast<const clang::TypedefType>(type));
        const clang::TypedefType* replacementType =
           static_cast<clang::TypedefType const*>(type);
        return replacementType->isSugared()
            ? makeCompoundType(replacementType->desugar().getTypePtr(),
                templateKind)
            : NULL;
      };
    case clang::Type::Elaborated:
      { assert(llvm::dyn_cast<const clang::ElaboratedType>(type));
        const clang::ElaboratedType* elaborated =
            static_cast<clang::ElaboratedType const*>(type);
        return elaborated->isSugared()
          ? makeCompoundType(elaborated->desugar().getTypePtr(), templateKind)
          : NULL;
      }
    default: break;
  }
  return NULL;
}

bool
Clang_utils::retrieveTypeOfField(clang::Type const* type,
    const std::string& fieldName, term_offset& offset, logic_type& ltype,
    std::string& errorMessage, const clang::ASTContext* clangAST,
    clang::Sema* clangSema, const clang::SourceLocation& location,
    const RTTITable& rttiTable) const
{ switch(type->getTypeClass()) {
    case clang::Type::LValueReference:
      { assert(llvm::dyn_cast<const clang::LValueReferenceType>(type));
        const clang::PointerType*
          referenceType = static_cast<clang::PointerType const*>(type);
        clang::QualType subReferenceType = referenceType->getPointeeType();
        return retrieveTypeOfField(subReferenceType.getTypePtr(),
            fieldName, offset, ltype, errorMessage, clangAST, clangSema,
            location, rttiTable);
      };
    case clang::Type::Record:
      { assert(llvm::dyn_cast<const clang::RecordType>(type));
        const clang::RecordType*
          recordType = static_cast<clang::RecordType const*>(type);
        const clang::RecordDecl* decl = recordType->getDecl();
        if (!decl) {
          // all successful cases have already returned.
          errorMessage = "";
          errorMessage.append("Unsupported Field Access to ")
                      .append(fieldName)
                      .append(" in ")
                      .append(clang::QualType(type, 0).getAsString());
          return false;
        };

        clang::RecordDecl::field_iterator fieldEnd = decl->field_end();
        for (clang::RecordDecl::field_iterator fieldIter = decl->field_begin();
            fieldIter != fieldEnd; ++fieldIter) {
          if (fieldIter->getDeclName().getAsString() == fieldName) {
            offset = term_offset_TField(strdup(fieldName.c_str()),
                term_offset_TNoOffset());
            ltype =
              makeLogicType(fieldIter->getLocation(), fieldIter->getType().getTypePtr());
            return true;
          };
        };

        clang::LookupResult R(*clangSema, &clangAST->Idents.get(fieldName),
            location, clang::Sema::LookupMemberName);
        const clang::NamedDecl* found = NULL;
        if (!clangSema->LookupQualifiedName(R, const_cast<clang::RecordDecl*>(
            decl)))
          break;
        if (!found && !R.isSingleResult())
          break;
        if (!found)
          found = R.getFoundDecl();
        clang::Decl::Kind kind = found->getKind();
        if (kind == clang::Decl::Field) {
          const clang::FieldDecl* field = static_cast<const clang::FieldDecl*> (found);
          const clang::RecordDecl* parent = field->getParent();
          const clang::CXXRecordDecl
            *derived = llvm::dyn_cast<clang::CXXRecordDecl>(decl),
            *base = llvm::dyn_cast<clang::CXXRecordDecl>(parent);
          if (derived && base) {
            RTTITable::InheritancePath inheritancePath;
            RTTITable::VirtualInheritancePath virtualInheritancePath;
            rttiTable.retrieveInheritancePathBetween(derived, base,
                inheritancePath, virtualInheritancePath, *this);
            int sizeInheritancePath = (int) inheritancePath.size()-1;
            assert(sizeInheritancePath >= 0 || virtualInheritancePath.first);
            tkind base_tkind = makeTemplateKind(base);
            offset = term_offset_TBase(
              makeQualifiedName(*base), base_tkind,
              term_offset_TField(
                strdup(fieldName.c_str()), term_offset_TNoOffset()));
            if (virtualInheritancePath.first) {
              const clang::CXXRecordDecl
                *localDerived = virtualInheritancePath.first;
              tkind local_tkind = makeTemplateKind(localDerived);
              offset =
                term_offset_TVirtualBase(
                  makeQualifiedName(*localDerived), local_tkind, offset);
            };
            for (int index = 0; index < sizeInheritancePath; ++index) {
              const clang::CXXRecordDecl
                *localDerived = inheritancePath[index].first;
              tkind local_tkind = makeTemplateKind(localDerived);
              offset =
                term_offset_TBase(
                  makeQualifiedName(*localDerived), local_tkind, offset);
            };
            ltype =
              makeLogicType(field->getLocation(), field->getType().getTypePtr());
            return true;
          };
        }
        else if (kind >= clang::Decl::firstVar && kind <= clang::Decl::lastVar)
        { // maybe a static field
          // [TODO]
        };
      }
      break;
    case clang::Type::Auto:
      { assert(llvm::dyn_cast<const clang::AutoType>(type));
        const clang::AutoType*
          autotype = static_cast<clang::AutoType const*>(type);
        if (autotype->isDeduced())
          return retrieveTypeOfField(autotype->getDeducedType().getTypePtr(),
              fieldName, offset, ltype, errorMessage, clangAST, clangSema,
              location, rttiTable);
      };
      break;
    case clang::Type::SubstTemplateTypeParm:
      { assert(llvm::dyn_cast<const clang::SubstTemplateTypeParmType>(type));
        const clang::SubstTemplateTypeParmType* replacementType
            = static_cast<clang::SubstTemplateTypeParmType const*>(type);
        return retrieveTypeOfField(replacementType->getReplacementType()
            .getTypePtr(), fieldName, offset, ltype, errorMessage,
            clangAST, clangSema, location, rttiTable);
      };
    case clang::Type::TemplateSpecialization:
      { assert(llvm::dyn_cast<const clang::TemplateSpecializationType>(type));
        const clang::TemplateSpecializationType*
          sp_type = static_cast<clang::TemplateSpecializationType const*>(type);
        if (sp_type->isSugared())
          return retrieveTypeOfField(sp_type->desugar().getTypePtr(),
              fieldName, offset, ltype, errorMessage, clangAST, clangSema,
              location, rttiTable);
        break;
      }
    case clang::Type::Typedef:
      { assert(llvm::dyn_cast<const clang::TypedefType>(type));
        const clang::TypedefType* replacementType =
           static_cast<clang::TypedefType const*>(type);
        if (replacementType->isSugared())
          return retrieveTypeOfField(replacementType->desugar().getTypePtr(),
              fieldName, offset, ltype, errorMessage, clangAST, clangSema,
              location, rttiTable);
      };
      break;
    case clang::Type::Elaborated:
      { assert(llvm::dyn_cast<const clang::ElaboratedType>(type));
        const clang::ElaboratedType* elaborated =
           static_cast<clang::ElaboratedType const*>(type);
        if (elaborated->isSugared())
          return retrieveTypeOfField(elaborated->desugar().getTypePtr(),
              fieldName, offset, ltype, errorMessage, clangAST, clangSema,
              location, rttiTable);
        break;
      }
    default: break;
  }
  // all successful cases have already returned.
  errorMessage = "";
  errorMessage.append("Unsupported Field Access to ")
              .append(fieldName).append(" in ")
              .append(clang::QualType(type, 0).getAsString());
  return false;
}

logic_type
Clang_utils::makeLogicType(
  const clang::SourceLocation& loc, const clang::Type* type) const {
  std::string unsupported_kind;
  switch(type->getTypeClass()) {
    case clang::Type::Builtin:
      { assert(llvm::dyn_cast<const clang::BuiltinType>(type));
        return
          makeBuiltinLogicType(
            loc, static_cast<clang::BuiltinType const*>(type));
      };
    case clang::Type::Pointer:
      { assert(llvm::dyn_cast<const clang::PointerType>(type));
        const clang::PointerType*
          pointerType = static_cast<clang::PointerType const*>(type);
        clang::QualType subPointerType = pointerType->getPointeeType();
        logic_type subtype = makeLogicType(loc, subPointerType.getTypePtr());
        return logic_type_Lpointer(subtype);
      };
    case clang::Type::LValueReference:
      { 
        const clang::LValueReferenceType* referenceType =
          llvm::dyn_cast<const clang::LValueReferenceType>(type);
        assert(referenceType);
        clang::QualType subReferenceType = referenceType->getPointeeType();
        logic_type subtype = makeLogicType(loc, subReferenceType.getTypePtr());
        return logic_type_Lreference(subtype);
      };
    case clang::Type::RValueReference:
      { const clang::RValueReferenceType* referenceType =
          llvm::dyn_cast<const clang::RValueReferenceType>(type);
        assert(referenceType);
        clang::QualType subReferenceType = referenceType->getPointeeType();
        logic_type subtype = makeLogicType(loc, subReferenceType.getTypePtr());
        return logic_type_Lreference(subtype);
      };
    case clang::Type::MemberPointer:
      // see FunctionProto for the method pointers
      std::cerr << "Unsupported Member Type:"
          <<  clang::QualType(type, 0).getAsString ()
          << "\nAborting\n";
      exit(2);
    case clang::Type::ConstantArray:
      { assert(llvm::dyn_cast<const clang::ConstantArrayType>(type));
        const clang::ConstantArrayType*
          arrayType = static_cast<clang::ConstantArrayType const*>(type);
        clang::QualType subArrayType = arrayType->getElementType();
        logic_type subtype = makeLogicType(loc, subArrayType.getTypePtr());
        std::ostringstream buf;
        buf << arrayType->getSize().getLimitedValue(UINT64_MAX);
        logic_constant dimension = logic_constant_LCInt(buf.str().c_str());
        return logic_type_Larray(subtype, opt_some_container(dimension));
      };
    case clang::Type::IncompleteArray:
      { assert(llvm::dyn_cast<const clang::IncompleteArrayType>(type));
        const clang::IncompleteArrayType*
          arrayType = static_cast<clang::IncompleteArrayType const*>(type);
        clang::QualType subArrayType = arrayType->getElementType();
        logic_type subtype = makeLogicType(loc, subArrayType.getTypePtr());
        return logic_type_Larray(subtype, opt_none());
      }
    case clang::Type::FunctionProto:
      {
        assert (llvm::dyn_cast<const clang::FunctionProtoType>(type));
        const clang::FunctionProtoType* funType =
          static_cast<clang::FunctionProtoType const*>(type);
        clang::QualType ret = funType->getReturnType();
        llvm::ArrayRef<clang::QualType> args = funType->getParamTypes();
        logic_type cret = makeLogicType(loc, ret.getTypePtr());
        ForwardList cargs;
        for(llvm::ArrayRef<clang::QualType>::iterator it = args.begin();
            it != args.end(); it++) {
          cargs.insertContainer(makeLogicType(loc, it->getTypePtr()));
        }
        return logic_type_Larrow(cargs.getFront(),cret);
      }
    case clang::Type::FunctionNoProto:
      std::cerr << "Unsupported K&R Declaration Function Type:"
          << clang::QualType(type, 0).getAsString ()
          << "\nAborting\n";
      exit(2);
    case clang::Type::Record:
      { assert(llvm::dyn_cast<const clang::RecordType>(type));
        const clang::RecordType*
          recordType = static_cast<clang::RecordType const*>(type);
        const clang::RecordDecl* record = recordType->getDecl();
        clang::RecordDecl::TagKind tagKind = record->getTagKind();
        tkind templateParameters = NULL;
        const char* dec_name = get_aggregate_name(record, &templateParameters);
        const clang::DeclContext* ctx = record->getDeclContext();
        qualified_name name = makeQualifiedName(ctx,dec_name,record);
        switch (tagKind) {
          case clang::TTK_Struct:
          case clang::TTK_Class:
            return logic_type_Lstruct(name, templateParameters);
          case clang::TTK_Union:
            return logic_type_Lunion(name, templateParameters);
          default:
            if (templateParameters)
              delete templateParameters;
            std::cerr << "Unsupported Record Type:"
                << clang::QualType(type, 0).getAsString ()
                << "\nAborting\n";
            exit(2);
        };
      };
    case clang::Type::Enum:
      { assert(llvm::dyn_cast<const clang::EnumType>(type));
        const clang::EnumType*
          enumType = static_cast<clang::EnumType const*>(type);
        qualified_name name = makeQualifiedName(*enumType->getDecl());
        return logic_type_Lenum(name);
      };
    case clang::Type::Auto: {
        assert(llvm::dyn_cast<const clang::AutoType>(type));
        const clang::AutoType* autotype =
           static_cast<clang::AutoType const*>(type);
        if (autotype->isDeduced()) {
          return makeLogicType(loc, autotype->getDeducedType().getTypePtr());
        } else { 
           unsupported_kind = "unresolved auto type"; break; 
        }
    }
    case clang::Type::SubstTemplateTypeParm:
      { assert(llvm::dyn_cast<const clang::SubstTemplateTypeParmType>(type));
        const clang::SubstTemplateTypeParmType* replacementType
            = static_cast<clang::SubstTemplateTypeParmType const*>(type);
        return
          makeLogicType(loc, replacementType->getReplacementType().getTypePtr());
      };
    case clang::Type::TemplateSpecialization:
      { assert(llvm::dyn_cast<const clang::TemplateSpecializationType>(type));
        const clang::TemplateSpecializationType* sp_type =
           static_cast<clang::TemplateSpecializationType const*>(type);
        if (sp_type->isSugared()) {
          return makeLogicType(loc, sp_type->desugar().getTypePtr());
        }
        else {
          unsupported_kind = "uninstantiated template specialization";
          break;
        }
      }
    case clang::Type::Typedef:
      { assert(llvm::dyn_cast<const clang::TypedefType>(type));
        const clang::TypedefType* replacementType =
          static_cast<clang::TypedefType const*>(type);
        const clang::NamedDecl * decl = replacementType->getDecl();
        qualified_name name = makeQualifiedName(*decl);
        bool is_extern_c=Clang_utils::isExternCContext(decl->getDeclContext());
        return logic_type_LCnamed(name,is_extern_c);
      };
    case clang::Type::Elaborated:
      { assert(llvm::dyn_cast<const clang::ElaboratedType>(type));
        const clang::ElaboratedType* elaborated =
          static_cast<clang::ElaboratedType const*>(type);
        if (elaborated->isSugared()) {
          return makeLogicType(loc, elaborated->desugar().getTypePtr());
        }
        else {
          unsupported_kind="unresolved elaborated type";
          break;
        }
      }
    case clang::Type::TemplateTypeParm:
      { assert(llvm::dyn_cast<const clang::TemplateTypeParmType>(type));
        const clang::TemplateTypeParmType* parameterType =
          static_cast<clang::TemplateTypeParmType const*>(type);
        const clang::NamedDecl* templateParameter = NULL;
        const clang::TemplateArgument* result = findTemplateArgument(
          parameterType->getDecl()->getNameAsString(), templateParameter);
        return makeLogicType(loc, result->getAsType().getTypePtr());
      };
    case clang::Type::Paren:
      {
        assert(llvm::dyn_cast<const clang::ParenType>(type));
        const clang::ParenType* par =
          static_cast<clang::ParenType const*>(type);
        return makeLogicType(loc, par->getInnerType().getTypePtr());
      }
    case clang::Type::Decayed:
    case clang::Type::Adjusted:
      { assert(llvm::dyn_cast<const clang::AdjustedType>(type));
        const clang::AdjustedType* adjustedType =
           static_cast<clang::AdjustedType const*>(type);
        // Note that we do not use the adjusted type because of some mangling
        //   problems. Frama-C know how to translate the original type into
        //   the adjusted type.
        return makeLogicType(loc,adjustedType->getOriginalType().getTypePtr());
      };
    case clang::Type::Attributed: 
        unsupported_kind = "attributed type:"; break;
    case clang::Type::Atomic: unsupported_kind = "atomic"; break;
    case clang::Type::VariableArray:
      { assert(llvm::dyn_cast<const clang::VariableArrayType>(type));
        const clang::VariableArrayType*
          arrayType = static_cast<clang::VariableArrayType const*>(type);
        clang::QualType subArrayType = arrayType->getElementType();
        logic_type subtype = makeLogicType(loc, subArrayType.getTypePtr());
        /*Size is ignored on purpose: variable arrays are not needed in logic.
        */
        return logic_type_Larray(subtype, opt_none());
      };
    case clang::Type::BlockPointer:
        unsupported_kind = "block pointer"; break;
    case clang::Type::Complex:
        unsupported_kind = "complex"; break;
    case clang::Type::SubstTemplateTypeParmPack:
        unsupported_kind = "template parameter instance packed"; break;
    default: break;
  }
  // all successful cases have already returned.
  if (unsupported_kind.length() == 0) {
    std::stringstream buf;
    buf << "unsupported kind (" << type->getTypeClass() << ")";
    unsupported_kind = buf.str();
  }
  std::cerr << "Unsupported Type (" << unsupported_kind << "):"
         << clang::QualType(type, 0).getAsString ()
         << "\nAborting\n";
  exit(2);
}

logic_type
Clang_utils::logicArithmeticPromotion(
  const clang::SourceLocation &loc, const clang::Type* type) const {
  switch(type->getTypeClass()) {
    case clang::Type::Builtin:
      assert(llvm::dyn_cast<const clang::BuiltinType>(type));
      return
        makeBuiltinLogicType(loc, static_cast<clang::BuiltinType const*>(type));
    case clang::Type::Enum:
      return logic_type_Linteger();
    case clang::Type::Auto:
      { assert(llvm::dyn_cast<const clang::AutoType>(type));
        const clang::AutoType*
            autotype = static_cast<clang::AutoType const*>(type);
        return
          autotype->isDeduced()
          ? logicArithmeticPromotion(
            loc,autotype->getDeducedType().getTypePtr())
          : NULL;
      }
    case clang::Type::SubstTemplateTypeParm:
      { assert(llvm::dyn_cast<const clang::SubstTemplateTypeParmType>(type));
        const clang::SubstTemplateTypeParmType* replacementType
            = static_cast<clang::SubstTemplateTypeParmType const*>(type);
        return
          logicArithmeticPromotion(
            loc,replacementType -> getReplacementType().getTypePtr());
      };
    case clang::Type::TemplateSpecialization:
      { assert(llvm::dyn_cast<const clang::TemplateSpecializationType>(type));
        const clang::TemplateSpecializationType* sp_type =
           static_cast<clang::TemplateSpecializationType const*>(type);
        return sp_type->isSugared()
          ? logicArithmeticPromotion(loc, sp_type->desugar().getTypePtr())
          : NULL;
      }
    case clang::Type::Typedef:
      { assert(llvm::dyn_cast<const clang::TypedefType>(type));
        const clang::TypedefType* replacementType =
           static_cast<clang::TypedefType const*>(type);
        return replacementType->isSugared()
          ? logicArithmeticPromotion(
            loc, replacementType->desugar().getTypePtr())
          : NULL;
      };
    case clang::Type::Elaborated:
      { assert(llvm::dyn_cast<const clang::ElaboratedType>(type));
        const clang::ElaboratedType* elaborated =
            static_cast<clang::ElaboratedType const*>(type);
        return elaborated->isSugared()
          ? logicArithmeticPromotion(loc, elaborated->desugar().getTypePtr())
          : NULL;
      }
    default: break;
  }
  return NULL;
}

qual_type
Clang_utils::makeType(
  clang::SourceLocation const &loc,clang::QualType const& qt,
  VirtualDeclRegistration* declRegistration) const {
  list/*<specifier>*/ spec = make_specifier_list(qt);
  // QualType canonicalType = qt.getCanonicalType();
  typ type = makePlainType(loc, qt, declRegistration);
  return qual_type_cons(spec,type);
}

bool
Clang_utils::isExternCContext(const clang::DeclContext* ctx) {
  // NB: in the next clang version, we will be able to use directly
  // return ctx->isExternCContext();
  while(ctx) {
    if (ctx->getDeclKind()==clang::Decl::LinkageSpec) {
      const clang::LinkageSpecDecl* link_ctx
        = static_cast<const clang::LinkageSpecDecl*>(ctx);
      return link_ctx->getLanguage() == clang::LinkageSpecDecl::lang_c;
    }
    else ctx = ctx->getParent();
  }
  return false;
}

qual_type
Clang_utils::makePODType(
  clang::SourceLocation const& loc, clang::QualType const& qt) const {
  list/*<specifier>*/ spec = make_specifier_list(qt);
  // QualType canonicalType = qt.getCanonicalType();
  typ type = makePlainType(loc, qt, NULL, true);
  return qual_type_cons(spec,type);
}

const char* mk_tmp_name () {
  static unsigned long counter = 0;
  std::ostringstream s;
  s << "__fc_tmp_" << counter;
  counter++;
  return strdup(s.str().c_str());
}

const char* mk_materialized_tmp_name () {
  static unsigned long counter = 0;
  std::ostringstream s;
  s << "__clang_tmp_" << counter;
  counter++;
  return strdup(s.str().c_str());
}

bool isRecordOrRecordRef(const clang::Type* type) {
  return
    type->isStructureOrClassType() ||
    (type->isReferenceType() &&
     static_cast<const clang::ReferenceType*>(type)->
     getPointeeType()->isStructureOrClassType());
}


