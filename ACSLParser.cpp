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

//
// Description:
//   Implementation of the ACSL++ parser.
//

#include "clang/Basic/Version.h"
#include "llvm/ADT/SmallString.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/DeclTemplate.h"
#include "clang/Lex/Preprocessor.h"
#include "clang/Sema/Sema.h"
#include "clang/Sema/Lookup.h"
#include "clang/Basic/TargetInfo.h"
#include "clang/Lex/MacroArgs.h"

#include "ACSLParser.h"

namespace Acsl {

// FIXME - should combine these with a varargs argument
// FIXME - want to also allow logic functions with arbitrary numbers of arguments

void Parser::addBuiltinBinding(const std::string& ident, logic_type ret_type, std::initializer_list<logic_type> argtypes) {
  list types = NULL;
  auto iter = argtypes.end();
  while (iter != argtypes.begin()) {
    types = cons_container(logic_arg_decl_cons(*--iter, NULL), types);
  }
    logic_info def =
      logic_info_cons(
        qualified_name_cons(NULL,strdup(ident.c_str())),
        true,
        NULL,NULL,
      ret_type ? opt_some_container(ret_type) : opt_none(),
      types,
        logic_body_LBnone());
    _arguments.addOverloadedLogicFunctions(ident,def);
  }

//void Parser::addBuiltinBinding(const std::string& ident, logic_type ret_type, logic_type arg0) {
//  logic_info def =
//    logic_info_cons(
//      qualified_name_cons(NULL,strdup(ident.c_str())),
//      true,
//      NULL,NULL,
//      ret_type ? opt_some_container(ret_type) : opt_none(),
//      cons_container(
//          logic_arg_decl_cons(arg0,NULL),
//              NULL)
//          ,
//      logic_body_LBnone());
//  _arguments.addOverloadedLogicFunctions(ident,def);
//}
//
//void Parser::addBuiltinBinding(const std::string& ident, logic_type ret_type, logic_type arg0, logic_type arg1 ) {
//  logic_info def =
//    logic_info_cons(
//      qualified_name_cons(NULL,strdup(ident.c_str())),
//      true,
//      NULL,NULL,
//      ret_type ? opt_some_container(ret_type) : opt_none(),
//      cons_container(
//          logic_arg_decl_cons(arg0,NULL),
//          cons_container(
//              logic_arg_decl_cons(arg1,NULL)
//              ,NULL)
//          ),
//      logic_body_LBnone());
//  _arguments.addOverloadedLogicFunctions(ident,def);
//}

void Parser::addBuiltinBindings() {
  logic_type Lbool = logic_type_Lint(IBOOL);
  logic_type Lint = logic_type_Lint(IINT);
  logic_type Linteger = logic_type_Linteger();
  logic_type Lreal = logic_type_Lreal();
  logic_type Ldouble = logic_type_Lfloat(FDOUBLE);
  logic_type Lfloat = logic_type_Lfloat(FFLOAT);

  // Set the return type to NULL for predicates
  addBuiltinBinding("\\is_finite",NULL,{Lfloat});
  addBuiltinBinding("\\is_finite",NULL,{Ldouble});
  addBuiltinBinding("\\is_NaN",NULL,{Lfloat});
  addBuiltinBinding("\\is_NaN",NULL,{Ldouble});
  addBuiltinBinding("\\min",Linteger,{Linteger,Linteger});
  addBuiltinBinding("\\max",Linteger,{Linteger,Linteger});
  addBuiltinBinding("\\abs",Linteger,{Linteger});
  addBuiltinBinding("\\abs",Lreal,{Lreal});
  addBuiltinBinding("\\pow",Linteger,{Linteger,Linteger});
  addBuiltinBinding("\\pow",Lreal,{Lreal,Lreal});
  addBuiltinBinding("\\sqrt",Lreal,{Lreal});
  addBuiltinBinding("\\ceil",Lreal,{Lreal});
  addBuiltinBinding("\\floor",Lreal,{Lreal});
  addBuiltinBinding("\\exp",Lreal,{Lreal});
  addBuiltinBinding("\\log",Lreal,{Lreal});
  addBuiltinBinding("\\log10",Lreal,{Lreal});
  addBuiltinBinding("\\sin",Lreal,{Lreal});
  addBuiltinBinding("\\cos",Lreal,{Lreal});
  addBuiltinBinding("\\tan",Lreal,{Lreal});
  addBuiltinBinding("\\sinh",Lreal,{Lreal});
  addBuiltinBinding("\\cosh",Lreal,{Lreal});
  addBuiltinBinding("\\tanh",Lreal,{Lreal});
  addBuiltinBinding("\\asin",Lreal,{Lreal});
  addBuiltinBinding("\\acos",Lreal,{Lreal});
  addBuiltinBinding("\\atan",Lreal,{Lreal});
  addBuiltinBinding("\\asinh",Lreal,{Lreal});
  addBuiltinBinding("\\acosh",Lreal,{Lreal});
  addBuiltinBinding("\\atanh",Lreal,{Lreal});
  addBuiltinBinding("\\atan2",Lreal,{Lreal,Lreal});
  addBuiltinBinding("\\hypot",Lreal,{Lreal,Lreal});
}

void
Parser::Arguments::addErrorMessagesFromLexer()
{ std::list<Lexer::Error>& errorList = _lexer.errorList();
  std::list<Lexer::Error>::const_iterator iterEnd = errorList.end();
  for (std::list<Lexer::Error>::const_iterator iter = errorList.begin();
      iter != iterEnd; ++iter) {
    ++_countErrors;
    if (_errorMessages) {
      std::string message("[lexer error] ");
      message.append(iter->message);
      if (_errorMessages->empty()
          || (_errorMessages->back().getMessage() != message))
        _errorMessages->push_back(ErrorMessage(message,
              iter->filePos, iter->linePos, iter->columnPos));
      if (_doesStopOnError || !_errorMessages || _countErrors >= 20)
        return;
    };
  };
  errorList.clear();
}

void
Parser::Arguments::eatToken(ReadResult& result) {
  _lexer.eatToken(result);
}


const clang::NamedDecl*
Parser::Arguments::isCodeName(const std::string& name,
    const clang::TemplateArgument** templateArgument, bool* hasOverLoad) const
{ if (name.length() == 0)
    return NULL;
#if 0
  if (_clangContext->isFunctionOrMethod()) {
    // Apparently, LookupName does not consider formals in this case...
    const clang::FunctionDecl* f =
      static_cast<const clang::FunctionDecl*>(_clangContext);
    clang::FunctionDecl::param_const_iterator iter = f->param_begin();
    const clang::NamedDecl* param = NULL;
    while (iter!=f->param_end()) {
      const std::string s = (*iter)->getNameAsString();
      if (s == name) {
        param = *iter;
        break;
      }
      iter++;
    }
    if (param) return param;
  }
#endif

#if 0
  // The method clang::DeclContext::lookup seems to fail to find
  // adequate declaration. 
  // std::pair<clang::IdentifierInfo,const unsigned char*> mem;
  // mem.second = (const unsigned char*) name.c_str();
  // clang::DeclarationName delcName(&mem.first);
  
  const clang::DeclContext* currentContext = _clangContext;
  while (currentContext != NULL) {
    // clang::DeclContext::lookup_const_result cdeclResults
    //   = currentContext->lookup(delcName);
    if (currentContext->isRecord()
        && static_cast<const clang::RecordDecl*>(currentContext)->getName()
            .str() == name)
      return static_cast<const clang::RecordDecl*>(currentContext);
    if (currentContext->isNamespace()
        && static_cast<const clang::NamespaceDecl*>(currentContext)->getName()
            .str() == name)
      return static_cast<const clang::NamespaceDecl*>(currentContext);
    clang::DeclContext::decl_iterator iterEnd = currentContext->decls_end();
    for (clang::DeclContext::decl_iterator iter = currentContext->decls_begin();
        iter != iterEnd; ++iter) {
      clang::Decl* decl = *iter;
      clang::Decl::Kind kind = decl->getKind();
      if (kind >= clang::Decl::firstNamed && kind <= clang::Decl::lastNamed) {
        assert(llvm::dyn_cast<clang::NamedDecl>(decl));
        if (static_cast<const clang::NamedDecl*>(decl)->getNameAsString()
            == name)
          return static_cast<const clang::NamedDecl*>(decl);
      };
    };
    // if (cdeclResults.first != cdeclResults.second) {
    //   if (hasOverLoad)
    //     *hasOverLoad = (cdeclResults.first+1 != cdeclResults.second);
    //   return *cdeclResults.first;
    // };
    currentContext = currentContext->getParent();
  };
  // see Sema::CppLookupName(LookupResult &R, Scope *S)
  // for a conform lookup function
#endif

#if 1
  // clang::Token identifierToken;
  // identifierToken.startToken();
  // identifierToken.clearFlag(clang::Token::NeedsCleaning);
  // identifierToken.setIdentifierInfo(0);
  // // std::memset(&identifierToken, 0, sizeof(clang::Token));
  // identifierToken.setLength(name.size());
  // // identifierToken.setLocation(getSourceLocation(BufferPtr, TokLen));
  // identifierToken.setKind(clang::tok::raw_identifier);
  // identifierToken.setRawIdentifierData(name.c_str());
  // clang::IdentifierInfo& identifierInfo = *_clangSema->getPreprocessor()
  //     .LookUpIdentifierInfo(identifierToken);
  clang::IdentifierInfo& identifierInfo
      = _clangSema->getPreprocessor().getIdentifierTable().get(name);
  clang::LookupResult R(*_clangSema, &identifierInfo
      /* &_clangAST->Idents.get(name) */,
      _clangLocation, clang::Sema::LookupOrdinaryName);
  // Argh! The method getScopeForContext uses getCurScope that contains
  // the following comment:
  //   This routine must only be used when it is certain that semantic analysis
  //   and the parser are in precisely the same context, which is not the case
  //   when, e.g., we are performing any kind of template instantiation.
  //   Therefore, the only safe places to use this scope are in the parser
  //   itself and in routines directly invoked from the parser and *never* from
  //   template substitution or instantiation.
  // clang::Scope* scope = _clangSema->getScopeForContext(
  //    const_cast<clang::DeclContext*>(_clangContext));
  if (_clangSema->LookupName(R, _clangScope /* scope */, false)) {
    if (R.getResultKind() == clang::LookupResult::Found)
      return R.getFoundDecl();
    if (hasOverLoad && R.getResultKind()
        == clang::LookupResult::FoundOverloaded)
      *hasOverLoad = true;
  }
  else {
    const clang::NamedDecl* result = NULL;
    const clang::TemplateArgument*
        res = _clang_utils->findTemplateArgument(name, result);
    if (res) {
      if (templateArgument)
        *templateArgument = res;
      return result;
    };
  };
#endif
  return NULL;
}

const clang::NamedDecl*
Parser::Arguments::findQualifiedName(const std::string& name,
    const clang::DeclContext* context, bool* hasOverload) const
{ if (name.length() == 0)
    return NULL;
  clang::LookupResult R(*_clangSema, &_clangAST->Idents.get(name), _clangLocation,
      clang::Sema::LookupOrdinaryName);
  if (_clangSema->LookupQualifiedName(R, const_cast<clang::DeclContext*>(
          context))) {
    if (R.getResultKind() == clang::LookupResult::Found)
      return R.getFoundDecl();
    if (hasOverload
        && R.getResultKind() == clang::LookupResult::FoundOverloaded)
      *hasOverload = true;
  };
  return NULL;
}

template <class TypeTraits>
typename TypeTraits::ResultType
Parser::Arguments::isTypedefType(TypeTraits& traits, qualified_name name) const
{ /* qualification */ list prequalification = name->prequalification;
  const clang::DeclContext*
    declContext = _clangSema->Context.getTranslationUnitDecl();
  while (prequalification) {
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

    clang::LookupResult R(*_clangSema, &_clangAST->Idents.get(name),
        _clangLocation, clang::Sema::LookupOrdinaryName);
    const clang::NamedDecl* found = NULL;
    if (!_clangSema->LookupQualifiedName(R,
          const_cast<clang::DeclContext*>(declContext))) {
      if (name.compare(0, 10, "anonymous_") == 0)
        found = _clang_utils->findAnonymousDecl(name);
      if (!found)
        return TypeTraits::False();
    };
    if (!found && !R.isSingleResult()) // FIXME
      return TypeTraits::False();
    if (!found)
      found = R.getFoundDecl();
    clang::Decl::Kind kind = found->getKind();
    if (kind == clang::Decl::Namespace) {
      assert(llvm::dyn_cast<clang::NamespaceDecl>(found));
      declContext = static_cast<const clang::NamespaceDecl*>(found);
    }
    else if (kind >= clang::Decl::firstTag && kind <= clang::Decl::lastTag) {
      assert(llvm::dyn_cast<clang::TagDecl>(found));
      const clang::TagDecl*
        tagContext = static_cast<const clang::TagDecl*>(found);
      declContext = tagContext;
      if (qualif->tag_qualification == QTEMPLATEINSTANCE) {
        int existingInstancesNumber
          = tagContext->getNumTemplateParameterLists();
        for (int instance = 0; instance < existingInstancesNumber; ++instance) {
          // clang::TemplateParameterList* currentParameters
          //   = tagContext->getTemplateParameterList(instance);
          // TODO: check if qualification matches with currentParameters
          // TODO: find the actual instance of tagContext
          assert(false); // unimplemented
        };
        // TODO: A better alternative is to instantiate via Sema the
        //   CXXRecordDecl that corresponds to tagDecl.
      };
    }
    else if (kind == clang::Decl::ClassTemplate) {
      const clang::TemplateArgumentList* defaultTemplateArgs
          = _clang_utils->findInstanceArguments(found);
      assert(defaultTemplateArgs);
      void* InsertPos = NULL;
      clang::ClassTemplateSpecializationDecl* specialization =
        ((clang::ClassTemplateDecl*) const_cast<clang::NamedDecl*>(found))
        ->findSpecialization(defaultTemplateArgs->asArray(), InsertPos);
      if (!specialization)
         return TypeTraits::False();
      declContext = specialization;
    }
    else
      return TypeTraits::False();
    prequalification = prequalification->next;
  };

  clang::LookupResult R(*_clangSema, &_clangAST->Idents.get(name->decl_name),
      _clangLocation, clang::Sema::LookupOrdinaryName);
  const clang::NamedDecl* found = NULL;
  if (!_clangSema->LookupQualifiedName(R,
        const_cast<clang::DeclContext*>(declContext))) {
    if (strncmp(name->decl_name, "anonymous_", 10) == 0)
      found = _clang_utils->findAnonymousDecl(name->decl_name);
    if (!found)
      return TypeTraits::False();
  }
  if (!found && !R.isSingleResult()) // FIXME
    return TypeTraits::False();
  if (!found)
    found = R.getFoundDecl();
  clang::Decl::Kind kind = found->getKind();
  if (!(kind >= clang::Decl::firstType && kind <= clang::Decl::lastType)
      && kind != clang::Decl::ClassTemplate)
    return TypeTraits::False();
  if (kind == clang::Decl::ClassTemplate) {
    if (!traits.hasTemplateArgs())
      return TypeTraits::False();

    assert(llvm::dyn_cast<clang::ClassTemplateDecl>(found));
    /* template_parameter */ list templateArgs = traits.getTemplateArgs();
    const clang::ClassTemplateDecl* templateDecl
      = static_cast<const clang::ClassTemplateDecl*>(found);
    const clang::ClassTemplateSpecializationDecl* foundSpecialization = NULL;
    if (templateDecl) {
      clang::ClassTemplateDecl::spec_iterator iterEnd
        = const_cast<clang::ClassTemplateDecl*>(templateDecl)->spec_end();
      for (clang::ClassTemplateDecl::spec_iterator iter
          = const_cast<clang::ClassTemplateDecl*>(templateDecl)->spec_begin();
          !foundSpecialization && iter != iterEnd; ++iter) {
        tkind matchTemplateParameters =
          tkind_TTemplateInstance(
            _clang_utils->getTemplateExtension(
              tokenSourceLocation(), iter->getTemplateArgs()));
        struct _tkind templateParameters;
        templateParameters.tag_tkind = TTEMPLATEINSTANCE;
        templateParameters.cons_tkind.TTemplateInstance.parameters
          = templateArgs;
        if (tkind_equal(&templateParameters, matchTemplateParameters))
          foundSpecialization = *iter;
        free_tkind(matchTemplateParameters);
      };
    };
    // void* insertionPos = NULL;
    // const clang::ClassTemplateSpecializationDecl* foundSpecialization =
    //     templateDecl->findSpecialization(traits.getTemplateArgs(),
    //     traits.getNumTemplateArgs(), insertionPos);
    // if (!foundSpecialization)
    //   return TypeTraits::False();
    // return traits(foundSpecialization->getTypeForDecl());
    return traits(foundSpecialization->getTypeForDecl());
  };
  assert(llvm::dyn_cast<clang::TypeDecl>(found));
  const clang::TypeDecl* typeFound = static_cast<const clang::TypeDecl*>(found);
  const clang::Type* type = typeFound->getTypeForDecl();
  if (kind >= clang::Decl::firstTypedefName
      && kind <= clang::Decl::lastTypedefName)
    type = static_cast<const clang::TypedefNameDecl*>(typeFound)
      ->getUnderlyingType().getTypePtr();
  return traits(type);
}

class Parser::Arguments::IsIntegralTypeTraits {
private:
  const Clang_utils* _utils;

public:
  IsIntegralTypeTraits(const Clang_utils* utils) : _utils(utils) {}

  typedef bool ResultType;
  bool hasTemplateArgs() const { return false; }
  /* template_parameter */ list getTemplateArgs() const { return NULL; }

  static bool False() { return false; }
  ResultType operator()(const clang::Type* type) const
    { return _utils->isIntegralType(type); }
};

class Parser::Arguments::IsSignedTypeTraits {
private:
  const Clang_utils* _utils;

public:
  IsSignedTypeTraits(const Clang_utils* utils) : _utils(utils) {}

  bool hasTemplateArgs() const { return false; }
  /* template_parameter */ list getTemplateArgs() const { return NULL; }

  typedef bool ResultType;
  static bool False() { return false; }
  ResultType operator()(const clang::Type* type) const
    { return _utils->isSignedType(type); }
};

class Parser::Arguments::IsArithmeticTypeTraits {
private:
  const Clang_utils* _utils;

public:
  IsArithmeticTypeTraits(const Clang_utils* utils) : _utils(utils) {}

  bool hasTemplateArgs() const { return false; }
  /* template_parameter */ list getTemplateArgs() const { return NULL; }

  typedef bool ResultType;
  static bool False() { return false; }
  ResultType operator()(const clang::Type* type) const
    { return _utils->isArithmeticType(type); }
};

class Parser::Arguments::IsFloatingTypeTraits {
private:
  const Clang_utils* _utils;

public:
  IsFloatingTypeTraits(const Clang_utils* utils) : _utils(utils) {}

  bool hasTemplateArgs() const { return false; }
  /* template_parameter */ list getTemplateArgs() const { return NULL; }

  typedef bool ResultType;
  static bool False() { return false; }
  ResultType operator()(const clang::Type* type) const
    { return _utils->isFloatingType(type); }
};

class Parser::Arguments::IsPointerTypeTraits {
private:
  const Clang_utils* _utils;

public:
  IsPointerTypeTraits(const Clang_utils* utils) : _utils(utils) {}

  bool hasTemplateArgs() const { return false; }
  /* template_parameter */ list getTemplateArgs() const { return NULL; }

  typedef bool ResultType;
  static bool False() { return false; }
  ResultType operator()(const clang::Type* type) const
    { return _utils->isPointerType(type); }
};

class Parser::Arguments::IsReferenceTypeTraits {
private:
  const Clang_utils* _utils;

public:
  IsReferenceTypeTraits(const Clang_utils* utils) : _utils(utils) {}

  bool hasTemplateArgs() const { return false; }
  /* template_parameter */ list getTemplateArgs() const { return NULL; }

  typedef bool ResultType;
  static bool False() { return false; }
  ResultType operator()(const clang::Type* type) const
    { return _utils->isReferenceType(type); }
};

class Parser::Arguments::IsArrayTypeTraits {
private:
  const Clang_utils* _utils;

public:
  IsArrayTypeTraits(const Clang_utils* utils) : _utils(utils) {}

  bool hasTemplateArgs() const { return false; }
  /* template_parameter */ list getTemplateArgs() const { return NULL; }

  typedef bool ResultType;
  static bool False() { return false; }
  ResultType operator()(const clang::Type* type) const
    { return _utils->isArrayType(type); }
};

class Parser::Arguments::IsCompoundTypeTraits {
private:
  const Clang_utils* _utils;
  tkind* _templateKind;

public:
  IsCompoundTypeTraits(const Clang_utils* utils, tkind* templateKind)
    : _utils(utils), _templateKind(templateKind) {}

  bool hasTemplateArgs() const { return false; }
  /* template_parameter */ list getTemplateArgs() const { return NULL; }

  typedef qualified_name ResultType;
  static qualified_name False() { return NULL; }
  ResultType operator()(const clang::Type* type) const
    { return _utils->makeCompoundType(type, _templateKind); }
};

class Parser::Arguments::GetRecordTypeTraits {
private:
  const Clang_utils* _utils;

public:
  GetRecordTypeTraits(const Clang_utils* utils) : _utils(utils) {}

  bool hasTemplateArgs() const { return false; }
  /* template_parameter */ list getTemplateArgs() const { return NULL; }

  typedef const clang::RecordType* ResultType;
  static const clang::RecordType* False() { return NULL; }
  ResultType operator()(const clang::Type* type) const
    { ResultType result = NULL;
      if (type->getTypeClass() == clang::Type::Typedef) {
        assert(llvm::dyn_cast<clang::TypedefType>(type));
        type = static_cast<const clang::TypedefType*>(type)->desugar()
          .getTypePtr();
      };
      if (type->getTypeClass() == clang::Type::Record) {
        assert(llvm::dyn_cast<clang::RecordType>(type));
        result = static_cast<ResultType>(type);
      }
      return result;
    }
};

class Parser::Arguments::LogicArithmeticPromotionTraits {
private:
  const Clang_utils* _utils;

public:
  LogicArithmeticPromotionTraits(const Clang_utils* utils) : _utils(utils) {}

  bool hasTemplateArgs() const { return false; }
  /* template_parameter */ list getTemplateArgs() const { return NULL; }

  typedef logic_type ResultType;
  static logic_type False() { return NULL; }
  ResultType operator()(const clang::Type* type) const
    { return _utils->logicArithmeticPromotion(clang::SourceLocation(),type); }
  // FIXME - what about this source location? and elsewhere in this file?
};

class Parser::Arguments::MakePointedTypeTraits {
private:
  const Clang_utils* _utils;

public:
  MakePointedTypeTraits(const Clang_utils* utils) : _utils(utils) {}

  bool hasTemplateArgs() const { return false; }
  /* template_parameter */ list getTemplateArgs() const { return NULL; }

  typedef logic_type ResultType;
  static logic_type False() { return NULL; }
  ResultType operator()(const clang::Type* type) const
    { return _utils->makePointedType(clang::SourceLocation(),type); }
};

class Parser::Arguments::MakeReferencedTypeTraits {
private:
  const Clang_utils* _utils;

public:
  MakeReferencedTypeTraits(const Clang_utils* utils) : _utils(utils) {}

  bool hasTemplateArgs() const { return false; }
  /* template_parameter */ list getTemplateArgs() const { return NULL; }

  typedef logic_type ResultType;
  static logic_type False() { return NULL; }
  ResultType operator()(const clang::Type* type) const
    { return _utils->makeReferencedType(clang::SourceLocation(),type); }
};

class Parser::Arguments::MakeElementArrayTypeTraits {
private:
  const Clang_utils* _utils;

public:
  MakeElementArrayTypeTraits(const Clang_utils* utils) : _utils(utils) {}

  bool hasTemplateArgs() const { return false; }
  /* template_parameter */ list getTemplateArgs() const { return NULL; }

  typedef logic_type ResultType;
  static logic_type False() { return NULL; }
  ResultType operator()(const clang::Type* type) const
    { return _utils->makeElementArrayType(clang::SourceLocation(),type); }
};

class Parser::Arguments::MakeLogicTypeTraits {
private:
  const Clang_utils* _utils;

public:
  MakeLogicTypeTraits(const Clang_utils* utils) : _utils(utils) {}

  bool hasTemplateArgs() const { return false; }
  /* template_parameter */ list getTemplateArgs() const { return NULL; }

  typedef logic_type ResultType;
  static logic_type False() { return NULL; }
  ResultType operator()(const clang::Type* type) const
    { return _utils->makeLogicType(clang::SourceLocation(),type); }
};

bool
Parser::Arguments::isIntegralTypedefType(qualified_name name) const
{ IsIntegralTypeTraits traits(_clang_utils);
  return isTypedefType(traits, name);
}

bool
Parser::Arguments::isSignedTypedefType(qualified_name name) const
{ IsSignedTypeTraits traits(_clang_utils);
  return isTypedefType(traits, name);
}

bool
Parser::Arguments::isArithmeticTypedefType(qualified_name name) const
{ IsArithmeticTypeTraits traits(_clang_utils);
  return isTypedefType(traits, name);
}

bool
Parser::Arguments::isFloatingTypedefType(qualified_name name) const
{ IsFloatingTypeTraits traits(_clang_utils);
  return isTypedefType(traits, name);
}

bool
Parser::Arguments::isPointerTypedefType(qualified_name name) const
{ IsPointerTypeTraits traits(_clang_utils);
  return isTypedefType(traits, name);
}

bool
Parser::Arguments::isReferenceTypedefType(qualified_name name) const
{ IsReferenceTypeTraits traits(_clang_utils);
  return isTypedefType(traits, name);
}

bool
Parser::Arguments::isArrayTypedefType(qualified_name name) const
{ IsArrayTypeTraits traits(_clang_utils);
  return isTypedefType(traits, name);
}

bool Parser::Arguments::is_wchar_signed() const {
  return
    clang::TargetInfo::isTypeSigned(_clangAST->getTargetInfo().getWCharType());
}

bool Parser::Arguments::is_char_signed() const {
  return _clangAST->getLangOpts().CharIsSigned;
}

qualified_name
Parser::Arguments::makeCompoundTypedefType(qualified_name name,
    tkind* templateKind) const
{ IsCompoundTypeTraits traits(_clang_utils, templateKind);
  return isTypedefType(traits, name);
}

logic_type
Parser::Arguments::makeTypeOfPointed(qualified_name name) const
{ MakePointedTypeTraits traits(_clang_utils);
  return isTypedefType(traits, name);
}

logic_type
Parser::Arguments::makeTypeOfReferenced(qualified_name name) const
{ MakeReferencedTypeTraits traits(_clang_utils);
  return isTypedefType(traits, name);
}

logic_type
Parser::Arguments::makeTypeOfArrayElement(qualified_name name) const
{ MakeElementArrayTypeTraits traits(_clang_utils);
  return isTypedefType(traits, name);
}

const clang::RecordType*
Parser::Arguments::getRecordType(qualified_name name) const
{ GetRecordTypeTraits traits(_clang_utils);
  return isTypedefType(traits, name);
}

GlobalContext::NestedContext*
Parser::Arguments::findLogicName(qualified_name context,
    const std::string& name, tkind* templateParameterContext) const {
  GlobalContext::NestedContext* logicContext
      = _clang_utils->globalAcslContext().findAbsolute(context);
  if (logicContext) {
    if (templateParameterContext && *templateParameterContext
        && (*templateParameterContext)->tag_tkind == TTEMPLATEINSTANCE) {
      if (logicContext->isQualification() && logicContext->asQualification()
            .hasTemplateRecordType())
        logicContext = logicContext->asQualification().findInstance(
          (*templateParameterContext)->cons_tkind.TTemplateInstance.parameters);
      else
        logicContext = NULL;
    };
  };
  return logicContext
    ? _clang_utils->globalAcslContext().find(name, logicContext)
    : NULL;
}

logic_type
Parser::Arguments::logicArithmeticPromotion(qualified_name name) const
{ LogicArithmeticPromotionTraits traits(_clang_utils);
  return isTypedefType(traits, name);
}

logic_type
Parser::Arguments::makeLogicType(qualified_name name) const
{ MakeLogicTypeTraits traits(_clang_utils);
  return isTypedefType(traits, name);
}

qualified_name
Parser::Arguments::makeLogicQualifiedName(const std::string& name) const {
  const clang::DeclContext* ctxt = _clangContext;
  return _clang_utils->makeQualifiedName(ctxt, copy_string(name));
}

logic_type
Parser::Arguments::queryThisType() const {
  const clang::DeclContext* currentContext = _clangContext;
  while ((currentContext != NULL) && !currentContext->isRecord())
    currentContext = currentContext->getParent();
  if (!currentContext)
    return NULL;
  /* qualification */ list prequalification = NULL;
  const clang::DeclContext* qualContext = currentContext->getParent();
  while (qualContext != NULL) {
    if (qualContext->isRecord()) {
      const clang::RecordDecl* decl = static_cast<const clang::RecordDecl*>
          (qualContext);
      qualification res = NULL;
      if (decl->getKind() == clang::Decl::ClassTemplateSpecialization) {
        const clang::ClassTemplateSpecializationDecl* TSD
            = llvm::dyn_cast<clang::ClassTemplateSpecializationDecl>(decl);
        res = qualification_QTemplateInstance(
          strdup(decl->getName().str().c_str()),
          _clang_utils->getTemplateExtension(
            tokenSourceLocation(),TSD->getTemplateArgs()));
      }
      else
        res = qualification_QStructOrClass(
          strdup(decl->getName().str().c_str()));
      prequalification = cons_container(res, prequalification);
    }
    else if (qualContext->isNamespace())
      prequalification = cons_container(qualification_QNamespace(
        strdup(static_cast<const clang::NamespaceDecl*>(qualContext)
          ->getName().str().c_str())), prequalification);
    qualContext = qualContext->getParent();
  };
  const clang::RecordDecl* decl = static_cast<const clang::RecordDecl*>
      (currentContext);
  tkind templateParameters = NULL;
  if (decl->getKind() == clang::Decl::ClassTemplateSpecialization) {
    const clang::ClassTemplateSpecializationDecl* TSD
        = llvm::dyn_cast<clang::ClassTemplateSpecializationDecl>(decl);
    templateParameters =
      tkind_TTemplateInstance(
        _clang_utils->getTemplateExtension(
          tokenSourceLocation(),TSD->getTemplateArgs()));
  }
  else
    templateParameters = tkind_TStandard();
  const clang::RecordDecl* record =
    static_cast<const clang::RecordDecl*>(currentContext);
  qualified_name rec_name =
    qualified_name_cons(
      prequalification, strdup(record->getName().str().c_str()));
  logic_type classType =
    record->isUnion() ?
    logic_type_Lunion(rec_name, templateParameters):
    logic_type_Lstruct(rec_name, templateParameters);
  if (isGlobalAnnotContext()) return classType;
  else return logic_type_Lpointer(classType);
}

term_lval Parser::Arguments::thisLval () const {
  logic_type thisType = queryThisType();
  if (!thisType) return NULL;
  term_lval res = NULL;
  if (thisType->tag_logic_type == LPOINTER) {
    term_lval thisPtr =
      term_lval_cons(
        term_lhost_TVar(
          logic_var_cons(qualified_name_cons(NULL, strdup("this")), LVFORMAL)),
        term_offset_TNoOffset());
    res =
      term_lval_cons(
        term_lhost_TMem(
          term_cons(term_node_TLval(thisPtr), newTokenLocation(), NULL)),
        term_offset_TNoOffset());
  } else {
    res = 
      term_lval_cons(
        term_lhost_TVar(
          logic_var_cons(qualified_name_cons(NULL,strdup("\\this")), LVFORMAL)),
        term_offset_TNoOffset());
  }
  free_logic_type(thisType);
  return res;
}

class Parser::Arguments::RetrieveTypeOfFieldTraits {
private:
  const Clang_utils* _utils;
  const RTTITable* _rttiTable;
  std::string _fieldName;
  term_offset& _offset;
  logic_type& _ltype;
  tkind _templateParameters;
  std::string _errorMessage;
  const clang::ASTContext* _clangAST;
  clang::Sema* _clangSema;
  clang::SourceLocation _location;

public:
  RetrieveTypeOfFieldTraits(const Clang_utils* utils,const RTTITable* rttiTable,
      const std::string& fieldName, term_offset& offset, logic_type& ltype,
      tkind templateParameters, const clang::ASTContext* clangAST,
      clang::Sema* clangSema, clang::SourceLocation location)
    : _utils(utils), _rttiTable(rttiTable), _fieldName(fieldName),
      _offset(offset), _ltype(ltype), _templateParameters(templateParameters),
      _clangAST(clangAST), _clangSema(clangSema), _location(location) {}

  bool hasTemplateArgs() const
    { return _templateParameters->tag_tkind == TTEMPLATEINSTANCE; }
  /* template_parameter */ list getTemplateArgs() const
    { return _templateParameters->cons_tkind.TTemplateInstance.parameters; }
  const std::string& errorMessage() const { return _errorMessage; }

  typedef bool ResultType;
  static bool False() { return false; }
  ResultType operator()(const clang::Type* type)
    { return _utils->retrieveTypeOfField(type, _fieldName, _offset, _ltype,
        _errorMessage, _clangAST, _clangSema, _location, *_rttiTable);
    }
};

bool
Parser::Arguments::retrieveTypeOfField(qualified_name name,
    tkind templateParameters, const std::string& fieldName,
    term_offset& offset, logic_type& ltype, std::string& errorMessage)
{ RetrieveTypeOfFieldTraits traits(_clang_utils, &_rttiTable, fieldName,
      offset, ltype, templateParameters, _clangAST, _clangSema, _clangLocation);
  bool result = isTypedefType(traits, name);
  if (!result)
    errorMessage = traits.errorMessage();
  return result;
}

bool
Parser::Arguments::addOverloadedLogicFunctionOrOperator(const std::string& name,
    logic_info info, bool isMethod,
    DLexer::OperatorPunctuatorToken::Type* codeOperator) {
  GlobalContext::NestedContext::SonsSet* localScope = NULL;
  if (_currentLogicScope) {
    localScope = _currentLogicScope->ssons();
    if (!localScope && _currentLogicScope->sparent())
      localScope = _currentLogicScope->sparent()->ssons();
  }
  if (!localScope)
    localScope = &_clang_utils->globalAcslContext().logicTable();
  GlobalContext::NestedContext locateContext(name);
  GlobalContext::NestedContext::SonsSet::iterator
    found = localScope->find(&locateContext);
  if (found == localScope->end()) {
    if (!codeOperator)
      localScope->insert(
          new GlobalContext::OverloadedLogicFunctions(name, info, isMethod));
    else
      localScope->insert(new GlobalContext::OverloadedLogicOperators(name,
            *codeOperator, info, isMethod));
  }
  else if (!(*found)->isOverloadedLogicFunctions())
    return false;
  else {
    typedef GlobalContext::OverloadedLogicFunctions::Functions Functions;
    const Functions& existingInfos
      = (*found)->asOverloadedLogicFunctions().getFunctions();
    Functions::const_iterator iterEnd = existingInfos.end();
    for (Functions::const_iterator iter = existingInfos.begin();
        iter != iterEnd; ++iter) {
      logic_info sourceInfo = iter->second;

      std::map<std::string, std::string> renaming;
      bool isEqual = true;
      if (sourceInfo->tparams) {
        if (!info->tparams)
          isEqual = false;
        /* const char* */ list infoParamNames = info->tparams,
                        sourceInfoParamNames = sourceInfo->tparams;
        while (isEqual && infoParamNames && sourceInfoParamNames) {
          renaming.insert(std::pair<std::string, std::string>(
            (const char*) sourceInfoParamNames->element.container,
            (const char*) infoParamNames->element.container));
          infoParamNames = infoParamNames->next;
          sourceInfoParamNames = sourceInfoParamNames->next;
        };
        if (infoParamNames || sourceInfoParamNames)
          isEqual = false;
      };
      isEqual = isEqual
        || (info->returned_type->is_some == sourceInfo->returned_type->is_some);
      if (isEqual && info->returned_type->is_some)
        isEqual = logic_type_equal(
            (logic_type) sourceInfo->returned_type->content.container,
            (logic_type) info->returned_type->content.container);
      if (isEqual) {
        /* logic_arg_decl */ list args = info->profile,
                                  sourceArgs = sourceInfo->profile;
        while (isEqual && args && sourceArgs) {
          isEqual = logic_type_equal(
            ((logic_arg_decl) args->element.container)->la_type,
            ((logic_arg_decl) sourceArgs->element.container)->la_type);
          args = args->next;
          sourceArgs = sourceArgs->next;
        };
        isEqual = isEqual && (args == NULL) && (sourceArgs == NULL);
      };
      if (isEqual) {
        if (sourceInfo->fun_body->tag_logic_body == LBNONE) {
          free_logic_body(sourceInfo->fun_body);
          sourceInfo->fun_body = info->fun_body;
          info->fun_body = logic_body_LBnone();
        }
        else if (info->fun_body->tag_logic_body == LBNONE)
          return false;
        if (!sourceInfo->arg_labels) {
          sourceInfo->arg_labels = info->arg_labels;
          info->arg_labels = NULL;
        }
        else {
          while (info->arg_labels) {
            /* logic_label */ list sourceLabelIter = sourceInfo->arg_labels;
            do {
              if (logic_label_equal(
                    (logic_label) sourceLabelIter->element.container,
                    (logic_label) info->arg_labels->element.container))
                break;
              sourceLabelIter = sourceLabelIter->next;
            } while (sourceLabelIter);
            if (!sourceLabelIter) {
              sourceInfo->arg_labels = cons_container((logic_label) info
                  ->arg_labels->element.container, sourceInfo->arg_labels);
              /* logic_label */ list cell = info->arg_labels;
              info->arg_labels = info->arg_labels->next;
              free(cell);
            }
            else {
              /* logic_label */ list cell = info->arg_labels;
              free_logic_label((logic_label)
                  info->arg_labels->element.container);
              info->arg_labels = info->arg_labels->next;
              free(cell);
            };
            info->arg_labels = info->arg_labels->next;
          };
        };
        return true;
      }
    };
    (*found)->asOverloadedLogicFunctions().addFunction(info, isMethod);
  };
  return true;
}
 
bool
Parser::Arguments::addLogicType(const std::string& name, logic_type_info
    ltypeInfo) {
  GlobalContext::NestedContext::SonsSet* localScope = NULL;
  if (_currentLogicScope) {
    localScope = _currentLogicScope->ssons();
    if (!localScope && _currentLogicScope->sparent())
      localScope = _currentLogicScope->sparent()->ssons();
  }
  if (!localScope)
    localScope = &_clang_utils->globalAcslContext().logicTable();
  GlobalContext::NestedContext locateContext(name);
  GlobalContext::NestedContext::SonsSet::iterator
    found = localScope->find(&locateContext);
  if (found != localScope->end())
    return false;

  localScope->insert(new GlobalContext::LogicType(name, ltypeInfo));
  return true;
}

GlobalContext::LogicType*
Parser::Arguments::findGlobalLogicType(qualified_name name) const {
  GlobalContext::NestedContext* result
    = _clang_utils->globalAcslContext().findAbsolute(name);
  return (result && result->isLogicType()) ? &result->asLogicType() : NULL;
}

/* qualification */ list
Parser::Arguments::createPrequalification() const {
  /* qualification */ list result = NULL;
  GlobalContext::NestedContext* scope = _currentLogicScope;
  while (scope) {
    if (scope->isQualification()) {
      result = cons_container(scope->asQualification().getQualification(),
          result);
      scope = scope->sparent();
    }
    else if (scope->isTemplateQualification()) {
      GlobalContext::NestedContext* rightParent = scope->sparent();
      assert(rightParent && rightParent->isQualification());
      result = cons_container(scope->asTemplateQualification()
          .getQualification(strdup(rightParent->asQualification()
            .getName().c_str())), result);
      scope = rightParent->sparent();
    }
    else
      assert(false);
  };
  return result;
}

GlobalContext::LogicVariable*
Parser::Arguments::findGlobalLogicVariable(qualified_name name) const {
  GlobalContext::NestedContext* result
    = _clang_utils->globalAcslContext().findAbsolute(name);
  return (result && result->isLogicVariable())
    ? &result->asLogicVariable() : NULL;
}


logic_label
Parser::Arguments::findLogicLabel(const std::string& name) const {
  std::set<std::string>::iterator found = _logicLabels.find(name);
  if (found != _logicLabels.end())
    return logic_label_LogicLabel(strdup(found->c_str()));

  clang::IdentifierInfo& identifierInfo
      = _clangSema->getPreprocessor().getIdentifierTable().get(name);
  clang::NamedDecl* foundDecl = _clangSema->LookupSingleName(
      _clangScope /* scope */, &identifierInfo, _clangLocation,
      clang::Sema::LookupLabel, clang::Sema::NotForRedeclaration);
  if (!foundDecl || (foundDecl->getKind() != clang::Decl::Label))
    return NULL;
  assert(llvm::dyn_cast<clang::LabelDecl>(foundDecl));
  return logic_label_StmtLabel(strdup(foundDecl->getName().str().c_str()));
}

logic_type
Parser::Arguments::createResultType() const {
  const clang::DeclContext* context = _clangContext;
  clang::Decl::Kind declKind;
  if (!_result_context) return NULL;
  while (context
      && !((declKind = context->getDeclKind()) >= clang::Decl::firstFunction
      && declKind <= clang::Decl::lastFunction))
    context = context->getParent();
  if (!context)
    return NULL;
  assert(llvm::dyn_cast<clang::FunctionDecl>(context));
  const clang::FunctionDecl*
    functionDecl = static_cast<const clang::FunctionDecl*>(context);
  const clang::SourceLocation loc = tokenSourceLocation();
  return
    _clang_utils->makeLogicType(loc,functionDecl->getReturnType().getTypePtr());
}

void
Parser::parse(const std::string& buffer, const clang::SourceLocation& sourceLocation) {
  lexer().setBuffer(buffer, sourceLocation);
  _arguments._tokenLocation = lexer().seeTokenLocation();
  _arguments._clangLocation = sourceLocation;
//  _tokenLocation->linenum2 = __tokenLocation->linenum1;
//  _tokenLocation->charnum2 = _tokenLocation->charnum1-1;
  ReadResult parseResult = lexer().readToken();
  while (parseResult != RRFinished) {
    if (parseResult == RRNeedChars) {
        parseResult = _arguments.lexer().readToken();
        if (_arguments.lexer().hasErrors())
          _arguments.addErrorMessagesFromLexer();
      if (parseResult == RRFinished)
        break;
      if (parseResult == RRNeedChars)
        break; // could add characters to buffer
    };
 
    if (!_errorMessages.empty()) {
      std::list<ErrorMessage>::const_iterator iter = _errorMessages.begin();
      while(iter != _errorMessages.end()) {
        std::cerr << iter->getMessage() << std::endl;
        iter++;
      }
      _errorMessages.clear();
      if (_arguments.get_clang_utils()->stopOnAnnotError())
        exit(2);
    }

    while (parseResult == RRContinueLexing)
      parseResult = _arguments.lexer().readToken();
    if (parseResult == RRHasToken) {
      DLexer::AbstractToken::Type type = _arguments.queryToken().getType();
//      // This test is to be removed!
//      // The preprocessor should be called by the first pass
//      //   with the comment handler!
//      if (type == DLexer::AbstractToken::TIdentifier) {
//        if (_arguments.isPreprocessingDirective(
//            ((const DLexer::IdentifierToken&) _arguments.getContentToken())
//              .content())) {
//          std::string identifier = ((const DLexer::IdentifierToken&)
//            _arguments.getContentToken()).content();
//          clang::MacroInfo* macro = _arguments.getMacro(identifier);
//          if (_arguments._usedMacros.find(identifier)
//              != _arguments._usedMacros.end())
//            parseResult = RRHasToken;
//          else if (_arguments.handleMacroExpandedIdentifier(identifier, macro,
//                parseResult)) {
//            parseResult = RRNeedChars;
//            continue;
//          };
//        };
//      };
      if (parseResult == RRHasToken && type != DLexer::AbstractToken::TComment) {
        do {
          parseResult = _state.parse(_arguments);
          if (_arguments.hasErrors()) {
            std::list<ErrorMessage>& errors = _arguments.errors();
            std::list<ErrorMessage>::const_iterator iterEnd = errors.end();
            for (std::list<ErrorMessage>::const_iterator iter = errors.begin();
                iter != iterEnd; ++iter)
              std::cerr << iter->filepos() << ':' << iter->linepos() << ':'
                << iter->columnpos() << ": " << iter->getMessage() << std::endl;
            errors.clear();
          };
        } while (parseResult == RRContinueParsing);
//        if (parseResult == RRFinished && !lexer().hasFinished()) {
//          location loc = lexer().seeTokenLocation();
//          std::cerr << loc->filename1 << ":" << loc->linenum1 << ":" << loc->charnum1 << ": " << "Parser terminated before the end of input" << std::endl;
//        }
      }
      else
        parseResult = RRNeedChars;
      if (parseResult == RRNeedChars && _arguments.lexer().doesNeedClear())
        _arguments.lexer().clearToken();
    };
  };
}

bool
Parser::Arguments::addErrorMessage(const std::string& message, location tokenLocation)
  { ++_countErrors;
    if (_errorMessages && (_errorMessages->empty()
        || (_errorMessages->back().getMessage() != message))) {
      location tokenLocation = _lexer.seeTokenLocation();
      _errorMessages->push_back(ErrorMessage(message,
          tokenLocation->filename1, tokenLocation->linenum1,
          tokenLocation->charnum1));
    }
    return !doesStopAfterTooManyErrors();
  }


} // end of namespace Acsl

