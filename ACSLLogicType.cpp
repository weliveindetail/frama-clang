/**************************************************************************/
/*                                                                        */
/*  This file is part of Frama-Clang                                      */
/*                                                                        */
/*  Copyright (C) 2012-2021                                               */
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
//   Implementation of the ACSL logic types.
//

#include "ACSLTermOrPredicate.h"
#include "ACSLParser.h"

namespace Acsl {

bool is_signed(ikind i, Parser::Arguments &context) {
  switch (i) {
    case IBOOL:
    case ICHAR_U:
    case IUCHAR:
    case IWCHAR_U:
    case IWUCHAR:
    case IUSHORT:
    case IUINT:
    case IULONG:
    case ICHAR16:
    case ICHAR32:
      return false;
    case ICHAR:
      return context.is_char_signed();
    case IWCHAR:
      return context.is_wchar_signed();
    default:
      return true;
  }
}

bool equivalent_int_kind(ikind i1, ikind i2, Parser::Arguments &context) {
  if (i1 == i2) return true;
  if (is_signed(i1,context) != is_signed(i2,context)) return false;
  if ((i1 == IWCHAR || i1 == IWCHAR_U || i1 == IWCHAR_S) &&
      (i2 == IWCHAR || i2 == IWCHAR_U || i2 == IWCHAR_S)) return true;
  if ((i1 == ICHAR || i1 == ICHAR_U || i1 == ICHAR_S) &&
      (i2 == ICHAR || i2 == ICHAR_U || i2 == ICHAR_S)) return true;
  return false;
}

bool compatible_int_kind(ikind i1, ikind i2, Parser::Arguments &context) {
  if (equivalent_int_kind(i1,i2,context)) return true;
  if (i1 >= ISHORT && i2 < ISHORT)
    // char and bool are compatible with anything longer than short
    return true;

  if (is_signed(i1, context) != is_signed(i2, context)) return false;

  if (i1 == IULONG || i1 == ILONG) return true;
  if (i2 == IULONG || i2 == ILONG) return false;
  if (i1 == IUINT || i1 == IINT) return true;
  if (i2 == IUINT || i2 == IINT) return false;
  if (i1 == ISHORT || i1 == IUSHORT) return true;
  if (i2 == ISHORT || i2 == IUSHORT) return false;
  if (i1 == ICHAR || i1 == IUCHAR || i1 == ISCHAR) return true;
  // i1 is bool, i2 is not compatible with it
  return false;
}

bool compatible_float_kind(fkind f1, fkind f2) {
  if (f1 == FLONGDOUBLE) return true;
  if (f2 == FLONGDOUBLE) return false;
  if (f1 == FDOUBLE) return true;
  if (f2 == FDOUBLE) return false;
  // f1 == f2 == FFLOAT
  return true;
}

// true if v2 is compatible with v1, i.e. is a subtype of v1
// note that we don't use inheritance relation here to check for
// compatibility.
bool
logic_type_compatible(logic_type v1, logic_type v2,
                      Parser::Arguments &context) {
  while (v1->tag_logic_type == LREFERENCE)
    v1 = v1->cons_logic_type.Lreference.subtype;
  while (v2->tag_logic_type == LREFERENCE)
    v2 = v2->cons_logic_type.Lreference.subtype;
  tag_logic_type first = v1->tag_logic_type;
  tag_logic_type second = v2->tag_logic_type;

  // VP: technically, any int is compatible with a real, the test below
  // should be improved...
  if (first == LINT)
    first = LINTEGER;
  else if (first == LFLOAT)
    first = LREAL;
  if (second == LINT)
    second = LINTEGER;
  else if (second == LFLOAT)
    second = LREAL;

  if (second == LPOINTER && first == LARRAY) {
    v2 = v2->cons_logic_type.Lpointer.subtype;
    v1 = v1->cons_logic_type.Larray.subtype;
    first = v1->tag_logic_type;
    second = v2->tag_logic_type;
  };
  if (first == LENUM && second != LENUM)
    first = LINTEGER;

  if (first == LREAL && second == LINTEGER) second = LREAL;

  if (first != second)
    return false;
  switch (v1->tag_logic_type) {
    case LVOID:
      return true;
    case LINTEGER:
      return true;
    case LREAL:
      return true;
    case LINT: {
      if (v2->tag_logic_type == LINT) {
        return
          compatible_int_kind(
            v1->cons_logic_type.Lint.kind,
            v2->cons_logic_type.Lint.kind,
            context);
          }
      return false; // v2 is a LINTEGER
    }
    case LFLOAT: {
      if (v2->tag_logic_type == LFLOAT) {
        return
          compatible_float_kind(
            v1->cons_logic_type.Lfloat.kind, v2->cons_logic_type.Lfloat.kind);
      }
      return false; // v2 is a LREAL
    }
    case LARRAY:
      if (!logic_type_compatible(
            v1->cons_logic_type.Larray.subtype,
            v2->cons_logic_type.Larray.subtype,
            context))
        return false;
      if (v1->cons_logic_type.Larray.dim->is_some
          != v2->cons_logic_type.Larray.dim->is_some) {
        if (v2->cons_logic_type.Larray.dim->is_some)
          return false;
      }
      if (v1->cons_logic_type.Larray.dim->is_some) {
        if (!logic_constant_equal((logic_constant) v1->cons_logic_type
              .Larray.dim->content.container,
            (logic_constant)v2->cons_logic_type.Larray.dim->content.container))
          return false;
      };
      return true;
    case LPOINTER:
      return logic_type_compatible(
        v1->cons_logic_type.Lpointer.subtype,
        v2->cons_logic_type.Lpointer.subtype,
        context);
    case LENUM:
      return qualified_name_equal(v1->cons_logic_type.Lenum.name,
            v2->cons_logic_type.Lenum.name);
    case LSTRUCT:
      return qualified_name_equal(v1->cons_logic_type.Lstruct.name,
          v2->cons_logic_type.Lstruct.name)
        && tkind_equal(v1->cons_logic_type.Lstruct.template_kind,
          v2->cons_logic_type.Lstruct.template_kind);
    case LUNION:
      return qualified_name_equal(v1->cons_logic_type.Lunion.name,
          v2->cons_logic_type.Lunion.name)
        && tkind_equal(v1->cons_logic_type.Lunion.template_kind,
          v2->cons_logic_type.Lunion.template_kind);
    case LCNAMED:
      return qualified_name_equal(v1->cons_logic_type.LCnamed.name,
          v2->cons_logic_type.LCnamed.name);
    case LVARIABLE:
      return qualified_name_equal(v1->cons_logic_type.Lvariable.name,
          v2->cons_logic_type.Lvariable.name);
    case LNAMED:
      if (!qualified_name_equal(v1->cons_logic_type.Lnamed.name,
            v2->cons_logic_type.Lnamed.name))
        return false;
      { list l1 = v1->cons_logic_type.Lnamed.template_arguments,
             l2 = v2->cons_logic_type.Lnamed.template_arguments;
        while (l1 != NULL || l2 != NULL) {
          if (l1 == NULL || l2 == NULL)
            return false;
          if (!logic_type_equal((logic_type)l1->element.container,
                (logic_type)l2->element.container))
            return false;
          l1 = l1 -> next;
          l2 = l2 -> next;
        }
      }
      return true;
    case LARROW:
      { list l1 = v1->cons_logic_type.Larrow.left,
             l2 = v2->cons_logic_type.Larrow.left;
        while (l1 != NULL || l2 != NULL) {
          if (l1 == NULL || l2 == NULL)
            return false;
          if (!logic_type_compatible(
                (logic_type)l1->element.container,
                (logic_type)l2->element.container,
                context))
            return false;
          l1 = l1 -> next;
          l2 = l2 -> next;
        }
      }
      return logic_type_compatible(
        v1->cons_logic_type.Larrow.right,
        v2->cons_logic_type.Larrow.right,
        context);
    default:
      return false;
  }
  return false;
}

using namespace DLexer;

#if defined(__clang__) || defined(__GNUC__)
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wunused-label"
#endif

bool is_type_synonym(logic_type_info info) {
  option def = info->definition;
  return
    def->is_some &&
    ((logic_type_def)def->content.container)->tag_logic_type_def == LTSYN;
}

logic_type make_set_type(logic_type base_type) {
  return
    logic_type_Lnamed(
      qualified_name_cons(NULL,strdup("set")),true,
      cons_container(base_type,NULL));
}

logic_type remove_set_type(logic_type set_type) {
  assert(TermOrPredicate::isSetType(set_type));
  return
    (logic_type)
    set_type->cons_logic_type.Lnamed.template_arguments->element.container;
}

// Extract a definition. is_type_synonym(info) must be true.
logic_type extract_synonym_def(logic_type_info info) {
  option def = info -> definition;
  assert(def->is_some);
  logic_type_def ltdef = (logic_type_def)def->content.container;
  assert(ltdef->tag_logic_type_def == LTSYN);
  return ltdef->cons_logic_type_def.LTsyn.def;
}

logic_type from_c_named_type(
  const clang::NamedDecl* type, const Clang_utils* utils) {
  clang::Decl::Kind kind = type->getKind();
  assert (kind >= clang::Decl::firstType && kind <= clang::Decl::lastType);
  if (kind >= clang::Decl::firstTypedefName && 
      kind <= clang::Decl::lastTypedefName) {
    const clang::TypedefNameDecl* tidentifier =
      static_cast<const clang::TypedefNameDecl*>(type);
    return
      logic_type_LCnamed(
        utils-> makeQualifiedName(*tidentifier),
        utils->isExternCContext(tidentifier->getDeclContext()));
  } else {
    return
      utils->makeLogicType(
        type->getLocation(),
        static_cast<const clang::TypeDecl*>(type)->getTypeForDecl());
  }
}

Parser::ReadResult
LogicType::readToken(Parser::State& state, Parser::Arguments& arguments) {
  enum Delimiters
    { DBegin, DAfterLogicIdentifier, DAfterLogicAndCContextIdentifier,
      DAfterQualifiedLogicIdentifier, DAfterQualifiedLogicAndCContextIdentifier,
      DAfterCContextIdentifier, DAfterQualifiedCContextIdentifier,
      DCTypeSignedSuffix, DCTypeUnsignedSuffix, DCTypeSuffix, DTypeSuffix,
      DLogicTypeSuffix, DTypeSuffixArray,
      DTypeProduct, DTypeRecord, DTypeRecordItem, DTypeSumIdent, DEndTypeSum,
      DTypeConstructorParam
    };

  ReadResult result = RRNeedChars;
  switch (state.point()) {
    DefineParseCase(Begin)
      { AbstractToken token = arguments.queryToken();
        if (!_loc)
          absorbLoc(arguments.newTokenLocation());
        KeywordToken::Type prefixedToken = KeywordToken::TUndefined;
        if (token.getType() == AbstractToken::TKeyword) {
          KeywordToken::Type kw = ((const KeywordToken&) token).getType();
          if (kw == KeywordToken::TStruct || kw == KeywordToken::TClass || kw == KeywordToken::TUnion) {
            // A struct/union/class keyword at the beginning of a type is permitted but not necessary.
            // So we skip it if the next token is an identifier
            prefixedToken = kw;
            result = arguments.lexer().readToken();
            if (result == RRFinished) {
              DefineAddError("unexpected end of input after a struct/union/class token, beginning a type");
              return result;
            }
            token = arguments.queryToken();
            if (!_loc) absorbLoc(arguments.newTokenLocation());
            if (token.getType() != AbstractToken::TIdentifier) {
              DefineAddError("expected an identifier after the struct, union, or class token at the beginning of a type");
              return RRFinished;
            }
          }
        }
        switch (token.getType()) {
          case AbstractToken::TIdentifier:
            { std::string identifier = ((const IdentifierToken&)
                arguments.getContentToken()).content();

              bool hasFoundLogicQualification = false;
              arguments.extendLocationWithToken(_loc);
              if ((_qualification = arguments.findLogicName(identifier))
                  != NULL) {
                if (_qualification->ssons())
                  hasFoundLogicQualification = true;
              };
              const clang::TemplateArgument* templateArgument=NULL;
              const clang::NamedDecl* cidentifier
                  = arguments.isCodeName(identifier, &templateArgument);
              if (cidentifier) {
                clang::Decl::Kind kind = cidentifier->getKind();
                if (kind >= clang::Decl::firstRecord
                      && kind <= clang::Decl::lastRecord) {
                  const clang::RecordDecl* decl =
                    llvm::dyn_cast<clang::RecordDecl>(cidentifier);
                  assert(decl);
                  _declContext = decl;
                  switch (prefixedToken) {
                    case KeywordToken::TUndefined: break;
                    case KeywordToken::TUnion:
                      if (!decl->isUnion()) {
                        DefineAddError(identifier + " is not an union.");
                        return RRFinished;
                      }
                      break;
                    case KeywordToken::TStruct:
                    case KeywordToken::TClass:
                      if (!(decl->isStruct() || decl->isClass())) {
                        DefineAddError(
                          identifier + " is not a struct or class.");
                        return RRFinished;
                      }
                      break;
                    default: break;
                  }

                  if (!hasFoundLogicQualification)
                    DefineGotoCase(AfterCContextIdentifier)
                  else
                    DefineGotoCase(AfterLogicAndCContextIdentifier)
                };
                if (kind >= clang::Decl::firstType
                      && kind <= clang::Decl::lastType) {
                  if (prefixedToken != KeywordToken::TUndefined) {
                    DefineAddError(
                      identifier + " is not a struct, class, or union.");
                    return RRFinished;
                  }
                  if (hasFoundLogicQualification) /* else issue a conflict */
                    DefineGotoCase(AfterLogicIdentifier);
                  _typeResult =
                    from_c_named_type(cidentifier,arguments.get_clang_utils());
                  DefineGotoCase(TypeSuffix)
                };
                if ((kind >= clang::Decl::firstTemplate
                      && kind <= clang::Decl::lastTemplate)
                    || kind == clang::Decl::NonTypeTemplateParm) {
                  DefineAddError(
                    "unsupported: templates in logic annotations");
                  return RRFinished;
                  // the following is completely false: we have Foo<Bar> in
                  // ACSL++ and translate it as Bar in IR...
                  // assert(templateArgument);
                  // switch (templateArgument->getKind()) {
                  //  case clang::TemplateArgument::Type:
                  //    _typeResult =
                  //      arguments.get_clang_utils()->makeLogicType(
                  //        arguments.tokenSourceLocation(),
                  //        templateArgument->getAsType().getTypePtr());
                  //    DefineGotoCase(TypeSuffix)
                  //  default:
                  //    break;
                  // };
                };
                if (prefixedToken != KeywordToken::TUndefined) {
                  DefineAddError(
                    identifier + " is a namespace.");
                  return RRFinished;
                }
                switch (kind) {
                  // case clang::Decl::Label:
                  case clang::Decl::Namespace:
                    assert(llvm::dyn_cast<clang::NamespaceDecl>(cidentifier));
                    _declContext = static_cast<const clang::NamespaceDecl*>(
                        cidentifier);
                    if (!hasFoundLogicQualification)
                      DefineGotoCase(AfterCContextIdentifier)
                    else
                      DefineGotoCase(AfterLogicAndCContextIdentifier)
                  case clang::Decl::NamespaceAlias:
                    assert(llvm::dyn_cast<clang::NamespaceAliasDecl>(
                          cidentifier));
                    _declContext = static_cast<const clang::NamespaceAliasDecl*>
                      (cidentifier)->getNamespace();
                    if (!hasFoundLogicQualification)
                      DefineGotoCase(AfterCContextIdentifier)
                    else
                      DefineGotoCase(AfterLogicAndCContextIdentifier);
                  default:
                    break;
                };
              };
              if (hasFoundLogicQualification)
                DefineGotoCase(AfterLogicIdentifier);
              if (_qualification) {
                if (_qualification->isLogicType()) {
                  logic_type_info ti =
                    _qualification->asLogicType().type_info();
                  _typeResult =
                    logic_type_Lnamed(
                      qualified_name_dup(ti->type_name), ti->is_extern_c, NULL);
                  DefineGotoCase(LogicTypeSuffix)
                };
                DefineGotoCase(AfterLogicIdentifier)
              };
              _typeResult = logic_type_Linteger();
              DefineAddError(std::string("unknown identifier '")
                  .append(identifier).append("'"));
              DefineReduce
            };
            break;
          case AbstractToken::TKeyword:
            switch (((const KeywordToken&) token).getType()) {
              case KeywordToken::TBool:
                _typeResult = logic_type_Lint(IBOOL);
                arguments.extendLocationWithToken(_loc);
                DefineGotoCase(TypeSuffix)
              case KeywordToken::TChar:
                _typeResult = logic_type_Lint(ICHAR);
                arguments.extendLocationWithToken(_loc);
                DefineGotoCase(CTypeSuffix)
              case KeywordToken::TChar16:
                _typeResult = logic_type_Lint(ICHAR16);
                arguments.extendLocationWithToken(_loc);
                DefineGotoCase(CTypeSuffix)
              case KeywordToken::TChar32:
                _typeResult = logic_type_Lint(ICHAR32);
                arguments.extendLocationWithToken(_loc);
                DefineGotoCase(CTypeSuffix);
              case KeywordToken::TConst:
              case KeywordToken::TVolatile:
                // don't know how to translate this in logic_type _typeResult
                DefineGotoCase(Begin)
              case KeywordToken::TDouble:
                _typeResult = logic_type_Lfloat(FDOUBLE);
                arguments.extendLocationWithToken(_loc);
                DefineGotoCase(CTypeSuffix)
              case KeywordToken::TFloat:
                _typeResult = logic_type_Lfloat(FFLOAT);
                arguments.extendLocationWithToken(_loc);
                DefineGotoCase(TypeSuffix)
              case KeywordToken::TInt:
                _typeResult = logic_type_Lint(IINT);
                _seenInt = true;
                arguments.extendLocationWithToken(_loc);
                DefineGotoCase(CTypeSuffix)
              case KeywordToken::TLong:
                _typeResult = logic_type_Lint(ILONG);
                arguments.extendLocationWithToken(_loc);
                DefineGotoCase(CTypeSuffix)
              case KeywordToken::TShort:
                _typeResult = logic_type_Lint(ISHORT);
                arguments.extendLocationWithToken(_loc);
                DefineGotoCase(CTypeSuffix)
              case KeywordToken::TSigned:
                _typeResult = logic_type_Lint(IINT);
                _seenSigned = true;
                arguments.extendLocationWithToken(_loc);
                DefineGotoCase(CTypeSuffix)
              case KeywordToken::TUnsigned:
                _typeResult = logic_type_Lint(IUINT);
                arguments.extendLocationWithToken(_loc);
                DefineGotoCase(CTypeSuffix)
              case KeywordToken::TVoid:
                _typeResult = logic_type_Lvoid();
                arguments.extendLocationWithToken(_loc);
                DefineGotoCase(TypeSuffix)
              case KeywordToken::TInteger:
                _typeResult = logic_type_Linteger();
                arguments.extendLocationWithToken(_loc);
                DefineGotoCase(LogicTypeSuffix)
              case KeywordToken::TReal:
                _typeResult = logic_type_Lreal();
                arguments.extendLocationWithToken(_loc);
                DefineGotoCase(LogicTypeSuffix)
              case KeywordToken::TBoolean:
                _typeResult = arguments.boolean_type();
                arguments.extendLocationWithToken(_loc);
                DefineGotoCase(LogicTypeSuffix)
              case KeywordToken::TWcharT:
                _typeResult = logic_type_Lint(IWCHAR);
                arguments.extendLocationWithToken(_loc);
                DefineGotoCase(CTypeSuffix)
              default:
                break;
            };
            { std::ostringstream outToken;
              arguments.lexer().assumeContentToken();
              arguments.getContentToken().write(outToken,
                  AbstractToken::PersistentFormat().setPretty());
              DefineAddError(std::string("keyword '")
                  .append(outToken.str())
                  .append("' encountered when parsing a type"));
            };
            DefineReduce
          case AbstractToken::TOperatorPunctuator:
            { OperatorPunctuatorToken::Type type
                = ((const OperatorPunctuatorToken&) token).getType();
              switch (type) {
                case OperatorPunctuatorToken::TOpenParen:
                  DefineAddError("product type is not implemented");
                  { LogicType* rule = new LogicType;
                    state.absorbRuleResult(rule);
                    DefineShift(TypeProduct, *rule, &LogicType::readToken);
                  };
                case OperatorPunctuatorToken::TOpenBrace:
                  DefineAddError("record type is not implemented");
                  { LogicType* rule = new LogicType;
                    state.absorbRuleResult(rule);
                    DefineShift(TypeRecord, *rule, &LogicType::readToken);
                  };
                case OperatorPunctuatorToken::TBitOr:
                  if (_superTypeName) {
                    _typedefResult = logic_type_def_LTsum(NULL);
                    DefineGotoCase(TypeSumIdent);
                  };
                default:
                  break;
              };
            };
          default:
            break;
        };
        { 
          arguments.lexer().assumeContentToken();
          DefineAddError(std::string("unexpected token '")
                    .append(arguments.getContentToken().str())
                    .append("' when starting to parse a type"));
        };
        DefineReduce;
      };
    DefineParseCase(AfterLogicIdentifier)
      { AbstractToken token = arguments.queryToken();
        if (token.getType() == AbstractToken::TOperatorPunctuator) {
          if (((const OperatorPunctuatorToken&) token).getType()
              == OperatorPunctuatorToken::TColonColon) {
            if (_qualification && !_qualification->ssons()) {
              std::string errorMessage = "unknown logic qualification ";
              errorMessage.append(_qualification->getName());
              DefineAddError(errorMessage)
            };
            DefineGotoCase(AfterQualifiedLogicIdentifier)
          };
        };
        std::string errorMessage = "unable to build a type from qualification ";
        errorMessage.append(_qualification->getName());
        DefineAddError(errorMessage)
        DefineReduceAndParse
      };
    DefineParseCase(AfterLogicAndCContextIdentifier)
      { AbstractToken token = arguments.queryToken();
        if (token.getType() == AbstractToken::TOperatorPunctuator) {
          if (((const OperatorPunctuatorToken&) token).getType()
              == OperatorPunctuatorToken::TColonColon) {
            if (_qualification && !_qualification->ssons()) {
              _qualification = NULL;
              DefineGotoCase(AfterQualifiedCContextIdentifier)
            }
            DefineGotoCase(AfterQualifiedLogicAndCContextIdentifier)
          };
        };
        if (_declContext->isRecord()) {
          const clang::RecordDecl* recordDecl =
            static_cast<const clang::RecordDecl*>(_declContext);
          _typeResult =
            arguments.get_clang_utils()->makeLogicType(
              arguments.tokenSourceLocation(),
              recordDecl->getTypeForDecl());
          DefineGotoCaseAndParse(TypeSuffix)
        };
        std::string errorMessage = "unable to build a type from qualification ";
        errorMessage.append(_qualification->getName());
        DefineAddError(errorMessage)
        DefineReduceAndParse
      };
    DefineParseCase(AfterQualifiedLogicIdentifier)
      if (arguments.queryToken().getType() == AbstractToken::TIdentifier) {
        const std::string& identifier = ((const IdentifierToken&)
            arguments.getContentToken()).content();
        assert(_qualification && _qualification->ssons());
        GlobalContext::NestedContext locateSon(identifier);
        const GlobalContext::NestedContext::SonsSet& sons =
          *_qualification->ssons();
        GlobalContext::NestedContext::SonsSet::const_iterator found =
          sons.find(&locateSon);
        if (found != sons.end()) {
          _qualification = *found;
          if (_qualification->ssons())
            DefineGotoCase(AfterLogicIdentifier)
          if (_qualification->isLogicType()) {
            logic_type_info ti = _qualification->asLogicType().type_info();
            _typeResult =
              logic_type_Lnamed(
                qualified_name_dup(ti->type_name),ti->is_extern_c,NULL);
            arguments.extendLocationWithToken(_loc);
            DefineGotoCase(LogicTypeSuffix)
          };
        };
        arguments.extendLocationWithToken(_loc);
        DefineAddError(std::string("identifier '").append(identifier)
            .append("' does not appear to be a type"));
        DefineTReduce
      };
      arguments.extendLocationWithToken(_loc);
      DefineAddError(std::string("expecting idendifier "
            "after parsing a qualification '::'"));
      DefineTReduce
    DefineParseCase(AfterQualifiedLogicAndCContextIdentifier)
      if (arguments.queryToken().getType() == AbstractToken::TIdentifier) {
        const std::string& identifier = ((const IdentifierToken&)
            arguments.getContentToken()).content();
        assert(_qualification && _qualification->ssons() && _declContext);
        GlobalContext::NestedContext locateSon(identifier);
        const GlobalContext::NestedContext::SonsSet& sons =
          *_qualification->ssons();
        GlobalContext::NestedContext::SonsSet::const_iterator found =
          sons.find(&locateSon);
        bool hasFoundLogicQualification = false;
        if (found != sons.end()) {
          _qualification = *found;
          if (_qualification->ssons())
            hasFoundLogicQualification = true;
          if (_qualification->isLogicType()) {
            logic_type_info ti = _qualification->asLogicType().type_info();
            _typeResult =
              logic_type_Lnamed(
                qualified_name_dup(ti->type_name),ti->is_extern_c,NULL);
            arguments.extendLocationWithToken(_loc);
            DefineGotoCase(LogicTypeSuffix)
          };
        };

        const clang::NamedDecl* cidentifier = arguments.findQualifiedName(
            identifier, _declContext);
        if (cidentifier) {
          clang::Decl::Kind kind = cidentifier->getKind();
          if (kind >= clang::Decl::firstRecord
                && kind <= clang::Decl::lastRecord) {
            assert(llvm::dyn_cast<clang::RecordDecl>(cidentifier));
            _declContext = static_cast<const clang::RecordDecl*>(cidentifier);
            arguments.extendLocationWithToken(_loc);
            if (!hasFoundLogicQualification)
              DefineGotoCase(AfterCContextIdentifier)
            else
              DefineGotoCase(AfterLogicAndCContextIdentifier);
          };
          if (kind >= clang::Decl::firstType && kind <= clang::Decl::lastType) {
            if (hasFoundLogicQualification)
              DefineGotoCase(AfterLogicIdentifier);
            _typeResult =
              from_c_named_type(cidentifier,arguments.get_clang_utils());
            arguments.extendLocationWithToken(_loc);
            DefineGotoCase(TypeSuffix)
          };
          
          switch (kind) {
            // case clang::Decl::Label:
            case clang::Decl::Namespace:
              assert(llvm::dyn_cast<clang::NamespaceDecl>(cidentifier));
              _declContext = static_cast<const clang::NamespaceDecl*>(
                  cidentifier);
              if (!hasFoundLogicQualification)
                DefineGotoCase(AfterCContextIdentifier)
              else
                DefineGotoCase(AfterLogicAndCContextIdentifier);
            case clang::Decl::NamespaceAlias:
              assert(llvm::dyn_cast<clang::NamespaceAliasDecl>(cidentifier));
              _declContext = static_cast<const clang::NamespaceAliasDecl*>(
                  cidentifier)->getNamespace();
              if (!hasFoundLogicQualification)
                DefineGotoCase(AfterCContextIdentifier)
              else
                DefineGotoCase(AfterLogicAndCContextIdentifier)
            default:
              break;
          };
        };
        if (hasFoundLogicQualification)
          DefineGotoCase(AfterLogicIdentifier);
        arguments.extendLocationWithToken(_loc);
        DefineAddError(std::string("identifier '").append(identifier)
            .append("' does not appear to be a type"));
        DefineTReduce
      };
      arguments.extendLocationWithToken(_loc);
      DefineAddError(std::string("expecting idendifier "
            "after parsing a qualification '::'"));
      DefineTReduce
    DefineParseCase(AfterCContextIdentifier)
      { AbstractToken token = arguments.queryToken();
        if (token.getType() == AbstractToken::TOperatorPunctuator) {
          if (((const OperatorPunctuatorToken&) token).getType()
              == OperatorPunctuatorToken::TColonColon)
            DefineGotoCase(AfterQualifiedCContextIdentifier)
        };
        if (_declContext->isRecord()) {
          const clang::RecordDecl* recordDecl =
            static_cast<const clang::RecordDecl*>(_declContext);
          _typeResult =
            arguments.get_clang_utils()->makeLogicType(
              arguments.tokenSourceLocation(),
              recordDecl->getTypeForDecl());
          DefineGotoCaseAndParse(TypeSuffix)
        };
        std::string errorMessage = "unable to build a C/C++ type "
          "from qualification ";
        errorMessage.append(_qualification->getName());
        DefineAddError(errorMessage)
        DefineReduceAndParse
      };
    DefineParseCase(AfterQualifiedCContextIdentifier)
      if (arguments.queryToken().getType() == AbstractToken::TIdentifier) {
        const std::string& identifier = ((const IdentifierToken&)
            arguments.getContentToken()).content();
        assert(_declContext);
        const clang::NamedDecl* cidentifier = arguments.findQualifiedName(
            identifier, _declContext);
        if (cidentifier) {
          clang::Decl::Kind kind = cidentifier->getKind();
          if (kind >= clang::Decl::firstRecord
                && kind <= clang::Decl::lastRecord) {
            assert(llvm::dyn_cast<clang::RecordDecl>(cidentifier));
            _declContext = static_cast<const clang::RecordDecl*>(cidentifier);
            arguments.extendLocationWithToken(_loc);
            DefineGotoCase(AfterCContextIdentifier);
          };
          if (kind >= clang::Decl::firstType && kind <= clang::Decl::lastType) {
            _typeResult =
              from_c_named_type(cidentifier,arguments.get_clang_utils());
            arguments.extendLocationWithToken(_loc);
            DefineGotoCase(TypeSuffix)
          };
          
          switch (kind) {
            // case clang::Decl::Label:
            case clang::Decl::Namespace:
              assert(llvm::dyn_cast<clang::NamespaceDecl>(cidentifier));
              _declContext = static_cast<const clang::NamespaceDecl*>(
                  cidentifier);
              DefineGotoCase(AfterCContextIdentifier);
            case clang::Decl::NamespaceAlias:
              assert(llvm::dyn_cast<clang::NamespaceAliasDecl>(cidentifier));
              _declContext = static_cast<const clang::NamespaceAliasDecl*>(
                  cidentifier)->getNamespace();
              DefineGotoCase(AfterCContextIdentifier);
            default:
              break;
          };
        };
        DefineAddError(std::string("unknown identifier '").append(identifier)
            .append("'"));
        DefineReduce
      };
      DefineAddError(std::string("expecting type idendifier "
            "after parsing a qualification '::'"));
      DefineReduce
    DefineParseCase(CTypeSuffix) {// there might be more than one C specifier
        AbstractToken token = arguments.queryToken();
        if (token.getType() == AbstractToken::TKeyword) {
          switch (((const KeywordToken&) token).getType()) {
            case KeywordToken::TChar: {
              // can only be mixed with signed and unsigned
              if (unspecifiedKind()) {
                if (_typeResult->cons_logic_type.Lint.kind == IINT)
                  _typeResult->cons_logic_type.Lint.kind =
                    _seenSigned?ISCHAR:ICHAR;
                else
                  _typeResult->cons_logic_type.Lint.kind = IUCHAR;
                arguments.extendLocationWithToken(_loc);
                DefineGotoCase(TypeSuffix) }
              else {
                DefineAddError(
                  "conflicting C type specification in logic type: char");
                DefineReduceAndParse
              }
            }
            case KeywordToken::TConst:
            case KeywordToken::TVolatile:
              // just ignore these arguments, they are irrelevant in the logic
              arguments.extendLocationWithToken(_loc);
              DefineGotoCase(CTypeSuffix)
            case KeywordToken::TInt: {
                // can be mixed with long, short, unsigned, and signed
                if (_typeResult->tag_logic_type == LINT) {
                  if (_seenInt) {
                    DefineAddErrorAndParse(
                      "duplicated 'int' type specification")
                  }
                  switch (_typeResult->cons_logic_type.Lint.kind) {
                    case ISHORT:
                    case IUSHORT:
                    case IINT:
                    case IUINT:
                    case ILONG:
                    case IULONG:
                    case ILONGLONG:
                    case IULONGLONG:
                      break;
                    default:
                      DefineAddErrorAndParse(
                        "unexpected 'int' type specification")
                  }
                  _seenInt = true;
                  arguments.extendLocationWithToken(_loc);
                  DefineGotoCase(CTypeSuffix)
                } else {
                  DefineAddErrorAndParse(
                    "conflicting C type specification in logic type: int")
                }
            }
            case KeywordToken::TUnsigned: {
              if (_seenSigned) {
                DefineAddErrorAndParse(
                  "mixing signed and unsigned type specification")
              } else if (_typeResult->tag_logic_type == LFLOAT) {
                DefineAddErrorAndParse(
                  "'unsigned' meaningless for floating point")
              } else {
                switch (_typeResult->cons_logic_type.Lint.kind) {
                  case IBOOL:
                    DefineAddErrorAndParse("'unsigned' meaningless for boolean")
                  case ICHAR16:
                    DefineAddErrorAndParse("'unsigned' meaningless for char16_t")
                  case ICHAR32:
                    DefineAddErrorAndParse("'unsigned' meaningless for char32_t")
                  case IUCHAR:
                  case IWUCHAR:
                  case IUSHORT:
                  case IUINT:
                  case IULONG:
                  case IULONGLONG:
                    DefineAddErrorAndParse("found 'unsigned' twice")
                  case ICHAR:
                    _typeResult->cons_logic_type.Lint.kind = IUCHAR;
                    break;
                  case IWCHAR:
                    _typeResult->cons_logic_type.Lint.kind = IWUCHAR;
                    break;
                  case ISHORT:
                    _typeResult->cons_logic_type.Lint.kind = IUSHORT;
                    break;
                  case ILONG:
                    _typeResult->cons_logic_type.Lint.kind = IULONG;
                    break;
                  case ILONGLONG:
                    _typeResult->cons_logic_type.Lint.kind = IULONGLONG;
                    break;
                  default:
                    // architecture dependent char types. can't be generated
                    assert(false);
                }
                arguments.extendLocationWithToken(_loc);
                DefineGotoCase(CTypeSuffix)
              }
            }
            case KeywordToken::TSigned: {
              if (_seenSigned) {
                DefineAddErrorAndParse("duplicated signed type specification")
              } else if (_typeResult->tag_logic_type == LFLOAT) {
                DefineAddErrorAndParse(
                  "'signed' meaningless for floating point")
              } else {
                switch (_typeResult->cons_logic_type.Lint.kind) {
                  case IBOOL:
                    DefineAddErrorAndParse("'signed' meaningless for boolean")
                  case ICHAR16:
                    DefineAddErrorAndParse("'signed' meaningless for char16_t")
                  case ICHAR32:
                    DefineAddErrorAndParse("'signed' meaningless for char32_t")
                  case IUCHAR:
                  case IWUCHAR:
                  case IUSHORT:
                  case IUINT:
                  case IULONG:
                  case IULONGLONG:
                    DefineAddErrorAndParse(
                      "mixing 'signed' and 'unsigned' in type specification")
                  case ICHAR:
                  case IWCHAR:
                  case ISHORT:
                  case ILONG:
                  case ILONGLONG:
                    break;
                  default: 
                    // architecture dependent char types. can't be generated
                    assert(false);
                }
                _seenSigned = true;
                arguments.extendLocationWithToken(_loc);
              }
              DefineGotoCase(CTypeSuffix)
            }
            case KeywordToken::TLong: {
              if (_typeResult->tag_logic_type == LFLOAT) {
                switch(_typeResult->cons_logic_type.Lfloat.kind) {
                  case FFLOAT:
                    DefineAddErrorAndParse(
                      "unexpected 'long' specification for a float")
                  case FDOUBLE:
                    _typeResult->cons_logic_type.Lfloat.kind = FLONGDOUBLE;
                    DefineGotoCase(TypeSuffix)
                  case FLONGDOUBLE:
                    DefineAddErrorAndParse(
                      "cannot have long long double type in Frama-Clang")
                }
              } else { // integer type
                switch(_typeResult->cons_logic_type.Lint.kind) {
                  case IINT:
                    _typeResult->cons_logic_type.Lint.kind = ILONG;
                    break;
                  case IUINT:
                    _typeResult->cons_logic_type.Lint.kind = IULONG;
                    break;
                  case ILONG:
                    _typeResult->cons_logic_type.Lint.kind = ILONGLONG;
                    break;
                  case IULONG:
                    _typeResult->cons_logic_type.Lint.kind = IULONGLONG;
                    break;
                  case ILONGLONG:
                  case IULONGLONG:
                    DefineAddErrorAndParse(
                      "long long long integer type does not exist")
                  default:
                    DefineAddErrorAndParse(
                      "unexpected 'long' type specification")
                }
                arguments.extendLocationWithToken(_loc);
              }
              DefineGotoCase(CTypeSuffix)
            }
            case KeywordToken::TShort: {
              // can only be mixed with signed, unsigned, and int
              if (unspecifiedKind()) {
                if (_typeResult->cons_logic_type.Lint.kind == IUINT)
                  _typeResult->cons_logic_type.Lint.kind = IUSHORT;
                else
                  _typeResult->cons_logic_type.Lint.kind = ISHORT;
                arguments.extendLocationWithToken(_loc);
                DefineGotoCase(CTypeSuffix)
              }
              else
                DefineAddErrorAndParse(
                  "unexpected 'short' type specification")
            }
            case KeywordToken::TDouble: {
              // only possibility is 'long double'
              if (_typeResult->tag_logic_type == LINT &&
                  _typeResult->cons_logic_type.Lint.kind == ILONG) {
                free_logic_type(_typeResult);
                _typeResult=logic_type_Lfloat(FLONGDOUBLE);
                arguments.extendLocationWithToken(_loc);
                DefineGotoCase(TypeSuffix)
              } else {
                DefineAddErrorAndParse(
                  "unexpected 'double' type specification")
              }
            }
            default:
              DefineGotoCaseAndParse(TypeSuffix)
         }
        }
        else
          DefineGotoCaseAndParse(TypeSuffix)
    }
    DefineParseCase(TypeSuffix)
      { AbstractToken token = arguments.queryToken();
        if (!_doesStopSuffix
              && token.getType() == AbstractToken::TOperatorPunctuator) {
          OperatorPunctuatorToken::Type
              type = ((const OperatorPunctuatorToken&) token).getType();
          if (type == OperatorPunctuatorToken::TStar) {
            _typeResult = logic_type_Lpointer(_typeResult);
            arguments.extendLocationWithToken(_loc);
            DefineGotoCase(TypeSuffix)
          };
          if (type == OperatorPunctuatorToken::TAmpersand) {
            _typeResult = logic_type_Lreference(_typeResult);
            arguments.extendLocationWithToken(_loc);
            DefineGotoCase(TypeSuffix)
          };
          if (type == OperatorPunctuatorToken::TOpenBracket) {
            TermOrPredicate* subTerm = new TermOrPredicate;
            state.absorbRuleResult(&subTerm->setTerm());
            arguments.extendLocationWithToken(_loc);
            DefineShift(TypeSuffixArray, *subTerm, &TermOrPredicate::readToken)
          };
        }
        else if (token.getType() == AbstractToken::TKeyword) {
          KeywordToken::Type type = ((const KeywordToken&) token).getType();
          if (type == KeywordToken::TConst || type == KeywordToken::TVolatile) {
            arguments.extendLocationWithToken(_loc);
            DefineGotoCase(CTypeSuffix)
          };
        };
      }
      DefineReduceAndParse
    DefineParseCase(LogicTypeSuffix)
      { AbstractToken token = arguments.queryToken();
        if (!_doesStopSuffix
            && token.getType() == AbstractToken::TOperatorPunctuator) {
          OperatorPunctuatorToken::Type
            type = ((const OperatorPunctuatorToken&) token).getType();
          if (type == OperatorPunctuatorToken::TStar) {
            DefineAddError("pointers cannot point onto a logic type");
            _typeResult = logic_type_Lpointer(_typeResult);
            arguments.extendLocationWithToken(_loc);
            DefineGotoCase(LogicTypeSuffix)
          };
          if (type == OperatorPunctuatorToken::TAmpersand) {
            DefineAddError("references cannot reference a logic type");
            _typeResult = logic_type_Lreference(_typeResult);
            arguments.extendLocationWithToken(_loc);
            DefineGotoCase(LogicTypeSuffix)
          };
          if (type == OperatorPunctuatorToken::TOpenBracket) {
            TermOrPredicate* subTerm = new TermOrPredicate;
            state.absorbRuleResult(&subTerm->setTerm());
            arguments.extendLocationWithToken(_loc);
            DefineShift(TypeSuffixArray, *subTerm, &TermOrPredicate::readToken)
          };
        }
        else if (token.getType() == AbstractToken::TKeyword) {
          KeywordToken::Type type = ((const KeywordToken&) token).getType();
          if (type == KeywordToken::TConst || type == KeywordToken::TVolatile) {
            arguments.extendLocationWithToken(_loc);
            DefineGotoCase(LogicTypeSuffix)
          };
        };
      }
      DefineReduceAndParse
    DefineParseCase(TypeSuffixArray)
      { AbstractToken token = arguments.queryToken();
        if (token.getType() == AbstractToken::TOperatorPunctuator
            && (((const OperatorPunctuatorToken&) token).getType()
              == OperatorPunctuatorToken::TCloseBracket)) {
          // int intResult = 0; double doubleResult = 0;
          logic_type ltype = NULL;
          term termNode = NULL;
          std::string dimension = "0";
          // bool isRValue = false;
          { Parser::State::RuleAccess::TCastFromRule<TermOrPredicate>
              subterm(state.getRuleResult());
            // bool isConstant = false; // [TODO] activate it!
            termNode = subterm->extractTerm(arguments, ltype);
            state.freeRuleResult();
          };
          // if (!isRValue) {
          //   // term_lval_cons ...
          //   // term_node = term_node_TLval(lval)
          // };
          if (!ltype || !termNode) {
            if (arguments.doesStopAfterTooManyErrors())
              return RRFinished;
            DefineReduceAndParse
          };
          assert(false); // unimplemented
          _typeResult =
            logic_type_Larray(
              _typeResult,
              opt_some_container(logic_constant_LCInt(dimension.c_str())));
          DefineGotoCase(CTypeSuffix)
          DefineTReduce
        };
      };
      { std::ostringstream outToken;
        arguments.lexer().assumeContentToken();
        arguments.getContentToken().write(outToken,
            AbstractToken::PersistentFormat().setPretty());
        DefineAddError(std::string("unexpected token '")
            .append(outToken.str())
            .append("' when parsing the dimension of a cast "
              "with a logic array type"));
      };
      DefineGotoCase(TypeSuffixArray)
    DefineParseCase(TypeProduct)
      // TODO only the parsing rules are correct. Type products are not
      // implemented in the IR.
      { Parser::State::RuleAccess::TCastFromRule<LogicType>
            subtype(state.getRuleResult());
        // ...
        state.freeRuleResult();
        AbstractToken token = arguments.queryToken();
        if (token.getType() == AbstractToken::TOperatorPunctuator) {
          OperatorPunctuatorToken::Type type
              = ((const OperatorPunctuatorToken&) token).getType();
          if (type == OperatorPunctuatorToken::TCloseParen) {
            _typeResult = logic_type_Linteger();
            arguments.extendLocationWithToken(_loc);
            DefineGotoCase(LogicTypeSuffix)
          };
          if (type == OperatorPunctuatorToken::TComma) {
            state.absorbRuleResult(new LogicType);
            DefineGotoCase(TypeProduct)
          };
        };
        std::ostringstream outToken;
        arguments.lexer().assumeContentToken();
        arguments.getContentToken().write(outToken,
            AbstractToken::PersistentFormat().setPretty());
        DefineAddError(std::string("unexpected token '")
            .append(outToken.str())
            .append("' when parsing a product type"));
      };
      DefineReduceAndParse
    DefineParseCase(TypeRecord)
      //TODO only the parsing rules are correct. Records are not implemented
      //in the IR
      { Parser::State::RuleAccess::TCastFromRule<LogicType>
            subtype(state.getRuleResult());
        // ...
        state.freeRuleResult();
        if (arguments.queryToken().getType() == AbstractToken::TIdentifier) {
          //const std::string& identifier =
          //  ((const IdentifierToken&) arguments.getContentToken()).content();
          DefineGotoCase(TypeRecordItem)
        };
        DefineAddError("expecting identifier when parsing a record type");
      };
      DefineGotoCaseAndParse(TypeRecordItem)
    DefineParseCase(TypeRecordItem)
      { AbstractToken token = arguments.queryToken();
        token = arguments.queryToken();
        if (token.getType() == AbstractToken::TOperatorPunctuator) {
          OperatorPunctuatorToken::Type type
              = ((const OperatorPunctuatorToken&) token).getType();
          if (type == OperatorPunctuatorToken::TCloseBrace) {
            _typeResult = logic_type_Linteger();
            arguments.extendLocationWithToken(_loc);
            DefineGotoCase(LogicTypeSuffix)
          };
          if (type == OperatorPunctuatorToken::TSemiColon) {
            state.absorbRuleResult(new LogicType);
            DefineGotoCase(TypeProduct)
          };
        };
        std::ostringstream outToken;
        arguments.lexer().assumeContentToken();
        arguments.getContentToken().write(outToken,
            AbstractToken::PersistentFormat().setPretty());
        DefineAddError(std::string("unexpected token '")
            .append(outToken.str())
            .append("' when parsing a record type"));
      };
      DefineGotoCase(TypeRecordItem)
    DefineParseCase(TypeSumIdent)
      if (arguments.queryToken().getType() == AbstractToken::TIdentifier) {
        _sumIdentifier = ((const IdentifierToken&)
            arguments.getContentToken()).content();
        DefineGotoCase(EndTypeSum)
      };
      DefineAddError("expecting identifier when parsing a sum type");
      DefineGotoCaseAndParse(EndTypeSum)
    DefineParseCase(EndTypeSum)
      { assert(_superTypeName);
        bool is_extern_c = arguments.isExternCContext();
        /* logic_ctor_info */ list* endSum = &_typedefResult
            ->cons_logic_type_def.LTsum.arguments;
        while (*endSum)
          endSum = &(*endSum)->next;
        
        *endSum =
          cons_container(
            logic_ctor_info_cons(
              qualified_name_cons(NULL, strdup(_sumIdentifier.c_str())),
              is_extern_c,
              qualified_name_dup(_superTypeName), NULL), NULL);
        _sumIdentifier = "";
        AbstractToken token = arguments.queryToken();
        token = arguments.queryToken();
        if (token.getType() == AbstractToken::TOperatorPunctuator) {
          OperatorPunctuatorToken::Type type
            = ((const OperatorPunctuatorToken&) token).getType();
          if (type == OperatorPunctuatorToken::TOpenParen) {
            LogicType* rule = new LogicType;
            state.absorbRuleResult(rule);
            DefineShift(TypeConstructorParam, *rule, &LogicType::readToken);
          };
          if (type == OperatorPunctuatorToken::TBitOr)
            DefineGotoCase(TypeSumIdent)
        };
      };
      DefineReduceAndParse
    DefineParseCase(TypeConstructorParam)
      { Parser::State::RuleAccess::TCastFromRule<LogicType>
            definition(state.getRuleResult());
        /* logic_ctor_info */ list*
            endSum = &_typedefResult->cons_logic_type_def.LTsum.arguments;
        while (*endSum)
          endSum = &(*endSum)->next;
        /* logic_type */ list* locationParams =
            &((logic_ctor_info) (*endSum)->element.container)->ctor_params;
        while (*locationParams)
          locationParams = &(*locationParams)->next;
        (*locationParams) = cons_container(definition->extractType(), NULL);
        state.freeRuleResult();
        AbstractToken token = arguments.queryToken();
        if (token.getType() == AbstractToken::TOperatorPunctuator) {
          OperatorPunctuatorToken::Type
              type = ((const OperatorPunctuatorToken&) token).getType();
          if (type == OperatorPunctuatorToken::TComma) {
            LogicType* rule = new LogicType;
            state.absorbRuleResult(rule);
            DefineShift(TypeConstructorParam, *rule, &LogicType::readToken);
          };
          if (type == OperatorPunctuatorToken::TCloseParen)
            DefineGotoCase(EndTypeSum)
        };
      };
      DefineAddError("expecting ',' or ')' in the parameters of a sum type");
      DefineGotoCase(TypeConstructorParam)
  };
  return result;
}

std::string str(logic_type typ) {
  std::string n;
  tag_logic_type tag = typ->tag_logic_type;
  if (tag == LINTEGER) return "integer";
  if (tag == LREAL) return "real";
  if (tag == LINT) return "int#";
  if (tag == LFLOAT) {
    auto tagf = typ->cons_logic_type.Lfloat.kind;
    if (tagf == FDOUBLE) return "double";
    if (tagf == FFLOAT) return "float";
  }
  return  "????";
}

std::string str(list typs) {
  std::ostringstream s;
  while (typs) {
    logic_type curr_type =
            ((logic_arg_decl)typs->element.container)->la_type;
    s << str(curr_type) << " ";
    typs = typs->next;
  }
  return s.str();
}


#if defined(__clang__) || defined(__GNUC__)
#pragma GCC diagnostic pop
#endif

} // end of namespace Acsl

