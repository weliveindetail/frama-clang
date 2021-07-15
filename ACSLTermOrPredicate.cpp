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
//   Implementation of the ACSL terms and predicates.
//

#include "ACSLTermOrPredicate.h"
#include "clang/AST/DeclTemplate.h"

namespace Acsl {

using namespace DLexer;

#if defined(__clang__) || defined(__GNUC__)
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wunused-label"
#endif

std::string
TermOrPredicate::Operator::queryOperatorName() const {
  switch (_type) {
    case TPlus: return "+";
    case TMinus: return "-";
    case TTimes: return "*";
    case TDivide: return "/";
    case TModulo: return "%";
    case TLeftShift: return "<<";
    case TRightShift: return ">>";
    case TEqual: return "==";
    case TDifferent: return "!=";
    case TLessOrEqual: return "<=";
    case TGreaterOrEqual: return ">=";
    case TLess: return "<";
    case TGreater: return ">";
    case TLogicalAnd: return "&&";
    case TLogicalOr: return "||";
    case TLogicalImply: return "==>";
    case TLogicalEquiv: return "<==>";
    case TLogicalXOr: return "^^";
    case TBitAnd: return "&";
    case TBitOr: return "|";
    case TBitImply: return "-->";
    case TBitEquiv: return "<-->";
    case TBitXOr: return "^";
    case TUnaryPlus: return "+";
    case TUnaryMinus: return "-";
    case TNot: return "!";
    case TComplement: return "~";
    case TDereference: return "*";
    case TAddressOf: return "&";
    case TCast: return "(cast)";
    case TSubType: return "<:";
    case TCoerce: return ":>";
    case TNaming: return "naming";
    case TStructAccess: return ".";
    case TArrowStructAccess: return "->";
    case TIndirectMethodAccess: return ".*";
    case TArrowIndirectMethodAccess: return "->*";
    case TArrayAccess: return "[]";
    case TCall: return "()";
    case TStructCall: return std::string(".").append(_fieldName).append("()");
    case TArrowStructCall:
      return std::string("->").append(_fieldName).append("()");
    case TForall: return "forall";
    case TExists: return "exists";
    case TLet: return "let";
    case TConditional: return "?:";
    default:
      assert(false);
  };
  return "";
}

DLexer::OperatorPunctuatorToken
TermOrPredicate::Operator::queryOperatorToken() const {
  DLexer::OperatorPunctuatorToken result;
  if (_type >= TPlus && _type <= TModulo)
    result.setType((DLexer::OperatorPunctuatorToken::Type)
        (DLexer::OperatorPunctuatorToken::TPlus + (_type - TPlus)));
  else if ((_type >= TLeftShift) && (_type <= TRightShift))
    result.setType((DLexer::OperatorPunctuatorToken::Type)
      (DLexer::OperatorPunctuatorToken::TLeftShift + (_type - TLeftShift)));
  else if ((_type >= TEqual) && (_type <= TGreaterOrEqual))
    result.setType((DLexer::OperatorPunctuatorToken::Type)
        (DLexer::OperatorPunctuatorToken::TEqual + (_type - TEqual)));
  else if ((_type >= TLess) && (_type <= TGreater))
    result.setType((DLexer::OperatorPunctuatorToken::Type)
        (DLexer::OperatorPunctuatorToken::TLess + (_type - TLess)));
  else if ((_type >= TLogicalAnd) && (_type <= TLogicalOr))
    result.setType((DLexer::OperatorPunctuatorToken::Type) (DLexer
          ::OperatorPunctuatorToken::TLogicalAnd + (_type - TLogicalAnd)));
  else if ((_type >= TLogicalImply) && (_type <= TLogicalXOr))
    result.setType((DLexer::OperatorPunctuatorToken::Type)
        (DLexer::OperatorPunctuatorToken::TImplies + (_type - TLogicalImply)));
  else if ((_type >= TBitAnd) && (_type <= TBitOr))
    result.setType((DLexer::OperatorPunctuatorToken::Type)
        (DLexer::OperatorPunctuatorToken::TAmpersand + (_type - TBitAnd)));
  else if ((_type >= TBitImply) && (_type <= TBitEquiv))
    result.setType((DLexer::OperatorPunctuatorToken::Type)
        (DLexer::OperatorPunctuatorToken::TBitImplies + (_type - TBitImply)));
  else if (_type == TBitXOr)
    result.setType(DLexer::OperatorPunctuatorToken::TBitXor);
  else if ((_type >= TUnaryPlus) && (_type <= TUnaryMinus))
    result.setType((DLexer::OperatorPunctuatorToken::Type)
        (DLexer::OperatorPunctuatorToken::TPlus + (_type - TUnaryPlus)));
  else if (_type == TNot)
    result.setType(DLexer::OperatorPunctuatorToken::TNot);
  else if (_type == TAddressOf)
    result.setType(DLexer::OperatorPunctuatorToken::TAmpersand);
  else if (_type == TComplement)
    result.setType(DLexer::OperatorPunctuatorToken::TTilda);
  else if (_type == TDereference)
    result.setType(DLexer::OperatorPunctuatorToken::TStar);
  else if (_type == TSubType)
    result.setType(DLexer::OperatorPunctuatorToken::TLTColon);
  else if (_type == TCoerce)
    result.setType(DLexer::OperatorPunctuatorToken::TColonGT);
  else if (_type == TArrowStructAccess)
    result.setType(DLexer::OperatorPunctuatorToken::TArrow);
  else if (_type == TArrayAccess)
    result.setType(DLexer::OperatorPunctuatorToken::TOpenBracket);
  result.clearFull();
  return result;
}

TermOrPredicate::Operator&
TermOrPredicate::Operator::setType(Type type, bool isPrefix) {
  _type = type;
  _isRightAssociative = false;
  switch (type) {
    case TUndefined: assert(false);
    case TPlus:
    case TMinus:
      _precedence = PAddition;
      break;
    case TTimes:
    case TDivide:
    case TModulo:
      _precedence = PMultiplication;
      break;
    case TLeftShift:
    case TRightShift:
      _precedence = PShift;
      break;
    case TEqual:
    case TDifferent:
      _precedence = PEquality;
      break;
    case TLessOrEqual:
    case TGreaterOrEqual:
    case TLess:
    case TGreater:
      _precedence = PComparison;
      break;
    case TLogicalAnd:
      _precedence = PLogicalAnd;
      break;
    case TLogicalOr:
      _precedence = PLogicalOr;
      break;
    case TLogicalImply:
      _precedence = PLogicalImply;
      break;
    case TLogicalEquiv:
      _precedence = PLogicalEquiv;
      break;
    case TLogicalXOr:
      _precedence = PLogicalXOr;
      break;
    case TBitAnd:
      _precedence = PBitAnd;
      break;
    case TBitOr:
      _precedence = PBitOr;
      break;
    case TBitImply:
      _precedence = PBitImply;
      break;
    case TBitEquiv:
      _precedence = PBitEquiv;
      break;
    case TBitXOr:
      _precedence = PBitExclusiveOr;
      break;
    case TUnaryPlus:
    case TUnaryMinus:
      _isRightAssociative = true;
      _precedence = isPrefix ? PPrefix : PPostFix;
      break;
    case TNot:
    case TComplement:
    case TDereference:
    case TAddressOf:
      _isRightAssociative = true;
      _precedence = PUnary;
      break;
    case TCast:
      _isRightAssociative = true;
      _precedence = PCast;
      break;
    case TSubType:
    case TCoerce:
      _precedence = PCast;
      break;
    case TNaming:
      _precedence = PNaming;
      break;
    case TStructAccess:
    case TArrowStructAccess:
    case TIndirectMethodAccess:
    case TArrowIndirectMethodAccess:
    case TArrayAccess:
    case TCall:
    case TStructCall:
    case TArrowStructCall:
      _precedence = PPostFix;
      break;
    case TForall:
    case TExists:
    case TLet:
      _precedence = PBinding;
      break;
    case TConditional:
      _isRightAssociative = true;
      _precedence = PConditional;
      break;
  };
  return *this;
}

TermOrPredicate::Operator&
TermOrPredicate::pushOperator(Operator::Type typeOperator,
    int leftSubExpressions, Parser::Arguments& context, bool& hasFailed) {
  assert(!_doesRequireValue);
  Operator* result = &_operatorStack.back();
  if (!result->isValid()) {
    result->setType(typeOperator).setLeftSubExpressions(leftSubExpressions);
  }
  else {
    Operator expressionOperator;
    expressionOperator.setType(typeOperator)
      .setLeftSubExpressions(leftSubExpressions);
    if (leftSubExpressions == 0)
      expressionOperator.setLocation(copy_loc(_loc));
    Operator* lastOperator = NULL;
    bool isLeftAssociative = expressionOperator.isLeftAssociative();
    logic_type ltype = NULL;
    term expressionResult = NULL;
    predicate_named predicateResult = NULL;
    unsigned possibleSubtypeResult = getSubExpressionPossibleTypes();
    while (!_operatorStack.empty() && (isLeftAssociative
        ? ((lastOperator = &_operatorStack.back())->getPrecedence()
          >= expressionOperator.getPrecedence())
        : ((lastOperator = &_operatorStack.back())->getPrecedence()
          > expressionOperator.getPrecedence()))) {
      if (expressionResult || predicateResult) {
        setLastArgument(*lastOperator, ltype, expressionResult,
            predicateResult);
        expressionResult = NULL;
        predicateResult = NULL;
        ltype = NULL;
      };
      if (!lastOperator->isFinished())
        break;
      bool ok = apply(*lastOperator, ltype, expressionResult, predicateResult,
          context, possibleSubtypeResult); 
      if (!ok) {
        hasFailed = true;
        return *result;
      };
      if (lastOperator->_startLocation) {
        free_location(lastOperator->_startLocation);
        lastOperator->_startLocation = NULL;
      }
      lastOperator = NULL;
      _operatorStack.pop_back();
    };
    if (expressionResult == NULL && predicateResult == NULL) {
      assert(!ltype && lastOperator != NULL);
      if (!lastOperator->isBinaryOperator() ||
          lastOperator->BinaryOperatorHasSecondArgument())
        lastOperator->extractLastArgument(
          ltype, expressionResult, predicateResult);
      else lastOperator->_leftSubExpressions++;
      // We're about to add another argument
    };
    expressionOperator.setFirstArgument(ltype, expressionResult,
        predicateResult);
    _operatorStack.push_back(expressionOperator);
    result = &_operatorStack.back();
  };
  _doesRequireValue = true;
  return *result;
}

class TermOrPredicate::GuardLogicType {
private:
  logic_type& _logicType;

public:
  GuardLogicType(logic_type& logicType) : _logicType(logicType) {}
  ~GuardLogicType()
    { if (_logicType) free_logic_type(_logicType); _logicType = NULL; }
};

class TermOrPredicate::GuardType {
private:
  typ& _tType;

public:
  GuardType(typ& tType) : _tType(tType) {}
  ~GuardType() { if (_tType) free_typ(_tType); _tType = NULL; }
};

class TermOrPredicate::GuardTerm {
private:
  term& _tTerm;

public:
  GuardTerm(term& tTerm) : _tTerm(tTerm) {}
  ~GuardTerm() { if (_tTerm) free_term(_tTerm); _tTerm = NULL; }
};

bool
TermOrPredicate::isCArray(const term& argument,const logic_type ltype, Parser::Arguments& context) {
  if (!isCArrayType(ltype,context)) return false ; 
  term_lhost termLHost = NULL;
  if (argument->node->tag_term_node == TSTARTOF)
    termLHost = argument->node->cons_term_node.TStartOf.subexpr->base_support;
  else if (argument->node->tag_term_node == TLVAL)
    termLHost = argument->node->cons_term_node.TLval.value->base_support;
  else if (argument->node->tag_term_node == TIF)
    return isCArray(argument->node->cons_term_node.TIf.then_part,ltype,context)
      && isCArray(argument->node->cons_term_node.TIf.else_part,ltype,context);
  else if (argument->node->tag_term_node == TLET)
    return isCArray(argument->node->cons_term_node.TLet.value,ltype,context);
  else
    // TUpdate gives back a logic array, TStartOf has pointer type anyway,
    // other constructors are never arrays.
    return false;
  if (termLHost->tag_term_lhost == TVAR)
      return termLHost->cons_term_lhost.TVar.var->lv_kind != LVLOCAL;
  if (termLHost->tag_term_lhost == TRESULT)
    return true;
  return (termLHost->tag_term_lhost == TMEM);
}

bool
TermOrPredicate::isLogicZero(const term& argument) {
  if (argument->node->tag_term_node == TCONST) {
    logic_constant constant = argument->node->cons_term_node.TConst.value;
    if (constant->tag_logic_constant == LCINT)
      // only catches 0 as generated by tzero
      return strcmp(constant->cons_logic_constant.LCInt.value,"0") == 0;
    else if (constant->tag_logic_constant == LCENUM)
      return constant->cons_logic_constant.LCEnum.value == 0;
    else if (constant->tag_logic_constant == LCHR)
      return constant->cons_logic_constant.LChr.value == 0;
  }
  else if (argument->node->tag_term_node == TCASTE)
    return isLogicZero(argument->node->cons_term_node.TCastE.subexpr);
  return false;
}

bool
TermOrPredicate::isLogicStrictNull(const term& argument) {
  if (argument->node->tag_term_node == TNULL)
    return true;
  else if (argument->node->tag_term_node == TCASTE)
    return isLogicStrictNull(argument->node->cons_term_node.TCastE.subexpr);
  return false;
}

bool
TermOrPredicate::needLogicCast(logic_type oldType, logic_type newType) {
  if (oldType->tag_logic_type != newType->tag_logic_type)
    return true;
  switch (newType->tag_logic_type) {
    case LVOID:
    case LINTEGER:
    case LREAL:
      return false;
    case LINT:
      return oldType->cons_logic_type.Lint.kind
        != newType->cons_logic_type.Lint.kind;
    case LFLOAT:
      return oldType->cons_logic_type.Lfloat.kind
        != newType->cons_logic_type.Lfloat.kind;
    case LARRAY:
      if (needLogicCast(oldType->cons_logic_type.Larray.subtype,
            newType->cons_logic_type.Larray.subtype))
        return true;
      if (oldType->cons_logic_type.Larray.dim->is_some) {
        if (newType->cons_logic_type.Larray.dim->is_some)
          return !logic_constant_equal(
              (logic_constant) oldType->cons_logic_type.Larray
                  .dim->content.container,
              (logic_constant) newType->cons_logic_type.Larray
                  .dim->content.container);
        return true;
      }
      return newType->cons_logic_type.Larray.dim->is_some;
    case LPOINTER:
      return needLogicCast(oldType->cons_logic_type.Lpointer.subtype,
          newType->cons_logic_type.Lpointer.subtype);
    case LREFERENCE:
      return needLogicCast(oldType->cons_logic_type.Lreference.subtype,
          newType->cons_logic_type.Lreference.subtype);
    case LENUM:
      return !qualified_name_equal(oldType->cons_logic_type.Lenum.name,
          newType->cons_logic_type.Lenum.name);
    case LSTRUCT:
      return !qualified_name_equal(oldType->cons_logic_type.Lstruct.name,
          newType->cons_logic_type.Lstruct.name)
        || !tkind_equal(oldType->cons_logic_type.Lstruct.template_kind,
            newType->cons_logic_type.Lstruct.template_kind);
    case LUNION:
      return !qualified_name_equal(oldType->cons_logic_type.Lunion.name,
          newType->cons_logic_type.Lunion.name)
        || !tkind_equal(oldType->cons_logic_type.Lstruct.template_kind,
            newType->cons_logic_type.Lstruct.template_kind);
    case LCNAMED:
      return !qualified_name_equal(oldType->cons_logic_type.LCnamed.name,
          newType->cons_logic_type.LCnamed.name);
    case LVARIABLE:
      return !qualified_name_equal(oldType->cons_logic_type.Lvariable.name,
          newType->cons_logic_type.Lvariable.name);
    case LNAMED:
      if (!qualified_name_equal(oldType->cons_logic_type.Lnamed.name,
            newType->cons_logic_type.Lnamed.name))
        return true;
      { list oldCursor = oldType->cons_logic_type.Lnamed.template_arguments;
        list newCursor = newType->cons_logic_type.Lnamed.template_arguments;
        while (oldCursor != NULL) {
          if (newCursor == NULL)
            return true;
          if (needLogicCast((logic_type) oldCursor->element.container,
                (logic_type) newCursor->element.container))
            return true;
          oldCursor = oldCursor->next;
          newCursor = newCursor->next;
        };
        if (newCursor != NULL)
          return true;
      };
      return false;
    case LARROW:
      { list oldCursor = oldType->cons_logic_type.Larrow.left;
        list newCursor = newType->cons_logic_type.Larrow.left;
        while (oldCursor != NULL) {
          if (newCursor == NULL)
            return true;
          if (needLogicCast((logic_type) oldCursor->element.container,
                (logic_type) newCursor->element.container))
            return true;
          oldCursor = oldCursor->next;
          newCursor = newCursor->next;
        };
        if (newCursor != NULL)
          return true;
      };
      return needLogicCast(oldType->cons_logic_type.Larrow.right,
          newType->cons_logic_type.Larrow.right);
  };
  return false;
}

term
TermOrPredicate::makeLogicStartOf(term node, Parser::Arguments& context) {
   term_node nodeResult = NULL;
  switch (node->node->tag_term_node) {
    case TLVAL:
      {	nodeResult =
        term_node_TStartOf(
          term_lval_dup(node->node->cons_term_node.TLval.value));
      };
      break;
    case TIF:
      {	nodeResult =
          term_node_TIf(
            term_dup(node->node->cons_term_node.TIf.condition),
            makeLogicStartOf(
              term_dup(node->node->cons_term_node.TIf.then_part), context),
            makeLogicStartOf(
              term_dup(node->node->cons_term_node.TIf.else_part), context));
      };
      break;
    case TLET:
      {	nodeResult =
          term_node_TLet(
            logic_info_dup(node->node->cons_term_node.TLet.name),
            makeLogicStartOf(
              term_dup(node->node->cons_term_node.TLet.value),
              context));
      };
      break;
    default:
      context.addErrorMessage("StartOf given a non-C-array term");
      assert(false);
      return NULL;
  };
  term result = term_cons(nodeResult, copy_loc(node->loc), NULL /* names */);
  free_term(node);
  // names = NULL;
  return result;
}

bool
TermOrPredicate::isCType(logic_type ltype) {
  tag_logic_type tagType = ltype->tag_logic_type;
  return tagType == LVOID || tagType == LINT || tagType == LFLOAT
      || tagType == LARRAY || tagType == LPOINTER || tagType == LREFERENCE
      || tagType == LENUM || tagType == LSTRUCT || tagType == LUNION
      || tagType == LCNAMED;
}

bool
TermOrPredicate::isCPointerType(logic_type ltype, Parser::Arguments& context) {
  tag_logic_type tagType = ltype->tag_logic_type;
  return tagType == LPOINTER || (tagType == LCNAMED
      && context.isPointerTypedefType(ltype->cons_logic_type.LCnamed.name));
}

bool
TermOrPredicate::isCReferenceType(logic_type ltype, Parser::Arguments& context)
{ tag_logic_type tagType = ltype->tag_logic_type;
  return tagType == LREFERENCE || (tagType == LCNAMED
      && context.isReferenceTypedefType(ltype->cons_logic_type.LCnamed.name));
}

bool
TermOrPredicate::isCArrayType(logic_type ltype, Parser::Arguments& context) {
  tag_logic_type tagType = ltype->tag_logic_type;
  return tagType == LARRAY || (tagType == LCNAMED
      && context.isArrayTypedefType(ltype->cons_logic_type.LCnamed.name));
}

qualified_name
TermOrPredicate::makeCCompoundType(logic_type ltype, Parser::Arguments& context,
    tkind* templateKind)
{ tag_logic_type tagType = ltype->tag_logic_type;
  if (tagType == LSTRUCT) {
    if (templateKind)
      *templateKind = tkind_dup(ltype->cons_logic_type.Lstruct.template_kind);
    return qualified_name_dup(ltype->cons_logic_type.Lstruct.name);
  };
  if (tagType == LUNION) {
    if (templateKind)
      *templateKind = tkind_dup(ltype->cons_logic_type.Lunion.template_kind);
    return qualified_name_dup(ltype->cons_logic_type.Lunion.name);
  }
  if (tagType == LCNAMED)
    return context.makeCompoundTypedefType(
        ltype->cons_logic_type.LCnamed.name, templateKind);
  return NULL;
}

term
TermOrPredicate::applyTermCast(logic_type& ccastType, term targument,
    logic_type ltype, Parser::Arguments& context) {
  GuardLogicType guardType(ccastType);
  logic_type alternateType = NULL;
  GuardLogicType guardAlternate(alternateType);
  if (ltype->tag_logic_type == LINTEGER) {
    alternateType = ltype = logic_type_Lint(IINT);
    targument = term_cons(term_node_TCastE(logic_type_dup(ltype), targument),
      copy_loc(targument->loc), NULL);
  }
  else if (ltype->tag_logic_type == LREAL) {
    alternateType = ltype = logic_type_Lfloat(FDOUBLE);
    targument = term_cons(term_node_TCastE(logic_type_dup(ltype), targument),
      copy_loc(targument->loc), NULL);
  };
  if (isCType(ltype)) {
    if (isCPointerType(ccastType, context) && isCArrayType(ltype, context)) {
      if (!isCArray(targument,ltype,context)) {
        context.addErrorMessage("cannot cast logic array to pointer type");
        assert(false);
        return NULL;
      };
      return makeLogicStartOf(targument, context);
    };
    if (isCPointerType(ccastType, context) && isLogicStrictNull(targument))
      return targument;
    if (ccastType->tag_logic_type == LENUM && ltype->tag_logic_type == LENUM
        && qualified_name_equal(ccastType->cons_logic_type.Lenum.name,
              ltype->cons_logic_type.Lenum.name))
      return targument;
    if (!needLogicCast(ltype, ccastType))
      return targument;
    // if (isCPointerType(ccastType, context)
    //     && targument->node->tag_term_node == TCASTE) {
    //   logic_type oldType = targument->node->cons_term_node.TCastE.oldtype;
    //   if (isCPointerType(oldType, context)) {
    //     // Old cast can be removed...
    //     if (needLogicCast(ccastType, oldType)) {
    //       free_logic_type(targument->node->cons_term_node.TCastE.code_type);
    //       targument->node->cons_term_node.TCastE.code_type
    //           = logic_type_dup(ccastType);
    //       targument->ltype = logic_type_Ctype(ccastType);
    //       ccastType = NULL;
    //       return targument;
    //     };
    //     // In fact, both casts can be removed.
    //     term result = targument->node->cons_term_node.TCastE.subexpr;
    //     targument->node->cons_term_node.TCastE.subexpr = NULL;
    //     targument->node->tag_term_node = (tag_term_node) (TLET + 1);
    //     return result;
    //   };
    //   // Do not remove old cast because they are conversions !!!
    // };
    term_node valueResult = term_node_TCastE(ccastType, targument);
    term result = term_cons(valueResult, copy_loc(targument->loc), NULL);
    ccastType = NULL;
    targument = NULL;
    // names = NULL;
    return result;
  };
  logic_type elementType = isSetType(ltype);
  if (elementType) {
    // For all other instances of cast, the result type of the expression is ccastType.
    // However for a cast on a set<>, the result type is a set<ccastType>.
    // However, the logic that presume this is in the caller - there is currently no way
    // return a different type. Also, it appears not to matter -- or at least there
    // are no tests yet that test this.
    //resultType = make_set_type(ccastType);
    term_node valueResult = term_node_TCastE(ccastType, targument);
    term result = term_cons(valueResult, copy_loc(targument->loc), NULL);
    ccastType = NULL;
    targument = NULL;
    return result;
  }
  context.addErrorMessage("cannot cast to logic type");
  assert(false);
  return NULL;
}

bool
TermOrPredicate::isIntegralType(logic_type ctype, Parser::Arguments& context) {
  bool result = (ctype->tag_logic_type == LINTEGER)
      || (ctype->tag_logic_type == LINT)
      || (ctype->tag_logic_type == LENUM);
  if (!result && ctype->tag_logic_type == LCNAMED)
    result = context.isIntegralTypedefType(ctype->cons_logic_type.LCnamed.name);
  if (!result)
    result = context.is_builtin_boolean(ctype);
  return result;
}

bool
TermOrPredicate::isSignedInteger(logic_type ctype, Parser::Arguments& context) {
  bool result = false;
  if (ctype->tag_logic_type == LINT) {
    ikind kind = ctype->cons_logic_type.Lint.kind;
    result = (kind == ICHAR_S || kind == ISCHAR || kind == IWCHAR_S
        || kind == IWSCHAR || kind == ISHORT || kind == IINT || kind == ILONG);
  }
  else if (ctype->tag_logic_type == LINTEGER)
    result = true;
  else if (ctype->tag_logic_type == LENUM) {
    // unimplemented
    result = true; // find if at least one constant elements is negative ?
  };
  if (!result && ctype->tag_logic_type == LCNAMED)
    result = context.isSignedTypedefType(ctype->cons_logic_type.LCnamed.name);
  return result;
}

bool
TermOrPredicate::isPlainBooleanType(logic_type ltype,
    Parser::Arguments& context) {
  bool result =
    context.is_builtin_boolean(ltype) || (ltype->tag_logic_type == LINTEGER) ||
    (ltype->tag_logic_type == LINT) || (ltype->tag_logic_type == LENUM);
  if (!result && ltype->tag_logic_type == LCNAMED)
    result = context.isIntegralTypedefType(ltype->cons_logic_type.LCnamed.name);
  return result;
}

class TermOrPredicate::SubstitutionLevel {
public:
  typedef std::map<std::string, logic_type> MapLogicType;

private:
  MapLogicType _map;
  SubstitutionLevel* _parent;
  mutable int _counter;
  friend class Substitution;

public:
  SubstitutionLevel() : _parent(NULL), _counter(0) {}
  ~SubstitutionLevel()
    { if (_parent)
        --_parent->_counter;
      while (_parent && _parent->_counter <= 0) {
        SubstitutionLevel* parent = _parent->_parent;
        _parent->_parent = NULL;
        delete _parent;
        _parent = parent;
        if (_parent)
          --_parent->_counter;
      };
    }

  void setParent(SubstitutionLevel* parent)
    { assert(_parent == NULL);
      _parent = parent;
      if (_parent)
        ++_parent->_counter;
    }
};

class TermOrPredicate::Substitution {
public:
  typedef SubstitutionLevel::MapLogicType MapLogicType;

private:
  SubstitutionLevel* _currentMap;

public:
  Substitution() : _currentMap(NULL) {}
  Substitution(const Substitution& source)
    : _currentMap(source._currentMap)
    { if (_currentMap)
        ++_currentMap->_counter;
    }
  ~Substitution()
    { if (_currentMap) {
        --_currentMap->_counter;
        while (_currentMap && _currentMap->_counter <= 0) {
          SubstitutionLevel* parent = _currentMap->_parent;
          _currentMap->_parent = NULL;
          delete _currentMap;
          _currentMap = parent;
          if (_currentMap)
            --_currentMap->_counter;
        };
      }
    }
  void pushLevel()
    { SubstitutionLevel* newLevel = new SubstitutionLevel;
      if (_currentMap)
        --_currentMap->_counter;
      newLevel->setParent(_currentMap);
      _currentMap = newLevel;
    }
  MapLogicType& map() { assert(_currentMap); return _currentMap->_map; }
  void popLevel()
    { assert(_currentMap);
      SubstitutionLevel* parentMap = _currentMap->_parent;
      --_currentMap->_counter;
      if (_currentMap->_counter <= 0) {
        _currentMap->_parent = NULL;
        delete _currentMap;
      };
      _currentMap = parentMap;
    }
};

bool
TermOrPredicate::Operator::changeTypeToCallAccess(Parser::Arguments& context) {
  if (_type == TStructAccess) {
    tkind tempKind = NULL;
    qualified_name structName = makeCompoundType(_ltypeFirstArgument,
        Substitution(), context, &tempKind);
    if (!structName || !tempKind)
      return false;
    _identifier = context.findGlobalLogicName(structName);
    free_qualified_name(structName);
    if (!_identifier)
       return false;
    if (tempKind->tag_tkind == TTEMPLATEINSTANCE) {
      assert(_identifier->isQualification()
        && _identifier->asQualification().hasTemplateRecordType());
      /* template_parameter */ list parameters
        = tempKind->cons_tkind.TTemplateInstance.parameters;
      GlobalContext::TemplateQualification locate(parameters);
      GlobalContext::NestedContext::SonsSet::iterator
         found = _identifier->sons().find(&locate);
      if (found == _identifier->sons().end())
         return false;
      _identifier = *found;
    }
    else
      assert(!_identifier->isQualification()
        || !_identifier->asQualification().hasTemplateRecordType());
    free_tkind(tempKind);
    _type = TStructCall;
  }
  else if (_type == TArrowStructAccess) {
    if (!isPointerType(_ltypeFirstArgument, Substitution(), context))
      return false;
    logic_type subtype = typeOfPointed(_ltypeFirstArgument, Substitution(),
        context);
    assert(subtype);
    tkind tempKind = NULL;
    qualified_name structName = makeCompoundType(subtype, Substitution(),
      context, &tempKind);
    free_logic_type(subtype);
    if (!structName || !tempKind)
      return false;
    _identifier = context.findGlobalLogicName(structName);
    free_qualified_name(structName);
    if (!_identifier)
       return false;
    if (tempKind->tag_tkind == TTEMPLATEINSTANCE) {
      assert(_identifier->isQualification()
        && _identifier->asQualification().hasTemplateRecordType());
      /* template_parameter */ list parameters
        = tempKind->cons_tkind.TTemplateInstance.parameters;
      GlobalContext::TemplateQualification locate(parameters);
      GlobalContext::NestedContext::SonsSet::iterator
         found = _identifier->sons().find(&locate);
      if (found == _identifier->sons().end())
         return false;
      _identifier = *found;
    }
    else
      assert(!_identifier->isQualification()
        || !_identifier->asQualification().hasTemplateRecordType());
    free_tkind(tempKind);
    _type = TArrowStructCall;
  }
  else
    assert(false);
  GlobalContext::NestedContext methodName(_fieldName);
  GlobalContext::NestedContext::SonsSet::iterator
     found = _identifier->sons().find(&methodName);
  if (found == _identifier->sons().end())
     return false;
  _identifier = *found;
  return true;
}

predicate_named TermOrPredicate::convertTermToPredicate(
  logic_type typ, term t, Parser::Arguments& context) 
{
  predicate_named pred = NULL;
  if(isIntegralType(typ,Substitution(),context)) {
    term zero = tzero(t->loc);
    predicate diff = predicate_Prel(RNEQ,term_dup(t),zero);
    pred = predicate_named_cons(NULL,copy_loc(t->loc),diff);
  } else if (isPlainBooleanType(typ,context)) {
    predicate equal =
      predicate_Prel(REQ,term_dup(t),term_true(copy_loc(t->loc)));
    pred = predicate_named_cons(NULL,copy_loc(t->loc),equal);
  }
  // no other conversion possible for now.
  return pred;
}

bool
TermOrPredicate::isArithmeticType(logic_type ctype,
    Parser::Arguments& context) {
  if (ctype->tag_logic_type == LREFERENCE)
    ctype = ctype->cons_logic_type.Lreference.subtype;
  bool result = (ctype->tag_logic_type == LINT)
    || (ctype->tag_logic_type == LENUM)
    || (ctype->tag_logic_type == LFLOAT)
    || (ctype->tag_logic_type == LINTEGER)
    || (ctype->tag_logic_type == LREAL)
    ;
  if (!result && ctype->tag_logic_type == LCNAMED)
    result = context.isArithmeticTypedefType(ctype->cons_logic_type
        .LCnamed.name);
  return result;
}

bool
TermOrPredicate::isFloatingType(logic_type ctype, Parser::Arguments& context) {
  if (ctype->tag_logic_type == LREFERENCE)
    ctype = ctype->cons_logic_type.Lreference.subtype;
  bool result = (ctype->tag_logic_type == LFLOAT);
  if (!result && ctype->tag_logic_type == LCNAMED)
    result = context.isFloatingTypedefType(ctype->cons_logic_type.LCnamed.name);
  return result;
}

logic_type
TermOrPredicate::logicArithmeticPromotion(logic_type source,
    Parser::Arguments& context) {
  if (source->tag_logic_type == LREFERENCE)
    source = source->cons_logic_type.Lreference.subtype;
  switch (source->tag_logic_type) {
    case LINT:
      return logic_type_Linteger();
    case LENUM:
      return logic_type_Linteger();
    case LFLOAT:
      return logic_type_Lreal();
    case LCNAMED:
      return context.logicArithmeticPromotion(source->cons_logic_type
          .LCnamed.name);
    case LVARIABLE:
      break;
    case LNAMED:
      if (source->cons_logic_type.Lnamed.name->prequalification == NULL &&
          strcmp(source->cons_logic_type.Lnamed.name->decl_name, "set") == 0) {
        /* logic_type */ list parameters = NULL, endParameters = NULL,
          sourceCursor = source->cons_logic_type.Lnamed.template_arguments;
        if (sourceCursor != NULL) {
          parameters = cons_container(logicArithmeticPromotion(
              (logic_type) sourceCursor->element.container, context), NULL);
          endParameters = parameters;
          sourceCursor = sourceCursor->next;
          while (sourceCursor != NULL) {
            endParameters->next = cons_container(logicArithmeticPromotion(
                (logic_type) sourceCursor->element.container, context), NULL);
            endParameters = endParameters->next;
            sourceCursor = sourceCursor->next;
          };
        };
        return
          logic_type_Lnamed(
            qualified_name_dup(source->cons_logic_type.Lnamed.name),
            source->cons_logic_type.Lnamed.is_extern_c_name,
            parameters);
      };
      break;
    case LINTEGER:
      return logic_type_Linteger();
    case LREAL:
      return logic_type_Lreal();
    default: break;
  };
  context.addErrorMessage("logic arithmetic promotion on non-arithmetic type");
  assert(false);
  return NULL;
}

qualified_name
TermOrPredicate::getClassType(logic_type ltype, tkind* templateParameters) {
  while (ltype->tag_logic_type == LREFERENCE)
    ltype = ltype->cons_logic_type.Lreference.subtype;
  if (ltype->tag_logic_type == LSTRUCT) {
    if (templateParameters)
      *templateParameters = ltype->cons_logic_type.Lstruct.template_kind;
    return ltype->cons_logic_type.Lstruct.name;
  }
  if (ltype->tag_logic_type == LUNION) {
    if (templateParameters)
      *templateParameters = ltype->cons_logic_type.Lunion.template_kind;
    return ltype->cons_logic_type.Lunion.name;
  };
  return NULL;
}

bool
TermOrPredicate::isSameType(logic_type lfirst, logic_type lsecond,
    Substitution substitutionFirst, Substitution substitutionSecond,
    Parser::Arguments& context) {
  while (lfirst->tag_logic_type == LREFERENCE)
     lfirst = lfirst->cons_logic_type.Lreference.subtype;
  while (lsecond->tag_logic_type == LREFERENCE)
     lsecond = lsecond->cons_logic_type.Lreference.subtype;
  if (lfirst->tag_logic_type == LNAMED || lsecond->tag_logic_type == LNAMED) {
    bool hasAdvanced = false;
    bool doesAdvance;
    do {
      doesAdvance = false;
      if (lfirst->tag_logic_type == LNAMED) {
        GlobalContext::LogicType* typeDefinition
          = context.findGlobalLogicType(lfirst->cons_logic_type.Lnamed.name);
        if (typeDefinition && is_type_synonym(typeDefinition->type_info())) {
          /* string */ list formalParameters
            = typeDefinition->type_info()->params;
          /* logic_type */ list actualParameters
            = lfirst->cons_logic_type.Lnamed.template_arguments;
          lfirst = extract_synonym_def(typeDefinition->type_info());
          substitutionFirst.pushLevel();
          Substitution::MapLogicType& map = substitutionFirst.map();
          while (formalParameters) {
            if (actualParameters == NULL) {
              context.addErrorMessage("Logic type used with "
                  "wrong number of parameters");
              assert(false);
            };
            map.insert(std::make_pair(
                std::string((const char*) formalParameters->element.container),
                (logic_type) actualParameters->element.container));
            formalParameters = formalParameters->next;
            actualParameters = actualParameters->next;
          };
          if (actualParameters != NULL) {
            context.addErrorMessage("Logic type used with "
                "wrong number of parameters");
            assert(false);
          };
          hasAdvanced = doesAdvance = true;
        };
      };
      if (lsecond->tag_logic_type == LNAMED) {
        GlobalContext::LogicType* typeDefinition
            = context.findGlobalLogicType(lsecond->cons_logic_type.Lnamed.name);
        assert(typeDefinition);
        if (is_type_synonym(typeDefinition->type_info())) {
          /* string */ list formalParameters
              = typeDefinition->type_info()->params;
          /* logic_type */ list actualParameters
              = lsecond->cons_logic_type.Lnamed.template_arguments;
          lsecond = extract_synonym_def(typeDefinition->type_info());
          substitutionSecond.pushLevel();
          Substitution::MapLogicType& map = substitutionSecond.map();
          while (formalParameters) {
            if (actualParameters == NULL) {
              context.addErrorMessage("Logic type used with "
                  "wrong number of parameters");
              assert(false);
            };
            map.insert(std::make_pair(
                std::string((const char*) formalParameters->element.container),
                (logic_type) actualParameters->element.container));
            formalParameters = formalParameters->next;
            actualParameters = actualParameters->next;
          };
          if (actualParameters != NULL) {
            context.addErrorMessage("Logic type used with "
                "wrong number of parameters");
            assert(false);
          };
          hasAdvanced = doesAdvance = true;
        };
      };
    } while (doesAdvance);
    if (hasAdvanced)
      return isSameType(lfirst, lsecond, substitutionFirst,
          substitutionSecond, context);
  };
  if (lfirst->tag_logic_type == LVARIABLE
      || lsecond->tag_logic_type == LVARIABLE) {
    bool hasFirstVar = false, hasSecondVar = false;
    if (lfirst->tag_logic_type == LVARIABLE
        && !lfirst->cons_logic_type.Lvariable.name->prequalification) {
      // LVFormal type variable ?
      std::string name = lfirst->cons_logic_type.Lvariable.name->decl_name;
      const Substitution::MapLogicType& map = substitutionFirst.map();
      Substitution::MapLogicType::const_iterator found = map.find(name);
      if (found != map.end()) {
        hasFirstVar = true;
        lfirst = found->second;
      };
    };
    if (lsecond->tag_logic_type == LVARIABLE
        && !lsecond->cons_logic_type.Lvariable.name->prequalification) {
      // LVFormal type variable ?
      std::string name = lsecond->cons_logic_type.Lvariable.name->decl_name;
      const Substitution::MapLogicType& map = substitutionSecond.map();
      Substitution::MapLogicType::const_iterator found = map.find(name);
      if (found != map.end()) {
        hasSecondVar = true;
        lsecond = found->second;
      };
    };
    if (hasFirstVar || hasSecondVar) {
      if (hasFirstVar)
        substitutionFirst.popLevel();
      if (hasSecondVar)
        substitutionSecond.popLevel();
      return isSameType(lfirst, lsecond, substitutionFirst,
          substitutionSecond, context);
    };
    return lfirst->tag_logic_type == LVARIABLE
        && lsecond->tag_logic_type == LVARIABLE
        && qualified_name_equal(lfirst->cons_logic_type.Lvariable.name,
            lsecond->cons_logic_type.Lvariable.name);
  };

  if (lfirst->tag_logic_type != lsecond->tag_logic_type)
    return false;
  switch (lsecond->tag_logic_type) {
    case LVOID:
    case LINTEGER:
    case LREAL:
      return true;
    case LINT:
      return 
        equivalent_int_kind(
          lfirst->cons_logic_type.Lint.kind,
          lsecond->cons_logic_type.Lint.kind,
          context);
    case LFLOAT:
      return lfirst->cons_logic_type.Lfloat.kind
          == lsecond->cons_logic_type.Lfloat.kind;
    case LARRAY:
      if (!isSameType(lfirst->cons_logic_type.Larray.subtype,
            lsecond->cons_logic_type.Larray.subtype,
            substitutionFirst, substitutionSecond, context))
        return false;
      if (lfirst->cons_logic_type.Larray.dim->is_some) {
        if (lsecond->cons_logic_type.Larray.dim->is_some)
          return logic_constant_equal(
              (logic_constant) lfirst->cons_logic_type.Larray
                  .dim->content.container,
              (logic_constant) lsecond->cons_logic_type.Larray
                  .dim->content.container);
        return false;
      }
      return !lsecond->cons_logic_type.Larray.dim->is_some;
    case LPOINTER:
      return isSameType(lfirst->cons_logic_type.Lpointer.subtype,
          lsecond->cons_logic_type.Lpointer.subtype,
          substitutionFirst, substitutionSecond, context);
    case LREFERENCE:
      return isSameType(lfirst->cons_logic_type.Lreference.subtype,
          lsecond->cons_logic_type.Lreference.subtype,
          substitutionFirst, substitutionSecond, context);
    case LENUM:
      return qualified_name_equal(lfirst->cons_logic_type.Lenum.name,
          lsecond->cons_logic_type.Lenum.name);
    case LSTRUCT:
      return qualified_name_equal(lfirst->cons_logic_type.Lstruct.name,
          lsecond->cons_logic_type.Lstruct.name)
        && tkind_equal(lfirst->cons_logic_type.Lstruct.template_kind,
          lsecond->cons_logic_type.Lstruct.template_kind);
    case LUNION:
      return qualified_name_equal(lfirst->cons_logic_type.Lunion.name,
          lsecond->cons_logic_type.Lunion.name)
        && tkind_equal(lfirst->cons_logic_type.Lunion.template_kind,
          lsecond->cons_logic_type.Lunion.template_kind);
    case LCNAMED:
      return qualified_name_equal(lfirst->cons_logic_type.LCnamed.name,
          lsecond->cons_logic_type.LCnamed.name);
    case LVARIABLE:
      return qualified_name_equal(lfirst->cons_logic_type.Lvariable.name,
          lsecond->cons_logic_type.Lvariable.name);
    case LNAMED:
      if (!qualified_name_equal(lfirst->cons_logic_type.Lnamed.name,
            lsecond->cons_logic_type.Lnamed.name))
        return false;
      { list firstCursor = lfirst->cons_logic_type.Lnamed.template_arguments;
        list secondCursor = lsecond->cons_logic_type.Lnamed.template_arguments;
        while (firstCursor != NULL) {
          if (secondCursor == NULL)
            return false;
          if (!isSameType((logic_type) firstCursor->element.container,
                (logic_type) secondCursor->element.container,
                substitutionFirst, substitutionSecond, context))
            return false;
          firstCursor = firstCursor->next;
          secondCursor = secondCursor->next;
        };
        return (secondCursor == NULL);
      };
    case LARROW:
      { /* logic_type */ list firstCursor = lfirst->cons_logic_type.Larrow.left;
        /* logic_type */ list secondCursor = lsecond->cons_logic_type
              .Larrow.left;
        while (firstCursor != NULL) {
          if (secondCursor == NULL)
            return false;
          if (!isSameType((logic_type) firstCursor->element.container,
                (logic_type) secondCursor->element.container,
                substitutionFirst, substitutionSecond, context))
            return false;
          firstCursor = firstCursor->next;
          secondCursor = secondCursor->next;
        };
        if (secondCursor != NULL)
          return false;
      };
      return isSameType(lfirst->cons_logic_type.Larrow.right,
          lsecond->cons_logic_type.Larrow.right,
          substitutionFirst, substitutionSecond, context);
  };
  return true;
}

logic_type
TermOrPredicate::isCompatibleType(logic_type lfirst, logic_type lsecond,
    Substitution substitutionFirst, Substitution substitutionSecond,
    Parser::Arguments& context) {
  while (lfirst->tag_logic_type == LREFERENCE)
     lfirst = lfirst->cons_logic_type.Lreference.subtype;
  while (lsecond->tag_logic_type == LREFERENCE)
     lsecond = lsecond->cons_logic_type.Lreference.subtype;
  if (lfirst->tag_logic_type == LNAMED || lsecond->tag_logic_type == LNAMED) {
    logic_type singletonFirstType = isSetType(lfirst);
    logic_type singletonSecondType = isSetType(lsecond);
    if (singletonFirstType && singletonSecondType)
      return isCompatibleType(singletonFirstType, singletonSecondType,
        substitutionFirst, substitutionSecond, context);
    if (singletonSecondType)
      return isCompatibleType(lfirst, singletonSecondType,
        substitutionFirst, substitutionSecond, context) ? lsecond : NULL;
    if (singletonFirstType)
      return NULL;
    bool hasAdvanced = false;
    bool doesAdvance;
    do {
      doesAdvance = false;
      if (lfirst->tag_logic_type == LNAMED) {
        GlobalContext::LogicType* typeDefinition
          = context.findGlobalLogicType(lfirst->cons_logic_type.Lnamed.name);
        if (typeDefinition && is_type_synonym(typeDefinition->type_info())) {
          /* string */ list formalParameters
            = typeDefinition->type_info()->params;
          /* logic_type */ list actualParameters
            = lfirst->cons_logic_type.Lnamed.template_arguments;
          lfirst = extract_synonym_def(typeDefinition->type_info());
          substitutionFirst.pushLevel();
          Substitution::MapLogicType& map = substitutionFirst.map();
          while (formalParameters) {
            if (actualParameters == NULL) {
              context.addErrorMessage("Logic type used with "
                  "wrong number of parameters");
              assert(false);
            };
            map.insert(std::make_pair(
                std::string((const char*) formalParameters->element.container),
                (logic_type) actualParameters->element.container));
            formalParameters = formalParameters->next;
            actualParameters = actualParameters->next;
          };
          if (actualParameters != NULL) {
            context.addErrorMessage("Logic type used with "
                "wrong number of parameters");
            assert(false);
          };
          hasAdvanced = doesAdvance = true;
        };
      };
      if (lsecond->tag_logic_type == LNAMED) {
        GlobalContext::LogicType* typeDefinition
            = context.findGlobalLogicType(lsecond->cons_logic_type.Lnamed.name);
        assert(typeDefinition);
        if (is_type_synonym(typeDefinition->type_info())) {
          /* string */ list formalParameters
              = typeDefinition->type_info()->params;
          /* logic_type */ list actualParameters
              = lsecond->cons_logic_type.Lnamed.template_arguments;
          lsecond = extract_synonym_def(typeDefinition->type_info());
          substitutionSecond.pushLevel();
          Substitution::MapLogicType& map = substitutionSecond.map();
          while (formalParameters) {
            if (actualParameters == NULL) {
              context.addErrorMessage("Logic type used with "
                  "wrong number of parameters");
              assert(false);
            };
            map.insert(std::make_pair(
                std::string((const char*) formalParameters->element.container),
                (logic_type) actualParameters->element.container));
            formalParameters = formalParameters->next;
            actualParameters = actualParameters->next;
          };
          if (actualParameters != NULL) {
            context.addErrorMessage("Logic type used with "
                "wrong number of parameters");
            assert(false);
          };
          hasAdvanced = doesAdvance = true;
        };
      };
    } while (doesAdvance);
    if (hasAdvanced)
      return isCompatibleType(lfirst, lsecond, substitutionFirst,
          substitutionSecond, context) ? lfirst : NULL;
  };
  if (lfirst->tag_logic_type == LCNAMED) {
    logic_type unroll =
      context.makeLogicType(lfirst->cons_logic_type.LCnamed.name);
    return
      isCompatibleType(
        unroll,lsecond,substitutionFirst,substitutionSecond,context)
      ?lfirst:NULL;
  }
  if (lsecond->tag_logic_type == LCNAMED) {
    logic_type unroll =
      context.makeLogicType(lsecond->cons_logic_type.LCnamed.name);
    return
      isCompatibleType(
        lfirst,unroll,substitutionFirst,substitutionSecond,context);
//        return
//          isCompatibleType(
//            lfirst,unroll,substitutionFirst,substitutionSecond,context)
//          ?lsecond:NULL;
  }
  if (lfirst->tag_logic_type == LVARIABLE
      || lsecond->tag_logic_type == LVARIABLE) {
    bool hasFirstVar = false, hasSecondVar = false;
    if (lfirst->tag_logic_type == LVARIABLE
        && !lfirst->cons_logic_type.Lvariable.name->prequalification) {
      // LVFormal type variable ?
      std::string name = lfirst->cons_logic_type.Lvariable.name->decl_name;
      const Substitution::MapLogicType& map = substitutionFirst.map();
      Substitution::MapLogicType::const_iterator found = map.find(name);
      if (found != map.end()) {
        hasFirstVar = true;
        lfirst = found->second;
      };
    };
    if (lsecond->tag_logic_type == LVARIABLE
        && !lsecond->cons_logic_type.Lvariable.name->prequalification) {
      // LVFormal type variable ?
      std::string name = lsecond->cons_logic_type.Lvariable.name->decl_name;
      const Substitution::MapLogicType& map = substitutionSecond.map();
      Substitution::MapLogicType::const_iterator found = map.find(name);
      if (found != map.end()) {
        hasSecondVar = true;
        lsecond = found->second;
      };
    };
    if (hasFirstVar || hasSecondVar) {
      if (hasFirstVar)
        substitutionFirst.popLevel();
      if (hasSecondVar)
        substitutionSecond.popLevel();
      return isCompatibleType(lfirst, lsecond, substitutionFirst,
          substitutionSecond, context) ? lfirst : NULL;
    };
    return (lfirst->tag_logic_type == LVARIABLE
        && lsecond->tag_logic_type == LVARIABLE
        && qualified_name_equal(lfirst->cons_logic_type.Lvariable.name,
            lsecond->cons_logic_type.Lvariable.name))
      ? lfirst : NULL;
  };
  if (lfirst->tag_logic_type == LPOINTER && 
      lsecond->tag_logic_type == LARROW) {
    // prefer pointer to fun over direct fun
    return
      isCompatibleType(
        lfirst->cons_logic_type.Lpointer.subtype,lsecond,
        substitutionFirst,substitutionSecond,context)
      ?lfirst:NULL;
  }
  if (lfirst->tag_logic_type == LARROW && 
      lsecond->tag_logic_type == LPOINTER) {
    // prefer pointer to fun over direct fun
    return
      isCompatibleType(
        lfirst,lsecond->cons_logic_type.Lpointer.subtype,
        substitutionFirst,substitutionSecond,context)
      ?lsecond:NULL;
  }

  if (lfirst->tag_logic_type == LREAL && lsecond->tag_logic_type == LFLOAT) return lfirst;
  if (lfirst->tag_logic_type == LINTEGER && lsecond->tag_logic_type == LINT) return lfirst;

  if (lfirst->tag_logic_type != lsecond->tag_logic_type) {
    return NULL;
  }
  switch (lsecond->tag_logic_type) {
    case LVOID:
    case LINTEGER:
    case LREAL:
      return lfirst;
    case LINT:
      return (lfirst->cons_logic_type.Lint.kind
            == lsecond->cons_logic_type.Lint.kind) ? lfirst : NULL;
    case LFLOAT:
      return (lfirst->cons_logic_type.Lfloat.kind
            == lsecond->cons_logic_type.Lfloat.kind) ? lfirst : NULL;
    case LARRAY:
      if (!isSameType(lfirst->cons_logic_type.Larray.subtype,
            lsecond->cons_logic_type.Larray.subtype,
            substitutionFirst, substitutionSecond, context))
        return NULL;
      if (lfirst->cons_logic_type.Larray.dim->is_some) {
        if (lsecond->cons_logic_type.Larray.dim->is_some)
          return logic_constant_equal(
              (logic_constant) lfirst->cons_logic_type.Larray
                  .dim->content.container,
              (logic_constant) lsecond->cons_logic_type.Larray
                  .dim->content.container) ? lfirst : NULL;
        return NULL;
      }
      return (!lsecond->cons_logic_type.Larray.dim->is_some) ? lfirst : NULL;
    case LPOINTER:
      return isSameType(lfirst->cons_logic_type.Lpointer.subtype,
          lsecond->cons_logic_type.Lpointer.subtype,
          substitutionFirst, substitutionSecond, context) ? lfirst : NULL;
    case LREFERENCE:
      return isSameType(lfirst->cons_logic_type.Lreference.subtype,
          lsecond->cons_logic_type.Lreference.subtype,
          substitutionFirst, substitutionSecond, context) ? lfirst : NULL;
    case LENUM:
      return qualified_name_equal(lfirst->cons_logic_type.Lenum.name,
          lsecond->cons_logic_type.Lenum.name) ? lfirst : NULL;
    case LSTRUCT:
      return (qualified_name_equal(lfirst->cons_logic_type.Lstruct.name,
            lsecond->cons_logic_type.Lstruct.name)
          && tkind_equal(lfirst->cons_logic_type.Lstruct.template_kind,
            lsecond->cons_logic_type.Lstruct.template_kind))? lfirst : NULL;
    case LUNION:
      return (qualified_name_equal(lfirst->cons_logic_type.Lunion.name,
            lsecond->cons_logic_type.Lunion.name)
          && tkind_equal(lfirst->cons_logic_type.Lunion.template_kind,
            lsecond->cons_logic_type.Lunion.template_kind))? lfirst : NULL;
    case LCNAMED:
      return qualified_name_equal(lfirst->cons_logic_type.LCnamed.name,
          lsecond->cons_logic_type.LCnamed.name) ? lfirst : NULL;;
    case LVARIABLE:
      return qualified_name_equal(lfirst->cons_logic_type.Lvariable.name,
          lsecond->cons_logic_type.Lvariable.name) ? lfirst : NULL;;
    case LNAMED:
      if (!qualified_name_equal(lfirst->cons_logic_type.Lnamed.name,
            lsecond->cons_logic_type.Lnamed.name))
        return NULL;
      { list firstCursor = lfirst->cons_logic_type.Lnamed.template_arguments;
        list secondCursor = lsecond->cons_logic_type.Lnamed.template_arguments;
        while (firstCursor != NULL) {
          if (secondCursor == NULL)
            return NULL;
          if (!isSameType((logic_type) firstCursor->element.container,
                (logic_type) secondCursor->element.container,
                substitutionFirst, substitutionSecond, context))
            return NULL;
          firstCursor = firstCursor->next;
          secondCursor = secondCursor->next;
        };
        return (secondCursor == NULL) ? lfirst : NULL;
      };
    case LARROW:
      { /* logic_type */ list firstCursor = lfirst->cons_logic_type.Larrow.left;
        /* logic_type */ list secondCursor = lsecond->cons_logic_type
              .Larrow.left;
        while (firstCursor != NULL) {
          if (secondCursor == NULL)
            return NULL;
          if (!isSameType((logic_type) firstCursor->element.container,
                (logic_type) secondCursor->element.container,
                substitutionFirst, substitutionSecond, context))
            return NULL;
          firstCursor = firstCursor->next;
          secondCursor = secondCursor->next;
        };
        if (secondCursor != NULL)
          return NULL;
      };
      return isSameType(lfirst->cons_logic_type.Larrow.right,
          lsecond->cons_logic_type.Larrow.right,
          substitutionFirst, substitutionSecond, context) ? lfirst : NULL;
  };
  return lfirst;
}

bool
TermOrPredicate::isIntegralType(logic_type type, Substitution substitution,
    Parser::Arguments& context) {
  if (context.isLogicSetType(type))
    return isIntegralType(context.type_of_element(type),substitution,context);
  if (type->tag_logic_type == LREFERENCE)
    type = type->cons_logic_type.Lreference.subtype;
  if ((type->tag_logic_type == LINT) || (type->tag_logic_type == LENUM))
    return true;
  if (type->tag_logic_type == LCNAMED)
    return context.isIntegralTypedefType(type->cons_logic_type.LCnamed.name);
  if (type->tag_logic_type == LINTEGER)
    return true;
  if (type->tag_logic_type == LNAMED) {
    bool hasAdvanced = false, doesAdvance;
    do {
      doesAdvance = false;
      GlobalContext::LogicType* typeDefinition
        = context.findGlobalLogicType(type->cons_logic_type.Lnamed.name);
      if (is_type_synonym(typeDefinition->type_info())) {
        /* string */ list formalParameters
            = typeDefinition->type_info()->params;
        /* logic_type */ list actualParameters
            = type->cons_logic_type.Lnamed.template_arguments;
        type = extract_synonym_def(typeDefinition->type_info());
        substitution.pushLevel();
        Substitution::MapLogicType& map = substitution.map();
        while (formalParameters) {
          if (actualParameters == NULL) {
            context.addErrorMessage("Logic type used with wrong number "
                "of parameters");
            assert(false);
          };
          map.insert(std::make_pair(
              std::string((const char*) formalParameters->element.container),
              (logic_type) actualParameters->element.container));
          formalParameters = formalParameters->next;
          actualParameters = actualParameters->next;
        };
        if (actualParameters != NULL) {
          context.addErrorMessage("Logic type used with "
              "wrong number of parameters");
          assert(false);
        };
        hasAdvanced = doesAdvance = true;
      };
    } while (doesAdvance && type->tag_logic_type == LNAMED);
    if (hasAdvanced)
      return isIntegralType(type, substitution, context);
  };
  if (type->tag_logic_type == LVARIABLE
      && !type->cons_logic_type.Lvariable.name->prequalification) {
    std::string name = type->cons_logic_type.Lvariable.name->decl_name;
    const Substitution::MapLogicType& map = substitution.map();
    Substitution::MapLogicType::const_iterator found = map.find(name);
    if (found == map.end())
      return false;
    type = found->second;
    substitution.popLevel();
    return isIntegralType(type, substitution, context);
  };
  return false;
}

bool
TermOrPredicate::isPlainPointerType(logic_type type, Substitution substitution,
    Parser::Arguments& context) {
  if (type->tag_logic_type == LREFERENCE)
    type = type->cons_logic_type.Lreference.subtype;
  if (isCPointerType(type, context))
    return true;
  if (type->tag_logic_type == LNAMED) {
    bool hasAdvanced = false, doesAdvance;
    do {
      doesAdvance = false;
      GlobalContext::LogicType* typeDefinition
        = context.findGlobalLogicType(type->cons_logic_type.Lnamed.name);
      if (is_type_synonym(typeDefinition->type_info())) {
        /* string */ list formalParameters
            = typeDefinition->type_info()->params;
        /* logic_type */ list actualParameters
            = type->cons_logic_type.Lnamed.template_arguments;
        type = extract_synonym_def(typeDefinition->type_info());
        substitution.pushLevel();
        Substitution::MapLogicType& map = substitution.map();
        while (formalParameters) {
          if (actualParameters == NULL) {
            context.addErrorMessage("Logic type used with "
                "wrong number of parameters");
            assert(false);
          };
          map.insert(std::make_pair(
              std::string((const char*) formalParameters->element.container),
              (logic_type) actualParameters->element.container));
          formalParameters = formalParameters->next;
          actualParameters = actualParameters->next;
        };
        if (actualParameters != NULL) {
          context.addErrorMessage("Logic type used with "
              "wrong number of parameters");
          assert(false);
        };
        hasAdvanced = doesAdvance = true;
      };
    } while (doesAdvance && type->tag_logic_type == LNAMED);
    if (hasAdvanced)
      return isPlainPointerType(type, substitution, context);
  };
  if (type->tag_logic_type == LVARIABLE
      && !type->cons_logic_type.Lvariable.name->prequalification) {
    std::string name = type->cons_logic_type.Lvariable.name->decl_name;
    const Substitution::MapLogicType& map = substitution.map();
    Substitution::MapLogicType::const_iterator found = map.find(name);
    if (found == map.end())
      return false;
    type = found->second;
    substitution.popLevel();
    return isPlainPointerType(type, substitution, context);
  };
  return false;
}

bool
TermOrPredicate::isPlainArrayType(logic_type type, Substitution substitution,
    Parser::Arguments& context) {
  if (type->tag_logic_type == LREFERENCE)
    type = type->cons_logic_type.Lreference.subtype;
  if (isCArrayType(type, context))
    return true;
  if (type->tag_logic_type == LNAMED) {
    bool hasAdvanced = false, doesAdvance;
    do {
      doesAdvance = false;
      GlobalContext::LogicType* typeDefinition
        = context.findGlobalLogicType(type->cons_logic_type.Lnamed.name);
      if (is_type_synonym(typeDefinition->type_info())) {
        /* string */ list formalParameters
            = typeDefinition->type_info()->params;
        /* logic_type */ list actualParameters
            = type->cons_logic_type.Lnamed.template_arguments;
          type = extract_synonym_def(typeDefinition->type_info());
        substitution.pushLevel();
        Substitution::MapLogicType& map = substitution.map();
        while (formalParameters) {
          if (actualParameters == NULL) {
            context.addErrorMessage("Logic type used with "
                "wrong number of parameters");
            assert(false);
          };
          map.insert(std::make_pair(
              std::string((const char*) formalParameters->element.container),
              (logic_type) actualParameters->element.container));
          formalParameters = formalParameters->next;
          actualParameters = actualParameters->next;
        };
        if (actualParameters != NULL) {
          context.addErrorMessage("Logic type used with "
              "wrong number of parameters");
          assert(false);
        };
        hasAdvanced = doesAdvance = true;
      };
    } while (doesAdvance && type->tag_logic_type == LNAMED);
    if (hasAdvanced)
      return isPlainArrayType(type, substitution, context);
  };
  if (type->tag_logic_type == LVARIABLE
      && !type->cons_logic_type.Lvariable.name->prequalification) {
    std::string name = type->cons_logic_type.Lvariable.name->decl_name;
    const Substitution::MapLogicType& map = substitution.map();
    Substitution::MapLogicType::const_iterator found = map.find(name);
    if (found == map.end())
      return false;
    type = found->second;
    substitution.popLevel();
    return isPlainArrayType(type, substitution, context);
  };
  return false;
}

qualified_name
TermOrPredicate::makePlainCompoundType(logic_type type,
    Substitution substitution, Parser::Arguments& context, tkind* templateKind)
{ if (type->tag_logic_type == LREFERENCE)
    return makePlainCompoundType(type->cons_logic_type.Lreference.subtype,
      substitution, context, templateKind);

  qualified_name result = makeCCompoundType(type, context, templateKind);
  if (result)
    return result;
  if (type->tag_logic_type == LNAMED) {
    bool hasAdvanced = false, doesAdvance;
    do {
      doesAdvance = false;
      GlobalContext::LogicType* typeDefinition
        = context.findGlobalLogicType(type->cons_logic_type.Lnamed.name);
      if (is_type_synonym(typeDefinition->type_info())) {
        /* string */ list formalParameters
            = typeDefinition->type_info()->params;
        /* logic_type */ list actualParameters
            = type->cons_logic_type.Lnamed.template_arguments;
          type = extract_synonym_def(typeDefinition->type_info());
        substitution.pushLevel();
        Substitution::MapLogicType& map = substitution.map();
        while (formalParameters) {
          if (actualParameters == NULL) {
            context.addErrorMessage("Logic type used with "
                "wrong number of parameters");
            assert(false);
          };
          map.insert(std::make_pair(
              std::string((const char*) formalParameters->element.container),
              (logic_type) actualParameters->element.container));
          formalParameters = formalParameters->next;
          actualParameters = actualParameters->next;
        };
        if (actualParameters != NULL) {
          context.addErrorMessage("Logic type used with "
              "wrong number of parameters");
          assert(false);
        };
        hasAdvanced = doesAdvance = true;
      };
    } while (doesAdvance && type->tag_logic_type == LNAMED);
    if (hasAdvanced)
      return makePlainCompoundType(type, substitution, context, templateKind);
  };
  if (type->tag_logic_type == LVARIABLE
      && !type->cons_logic_type.Lvariable.name->prequalification) {
    std::string name = type->cons_logic_type.Lvariable.name->decl_name;
    const Substitution::MapLogicType& map = substitution.map();
    Substitution::MapLogicType::const_iterator found = map.find(name);
    if (found == map.end())
      return NULL;
    type = found->second;
    substitution.popLevel();
    return makePlainCompoundType(type, substitution, context, templateKind);
  };
  return NULL;
}

bool
TermOrPredicate::isPointerType(logic_type ltype, Substitution substitution,
    Parser::Arguments& context) {
  while (ltype->tag_logic_type == LNAMED
      && strcmp(ltype->cons_logic_type.Lnamed.name->decl_name, "set") == 0
      && !ltype->cons_logic_type.Lnamed.name->prequalification
      && ltype->cons_logic_type.Lnamed.template_arguments
      && !ltype->cons_logic_type.Lnamed.template_arguments->next)
    ltype = (logic_type) ltype->cons_logic_type.Lnamed
        .template_arguments->element.container;
  return isPlainPointerType(ltype, substitution, context);
}

bool
TermOrPredicate::isArrayType(logic_type ltype, Substitution substitution,
    Parser::Arguments& context) {
  while (ltype->tag_logic_type == LNAMED
      && strcmp(ltype->cons_logic_type.Lnamed.name->decl_name, "set") == 0
      && !ltype->cons_logic_type.Lnamed.name->prequalification
      && ltype->cons_logic_type.Lnamed.template_arguments
      && !ltype->cons_logic_type.Lnamed.template_arguments->next)
    ltype = (logic_type) ltype->cons_logic_type.Lnamed
        .template_arguments->element.container;
  return isPlainArrayType(ltype, substitution, context);
}

qualified_name
TermOrPredicate::makeCompoundType(logic_type ltype, Substitution substitution,
    Parser::Arguments& context, tkind* templateKind) {
  while (ltype->tag_logic_type == LNAMED
      && strcmp(ltype->cons_logic_type.Lnamed.name->decl_name, "set") == 0
      && !ltype->cons_logic_type.Lnamed.name->prequalification
      && ltype->cons_logic_type.Lnamed.template_arguments
      && !ltype->cons_logic_type.Lnamed.template_arguments->next)
    ltype = (logic_type) ltype->cons_logic_type.Lnamed
        .template_arguments->element.container;
  return makePlainCompoundType(ltype, substitution, context, templateKind);
}

logic_type
TermOrPredicate::typeOfPointed(logic_type ltype, Substitution substitution,
    Parser::Arguments& context) {
  while (ltype->tag_logic_type == LNAMED
      && strcmp(ltype->cons_logic_type.Lnamed.name->decl_name, "set") == 0
      && !ltype->cons_logic_type.Lnamed.name->prequalification
      && ltype->cons_logic_type.Lnamed.template_arguments
      && !ltype->cons_logic_type.Lnamed.template_arguments->next)
    ltype = (logic_type) ltype->cons_logic_type.Lnamed
      .template_arguments->element.container;
  if (isCPointerType(ltype, context)) {
    if (ltype->tag_logic_type == LPOINTER)
      return logic_type_dup(ltype->cons_logic_type.Lpointer.subtype);
    assert(ltype->tag_logic_type == LCNAMED);
    return context.makeTypeOfPointed(ltype->cons_logic_type.LCnamed.name);
  };
  if (isCReferenceType(ltype, context)) {
    if (ltype->tag_logic_type == LREFERENCE)
      return logic_type_dup(ltype->cons_logic_type.Lreference.subtype);
    assert(ltype->tag_logic_type == LCNAMED);
    return context.makeTypeOfReferenced(ltype->cons_logic_type.LCnamed.name);
  };
  if (isCArrayType(ltype, context)) {
    if (ltype->tag_logic_type == LARRAY)
      return logic_type_dup(ltype->cons_logic_type.Larray.subtype);
    assert(ltype->tag_logic_type == LCNAMED);
    return context.makeTypeOfArrayElement(ltype->cons_logic_type.LCnamed.name);
  };
  if (ltype->tag_logic_type == LNAMED) {
    bool hasAdvanced = false, doesAdvance;
    do {
      doesAdvance = false;
      GlobalContext::LogicType* typeDefinition
        = context.findGlobalLogicType(ltype->cons_logic_type.Lnamed.name);
      if (typeDefinition && is_type_synonym(typeDefinition->type_info())) {
        /* string */ list formalParameters
            = typeDefinition->type_info()->params;
        /* logic_type */ list actualParameters
            = ltype->cons_logic_type.Lnamed.template_arguments;
          ltype = extract_synonym_def(typeDefinition->type_info());
        substitution.pushLevel();
        Substitution::MapLogicType& map = substitution.map();
        while (formalParameters) {
          if (actualParameters == NULL) {
            context.addErrorMessage("Logic type used with "
                "wrong number of parameters");
            assert(false);
          };
          map.insert(std::make_pair(
              std::string((const char*) formalParameters->element.container),
              (logic_type) actualParameters->element.container));
          formalParameters = formalParameters->next;
          actualParameters = actualParameters->next;
        };
        if (actualParameters != NULL) {
          context.addErrorMessage("Logic type used with "
              "wrong number of parameters");
          assert(false);
        };
        hasAdvanced = doesAdvance = true;
      };
    } while (doesAdvance && ltype->tag_logic_type == LNAMED);
    if (hasAdvanced)
      return typeOfPointed(ltype, substitution, context);
  };
  if (ltype->tag_logic_type == LVARIABLE
      && !ltype->cons_logic_type.Lvariable.name->prequalification) {
    std::string name = ltype->cons_logic_type.Lvariable.name->decl_name;
    const Substitution::MapLogicType& map = substitution.map();
    Substitution::MapLogicType::const_iterator found = map.find(name);
    if (found == map.end())
      return NULL;
    ltype = found->second;
    substitution.popLevel();
    return typeOfPointed(ltype, substitution, context);
  };
  context.addErrorMessage("type is not a pointer type");
  assert(false);
  return NULL;
}

logic_type
TermOrPredicate::typeOfArrayElement(logic_type ltype, Substitution substitution,
    Parser::Arguments& context) {
  while (ltype->tag_logic_type == LNAMED
      && strcmp(ltype->cons_logic_type.Lnamed.name->decl_name, "set") == 0
      && !ltype->cons_logic_type.Lnamed.name->prequalification
      && ltype->cons_logic_type.Lnamed.template_arguments
      && !ltype->cons_logic_type.Lnamed.template_arguments->next)
    ltype = (logic_type) ltype->cons_logic_type.Lnamed
        .template_arguments->element.container;
  if (ltype->tag_logic_type == LARRAY)
    return logic_type_dup(ltype->cons_logic_type.Larray.subtype);
  if (ltype->tag_logic_type == LPOINTER)
    return logic_type_dup(ltype->cons_logic_type.Lpointer.subtype);
  if (ltype->tag_logic_type == LCNAMED) {
    if (isCArrayType(ltype, context))
      return context.makeTypeOfPointed(ltype->cons_logic_type.LCnamed.name);
  };
  if (ltype->tag_logic_type == LNAMED) {
    bool hasAdvanced = false, doesAdvance;
    do {
      doesAdvance = false;
      GlobalContext::LogicType* typeDefinition
        = context.findGlobalLogicType(ltype->cons_logic_type.Lnamed.name);
      if (typeDefinition && is_type_synonym(typeDefinition->type_info())) {
        /* string */ list formalParameters
            = typeDefinition->type_info()->params;
        /* logic_type */ list actualParameters
            = ltype->cons_logic_type.Lnamed.template_arguments;
        ltype = extract_synonym_def(typeDefinition->type_info());
        substitution.pushLevel();
        Substitution::MapLogicType& map = substitution.map();
        while (formalParameters) {
          if (actualParameters == NULL) {
            context.addErrorMessage("Logic type used with "
                "wrong number of parameters");
            assert(false);
          };
          map.insert(std::make_pair(
              std::string((const char*) formalParameters->element.container),
              (logic_type) actualParameters->element.container));
          formalParameters = formalParameters->next;
          actualParameters = actualParameters->next;
        };
        if (actualParameters != NULL) {
          context.addErrorMessage("Logic type used with "
              "wrong number of parameters");
          assert(false);
        };
        hasAdvanced = doesAdvance = true;
      };
    } while (doesAdvance && ltype->tag_logic_type == LNAMED);
    if (hasAdvanced)
      return typeOfArrayElement(ltype, substitution, context);
  };
  if (ltype->tag_logic_type == LVARIABLE
      && !ltype->cons_logic_type.Lvariable.name->prequalification) {
    std::string name = ltype->cons_logic_type.Lvariable.name->decl_name;
    const Substitution::MapLogicType& map = substitution.map();
    Substitution::MapLogicType::const_iterator found = map.find(name);
    if (found == map.end())
      return NULL;
    ltype = found->second;
    substitution.popLevel();
    return typeOfArrayElement(ltype, substitution, context);
  };
  context.addErrorMessage("type is not a pointer type");
  assert(false);
  return NULL;
}

bool
TermOrPredicate::isPointerCharType(logic_type ltype, Substitution substitution,
    Parser::Arguments& context) {
  while (ltype->tag_logic_type == LNAMED
      && strcmp(ltype->cons_logic_type.Lnamed.name->decl_name, "set") == 0
      && !ltype->cons_logic_type.Lnamed.name->prequalification
      && ltype->cons_logic_type.Lnamed.template_arguments
      && !ltype->cons_logic_type.Lnamed.template_arguments->next)
    ltype = (logic_type) ltype->cons_logic_type.Lnamed
        .template_arguments->element.container;
  if (isCPointerType(ltype, context)) {
    if (ltype->tag_logic_type == LPOINTER) {
      if (ltype->cons_logic_type.Lpointer.subtype->tag_logic_type == LINT) {
        ikind kind = ltype->cons_logic_type.Lpointer
            .subtype->cons_logic_type.Lint.kind;
        return kind == ICHAR_U || kind == ICHAR_S
          || kind == IUCHAR || kind == ISCHAR;
      };
      return false;
    };
    assert(ltype->tag_logic_type == LCNAMED);
    bool result = false;
    logic_type subtype = context.makeTypeOfPointed(ltype->cons_logic_type
        .LCnamed.name);
    if (subtype->tag_logic_type == LINT) {
      ikind kind = subtype->cons_logic_type.Lint.kind;
      result = kind == ICHAR_U || kind == ICHAR_S
        || kind == IUCHAR || kind == ISCHAR;
    };
    free_logic_type(subtype);
    return result;
  };
  if (ltype->tag_logic_type == LNAMED) {
    bool hasAdvanced = false, doesAdvance;
    do {
      doesAdvance = false;
      GlobalContext::LogicType* typeDefinition
        = context.findGlobalLogicType(ltype->cons_logic_type.Lnamed.name);
      if (typeDefinition && is_type_synonym(typeDefinition->type_info())) {
        /* string */ list formalParameters
            = typeDefinition->type_info()->params;
        /* logic_type */ list actualParameters
            = ltype->cons_logic_type.Lnamed.template_arguments;
        ltype = extract_synonym_def(typeDefinition->type_info());
        substitution.pushLevel();
        Substitution::MapLogicType& map = substitution.map();
        while (formalParameters) {
          if (actualParameters == NULL) {
            context.addErrorMessage("Logic type used with "
                "wrong number of parameters");
            assert(false);
          };
          map.insert(std::make_pair(
              std::string((const char*) formalParameters->element.container),
              (logic_type) actualParameters->element.container));
          formalParameters = formalParameters->next;
          actualParameters = actualParameters->next;
        };
        if (actualParameters != NULL) {
          context.addErrorMessage("Logic type used with "
              "wrong number of parameters");
          assert(false);
        };
        hasAdvanced = doesAdvance = true;
      };
    } while (doesAdvance && ltype->tag_logic_type == LNAMED);
    if (hasAdvanced)
      return isPointerCharType(ltype, substitution, context);
  };
  if (ltype->tag_logic_type == LVARIABLE
      && !ltype->cons_logic_type.Lvariable.name->prequalification) {
    std::string name = ltype->cons_logic_type.Lvariable.name->decl_name;
    const Substitution::MapLogicType& map = substitution.map();
    Substitution::MapLogicType::const_iterator found = map.find(name);
    if (found == map.end())
      return false;
    ltype = found->second;
    substitution.popLevel();
    return isPointerCharType(ltype, substitution, context);
  };
  return false;
}

term
TermOrPredicate::logicCoerce(logic_type& ltype, term source) {
  if (source->node->tag_term_node == TCOMPREHENSION
      || source->node->tag_term_node == TUNION
      || source->node->tag_term_node == TINTER
      || source->node->tag_term_node == TEMPTY_SET) {
    if (!(ltype->tag_logic_type == LNAMED
        && strcmp(ltype->cons_logic_type.Lnamed.name->decl_name, "set") == 0
        && !ltype->cons_logic_type.Lnamed.name->prequalification
        && ltype->cons_logic_type.Lnamed.template_arguments
        && !ltype->cons_logic_type.Lnamed.template_arguments->next))
      ltype = make_set_type(ltype);

    if (source->node->tag_term_node == TCOMPREHENSION) {
      source->node->cons_term_node.TComprehension.subexpr =
        logicCoerce(ltype, source->node->cons_term_node.TComprehension.subexpr);
    }
    else if (source->node->tag_term_node == TUNION) {
      /* term */ list subiterator = source->node->cons_term_node.TUnion.tlist;
      while (subiterator != NULL) {
        subiterator->element.container = logicCoerce(ltype,
            (term) subiterator->element.container);
        subiterator = subiterator->next;
      };
    }
    else if (source->node->tag_term_node == TINTER) {
      /* term */ list subiterator = source->node->cons_term_node.TUnion.tlist;
      while (subiterator != NULL) {
        subiterator->element.container = logicCoerce(ltype,
            (term) subiterator->element.container);
        subiterator = subiterator->next;
      };
    };
    // else if (source->node->tag_term_node == TEMPTY_SET) {}
    return source;
  };
  logic_type lt_new = logic_type_dup(ltype);
  if (source->node->tag_term_node == TLOGIC_COERCE) {
    free_logic_type(source->node->cons_term_node.TLogic_coerce.result_type);
    source->node->cons_term_node.TLogic_coerce.result_type = lt_new;
    return source;
  };
  term result = term_cons(term_node_TLogic_coerce(lt_new, source),
      copy_loc(source->loc), NULL);
  return result;
}

logic_type
TermOrPredicate::isSetType(logic_type ltype) {
  return ((ltype->tag_logic_type == LNAMED)
      && strcmp(ltype->cons_logic_type.Lnamed.name->decl_name, "set") == 0
      && !ltype->cons_logic_type.Lnamed.name->prequalification
      && ltype->cons_logic_type.Lnamed.template_arguments
      && !ltype->cons_logic_type.Lnamed.template_arguments->next)
    ? (logic_type) ltype->cons_logic_type.Lnamed
        .template_arguments->element.container
    : NULL;
}

term
TermOrPredicate::makeCast(logic_type& ltype, term source, logic_type oldtype,
    Substitution substitutionThis, Substitution substitutionSource,
    Parser::Arguments& context) {
  GuardLogicType guardOldType(oldtype);
  if (isCompatibleType(oldtype, ltype, substitutionThis, substitutionSource,
      context))
    return source;
  if (source->node->tag_term_node == TCONST
      && source->node->cons_term_node.TConst.value->tag_logic_constant == LCENUM
      && ltype->tag_logic_type == LENUM
      && qualified_name_equal(source->node->cons_term_node.TConst.value
        ->cons_logic_constant.LCEnum.name, ltype->cons_logic_type.Lenum.name))
    return source;

  if (ltype->tag_logic_type == LNAMED) {
    if (context.is_builtin_boolean(ltype) &&
        isIntegralType(oldtype, substitutionSource, context)) {
      // (bool) x:int <=> x != 0
      logic_type internType = logic_type_Linteger();
      GuardLogicType guardType(internType);
      location locZero = copy_loc(source->loc);
      locZero->linenum2 = locZero->linenum1;
      locZero->charnum2 = locZero->charnum1;
      term_node node =
        term_node_TBinOp(
          BODIFFERENT,
          makeCast(
            internType,
            source, oldtype, Substitution(), substitutionSource, context),
          tzero(locZero));
      term result = term_cons(node, copy_loc(source->loc), NULL /* names */);
      oldtype = NULL;
      return result;
    };
    logic_type singletonType = isSetType(ltype);
    if (singletonType) {
      if (isPointerType(oldtype, substitutionSource, context)
          && isPointerCharType(singletonType, substitutionThis, context))
        return source;
      logic_type oldSingletonType = isSetType(oldtype);
      if (oldSingletonType) {
        free(oldtype->cons_logic_type.Lnamed.template_arguments);
        oldtype->cons_logic_type.Lnamed.template_arguments = NULL;
        free_logic_type(oldtype);
        oldtype = oldSingletonType;
        free(ltype->cons_logic_type.Lnamed.template_arguments);
        ltype->cons_logic_type.Lnamed.template_arguments = NULL;
        logic_type internType = logic_type_dup(singletonType);
        GuardLogicType guardType(internType);
        source = makeCast(internType, source, oldtype, substitutionThis,
            substitutionSource, context);
      }
      else {
        free(ltype->cons_logic_type.Lnamed.template_arguments);
        ltype->cons_logic_type.Lnamed.template_arguments = NULL;
        GuardLogicType guardType(singletonType);
        source = makeCast(singletonType, source, oldtype, substitutionThis,
            substitutionSource, context);
      };
      ltype = make_set_type(oldtype);
      oldtype = NULL;
      return source;
    };
    context.addErrorMessage("invalid cast");
    assert(false);
    return NULL;
  };

  if (isCType(ltype)) {
    if (isCType(oldtype))
      return applyTermCast(ltype, source, oldtype, context);
    if (oldtype->tag_logic_type == LINTEGER
        && isCPointerType(ltype, context)
        && (isLogicZero(source) || isLogicStrictNull(source)))
      return applyTermCast(ltype, source, oldtype, context);
    if (oldtype->tag_logic_type == LINTEGER && isIntegralType(ltype, context)) {
      context.addErrorMessage("term has a C type, "
          "but logic type integer is expected");
      assert(false);
      return NULL;
    };
    if (oldtype->tag_logic_type == LINTEGER || oldtype->tag_logic_type == LREAL)
    { context.addErrorMessage("invalid implicit cast "
        "from logic type to C type");
      assert(false);
      return NULL;
    }
  };

  if (isCType(oldtype)) {
    if (ltype->tag_logic_type == LINTEGER && isIntegralType(oldtype, context))
      return logicCoerce(ltype, source);
    if (ltype->tag_logic_type == LREAL && isArithmeticType(oldtype, context))
      return logicCoerce(ltype, source);
    context.addErrorMessage("invalid implicit cast from C type to logic type");
    assert(false);
    return NULL;
  };

  if (oldtype->tag_logic_type == LINTEGER) {
    if (ltype->tag_logic_type == LREAL) 
      return logicCoerce(ltype, source);
  };
  if (oldtype->tag_logic_type == LREAL) {
    if (ltype->tag_logic_type == LINTEGER) {
      context.addErrorMessage("invalid cast from real to integer. "
          "Use conversion functions instead");
      assert(false);
      return NULL;
    };
  };

  context.addErrorMessage("invalid cast");
  assert(false);
  return NULL;
}

term
TermOrPredicate::typeBoolTerm(logic_type& ltype, term source,
    Parser::Arguments& context) {
  if (!isPlainBooleanType(ltype, context)) {
    context.addErrorMessage("boolean expected");
    assert(false);
    return NULL;
  };
  logic_type internType = context.boolean_type();
  term result = makeCast(internType, source, ltype, Substitution(),
    Substitution(), context);
  ltype = internType;
  return result;
}

void
TermOrPredicate::addOffset(term_offset& source, term_offset shift) {
  switch (source->tag_term_offset) {
    case TNOOFFSET:
      free_term_offset(source);
      source = shift;
      break;
    case TFIELD:
      addOffset(source->cons_term_offset.TField.offset, shift);
      break;
    case TBASE:
      addOffset(source->cons_term_offset.TBase.offset, shift);
      break;
    case TVIRTUALBASE:
      addOffset(source->cons_term_offset.TVirtualBase.offset, shift);
      break;
    case TDERIVED:
      addOffset(source->cons_term_offset.TDerived.offset, shift);
      break;
    case TMODEL:
      addOffset(source->cons_term_offset.TModel.offset, shift);
      break;
    case TINDEX:
      addOffset(source->cons_term_offset.TIndex.offset, shift);
      break;
  };
}

term
TermOrPredicate::makeMemoryShift(logic_type ltype, term source,
    term_offset shift, location loc, logic_type& resultType,
    Parser::Arguments& context) {
  if (source->node->tag_term_node == TCOMPREHENSION
      || source->node->tag_term_node == TUNION
      || source->node->tag_term_node == TINTER
      || source->node->tag_term_node == TEMPTY_SET) {
    if (source->node->tag_term_node == TCOMPREHENSION) {
      source->node->cons_term_node.TComprehension.subexpr
        = makeMemoryShift(ltype, source->node->cons_term_node.TComprehension
            .subexpr, shift, loc, resultType, context);
    }
    else if (source->node->tag_term_node == TUNION) {
      /* term */ list subiterator = source->node->cons_term_node.TUnion.tlist;
      while (subiterator != NULL) {
        subiterator->element.container = makeMemoryShift(ltype,
            (term) subiterator->element.container, shift, loc, resultType,
            context);
        subiterator = subiterator->next;
      };
    }
    else if (source->node->tag_term_node == TINTER) {
      /* term */ list subiterator = source->node->cons_term_node.TUnion.tlist;
      while (subiterator != NULL) {
        subiterator->element.container = makeMemoryShift(ltype,
            (term) subiterator->element.container, shift, loc, resultType,
            context);
        subiterator = subiterator->next;
      };
    };
    // else if (source->node->tag_term_node == TEMPTY_SET) {}
    return source;
  };
  term_lval termVal;
  logic_type newtype = !resultType
      ? typeOfPointed(ltype, Substitution(), context) : resultType;
  if (source->node->tag_term_node == TADDROF) {
    termVal = source->node->cons_term_node.TAddrOf.subexpr;
    addOffset(termVal->offset, shift);
    source->node->cons_term_node.TAddrOf.subexpr = NULL;
    free_term(source);
  }
  else if (source->node->tag_term_node == TSTARTOF) {
    termVal = source->node->cons_term_node.TStartOf.subexpr;
    source->node->cons_term_node.TStartOf.subexpr = NULL;
    location zeroLoc = copy_loc(loc);
    zeroLoc->linenum2 = zeroLoc->linenum1;
    zeroLoc->charnum2 = zeroLoc->charnum1;
    addOffset(termVal->offset, term_offset_TIndex(tzero(zeroLoc),shift));
    free_term(source);
  }
  else
    termVal = term_lval_cons(term_lhost_TMem(source), shift);
  term result = term_cons(term_node_TLval(termVal), copy_loc(loc),
      NULL /* names */);
  if (!resultType)
    resultType = newtype;
  // names = NULL;
  return result;
}

term
TermOrPredicate::termLValAddressOf(logic_type ltype, term source, location loc,
    logic_type& lresultType, Parser::Arguments& context) {
  if (source->node->tag_term_node == TCOMPREHENSION
      || source->node->tag_term_node == TUNION
      || source->node->tag_term_node == TINTER
      || source->node->tag_term_node == TEMPTY_SET) {
    if (source->node->tag_term_node == TCOMPREHENSION) {
      source->node->cons_term_node.TComprehension.subexpr
        = termLValAddressOf(ltype, source->node->cons_term_node.TComprehension
            .subexpr, loc, lresultType, context);
    }
    else if (source->node->tag_term_node == TUNION) {
      /* term */ list subiterator = source->node->cons_term_node.TUnion.tlist;
      while (subiterator != NULL) {
        subiterator->element.container = termLValAddressOf(ltype,
            (term) subiterator->element.container, loc, lresultType, context);
        subiterator = subiterator->next;
      };
    }
    else if (source->node->tag_term_node == TINTER) {
      /* term */ list subiterator = source->node->cons_term_node.TUnion.tlist;
      while (subiterator != NULL) {
        subiterator->element.container = termLValAddressOf(ltype,
            (term) subiterator->element.container, loc, lresultType, context);
        subiterator = subiterator->next;
      };
    };
    // else if (source->node->tag_term_node == TEMPTY_SET) {}
    return source;
  };

  term_lval lval = NULL;
  bool doesCheckExitStatus = false;
  if (source->node->tag_term_node == TLVAL) {
    lval = source->node->cons_term_node.TLval.value;
    doesCheckExitStatus = true;
  }
  else if (source->node->tag_term_node == TCASTE
      && source->node->cons_term_node.TCastE.subexpr->node->tag_term_node
          == TLVAL) {
    lval = source->node->cons_term_node.TCastE.subexpr->node
      ->cons_term_node.TLval.value;
    doesCheckExitStatus = true;
  }
  else if (source->node->tag_term_node == TLOGIC_COERCE
      && source->node->cons_term_node.TLogic_coerce.code_type->node
          ->tag_term_node == TLVAL) {
    lval = source->node->cons_term_node.TLogic_coerce.code_type->node
        ->cons_term_node.TLval.value;
    doesCheckExitStatus = true;
  }
  else if (source->node->tag_term_node == TAT
      && source->node->cons_term_node.TAt.node->node->tag_term_node == TLVAL) {
    lval = source->node->cons_term_node.TAt.node->node
      ->cons_term_node.TLval.value;
    doesCheckExitStatus = true;
  }
  else if (source->node->tag_term_node == TSTARTOF)
    lval = source->node->cons_term_node.TStartOf.subexpr;
  else if (source->node->tag_term_node == TCASTE
      && source->node->cons_term_node.TCastE.subexpr->node->tag_term_node
          == TSTARTOF)
    lval = source->node->cons_term_node.TCastE.subexpr->node
      ->cons_term_node.TStartOf.subexpr;
  else if (source->node->tag_term_node == TAT
      && source->node->cons_term_node.TAt.node->node->tag_term_node == TSTARTOF)
    lval = source->node->cons_term_node.TAt.node->node
      ->cons_term_node.TStartOf.subexpr;
  if (lval) {
    if (doesCheckExitStatus && lval->base_support->tag_term_lhost == TVAR
        && !lval->base_support->cons_term_lhost.TVar.var
            ->lv_name->prequalification
        && strcmp(lval->base_support->cons_term_lhost.TVar.var
            ->lv_name->decl_name, "\\exit_status") == 0) {
      context.addErrorMessage("not an assignable left value");
      assert(false); // DefineAddError("not an assignable left value");
      return NULL;
      /* Tresult only exists when typing C functions and
        Tmem would lead to an error earlier if applied
        to pure logic expression.
       */
    };
    if (lval->offset->tag_term_offset == TMODEL) {
      context.addErrorMessage("Cannot take the address of model field");
      assert(false);
      return NULL;
    };
    if (lval->offset->tag_term_offset == TNOOFFSET
        && lval->base_support->tag_term_lhost == TMEM) {
      term result = lval->base_support->cons_term_lhost.TMem.subexpr;
      lval->base_support->cons_term_lhost.TMem.subexpr = NULL;
      lval->base_support->tag_term_lhost = (tag_term_lhost) (TMEM+1);
      free(result->loc);
      result->loc = copy_loc(loc);
      free_term(source);
      if (!lresultType)
        lresultType = logic_type_Lpointer(logic_type_dup(ltype));
      return result;
    };
    if (lval->offset->tag_term_offset == TINDEX
        && lval->offset->cons_term_offset.TIndex.offset->tag_term_offset
            == TNOOFFSET
        && isLogicZero(lval->offset->cons_term_offset.TIndex.subexpr)) {
      term_lhost base = lval->base_support;
      lval->base_support = term_lhost_TResult(logic_type_Lint(IINT));
      term_node nodeResult = term_node_TStartOf(term_lval_cons(base,
            term_offset_TNoOffset()));
      if (!lresultType)
        lresultType = logic_type_Lpointer(logic_type_dup(ltype)); /* array */
      term result = term_cons(nodeResult, copy_loc(loc), NULL /* names */);
      // names = NULL;
      return result;
    };

    term_node nodeResult = term_node_TAddrOf(term_lval_cons(lval->base_support,
          lval->offset));
    lval->base_support = term_lhost_TResult(logic_type_Lint(IINT));
    lval->offset = term_offset_TNoOffset();
    if (!lresultType)
      lresultType = logic_type_Lpointer(logic_type_dup(ltype)); /* array */
    term result = term_cons(nodeResult, copy_loc(loc), NULL /* names */);
    // names = NULL;
    return result;
  };
  context.addErrorMessage("not a left value");
  assert(false);
  return NULL;
}

bool
TermOrPredicate::retrieveTypeOfField(logic_type structType,
    const std::string& fieldName, term_offset& offset, logic_type& ltype,
    Parser::Arguments& context) {
  while (structType->tag_logic_type == LREFERENCE)
    structType = structType->cons_logic_type.Lreference.subtype;
  bool isSet = false;
  { logic_type singletonType = isSetType(structType);
    if (singletonType) {
      isSet = true;
      structType = singletonType;
    };
  };
  if (structType->tag_logic_type == LSTRUCT) {
    std::string errorMessage;
    if (!context.retrieveTypeOfField(structType->cons_logic_type.Lstruct.name,
        structType->cons_logic_type.Lstruct.template_kind,
        fieldName, offset, ltype, errorMessage)) {
      context.addErrorMessage(errorMessage);
      return false;
    };
  }
  else if (structType->tag_logic_type == LUNION) {
    std::string errorMessage;
    if (!context.retrieveTypeOfField(structType->cons_logic_type.Lunion.name,
        structType->cons_logic_type.Lunion.template_kind,
        fieldName, offset, ltype, errorMessage)) {
      context.addErrorMessage(errorMessage);
      return false;
    };
  }
  else if (structType->tag_logic_type == LCNAMED) {
    std::string errorMessage;
    if (!context.retrieveTypeOfField(
          structType->cons_logic_type.LCnamed.name,
          tkind_TStandard(), // LCnamed do not have any template information
          fieldName, offset, ltype, errorMessage)) {
      context.addErrorMessage(errorMessage);
      return false;
    }
  } else {
    context.addErrorMessage("expecting a struct with field");
    return context.fail();
  };

  if (isSet) ltype = make_set_type(ltype);
  return true;
}

term
TermOrPredicate::makeDot(term source, location loc, term_offset offset,
    Parser::Arguments& context) {
  if (source->node->tag_term_node == TCOMPREHENSION
      || source->node->tag_term_node == TUNION
      || source->node->tag_term_node == TINTER
      || source->node->tag_term_node == TEMPTY_SET) {
    if (source->node->tag_term_node == TCOMPREHENSION) {
      source->node->cons_term_node.TComprehension.subexpr
          = makeDot(source->node->cons_term_node.TComprehension.subexpr,
              loc, offset, context);
    }
    else if (source->node->tag_term_node == TUNION) {
      /* term */ list subiterator = source->node->cons_term_node.TUnion.tlist;
      while (subiterator != NULL) {
        subiterator->element.container = makeDot(
            (term) subiterator->element.container, loc, offset, context);
        subiterator = subiterator->next;
      };
    }
    else if (source->node->tag_term_node == TINTER) {
      /* term */ list subiterator = source->node->cons_term_node.TUnion.tlist;
      while (subiterator != NULL) {
        subiterator->element.container = makeDot(
            (term) subiterator->element.container, loc, offset, context);
        subiterator = subiterator->next;
      };
    };
    // else if (source->node->tag_term_node == TEMPTY_SET) {}
    return source;
  };

  if (source->node->tag_term_node == TLVAL) {
    addOffset(source->node->cons_term_node.TLval.value->offset, offset);
    return source;
  }
  else if (source->node->tag_term_node == TFIELDACCESS) {
    addOffset(source->node->cons_term_node.TFieldAccess.field, offset);
    return source;
  }
  else if (source->node->tag_term_node == TAT) {
    source->node->cons_term_node.TAt.node
      = makeDot(source->node->cons_term_node.TAt.node, loc, offset, context);
    return source;
  }
  source = term_cons(term_node_TFieldAccess(source, offset), copy_loc(loc),
      NULL);
  return source;
}

term
TermOrPredicate::makeMemory(term address, term_offset offset) {
  if (address->node->tag_term_node == TCOMPREHENSION
      || address->node->tag_term_node == TUNION
      || address->node->tag_term_node == TINTER
      || address->node->tag_term_node == TEMPTY_SET) {
    if (address->node->tag_term_node == TCOMPREHENSION) {
      address->node->cons_term_node.TComprehension.subexpr
        = makeMemory(address->node->cons_term_node.TComprehension.subexpr,
            offset);
    }
    else if (address->node->tag_term_node == TUNION) {
      /* term */ list subiterator = address->node->cons_term_node.TUnion.tlist;
      while (subiterator != NULL) {
        subiterator->element.container = makeMemory((term)
            subiterator->element.container, offset);
        subiterator = subiterator->next;
      };
    }
    else if (address->node->tag_term_node == TINTER) {
      /* term */ list subiterator = address->node->cons_term_node.TUnion.tlist;
      while (subiterator != NULL) {
        subiterator->element.container = makeMemory((term)
            subiterator->element.container, offset);
        subiterator = subiterator->next;
      };
    };
    // else if (address->node->tag_term_node == TEMPTY_SET) {}
    return address;
  };

  term_lval result = NULL;
  location resultLoc = copy_loc(address->loc);
  if (address->node->tag_term_node == TADDROF) {
    result = address->node->cons_term_node.TAddrOf.subexpr;
    address->node->cons_term_node.TAddrOf.subexpr = NULL;
    free_term(address);
    address = NULL;
    addOffset(result->offset, offset);
  }
  else if (address->node->tag_term_node == TSTARTOF) {
    result = address->node->cons_term_node.TStartOf.subexpr;
    address->node->cons_term_node.TStartOf.subexpr = NULL;
    free_term(address);
    address = NULL;
    location zeroLoc = copy_loc(address->loc);
    zeroLoc->linenum2 = zeroLoc->linenum1;
    zeroLoc->charnum2 = zeroLoc->charnum1;
    offset = term_offset_TIndex(tzero(zeroLoc), offset);
    addOffset(result->offset, offset);
  }
  else {
    result = term_lval_cons(term_lhost_TMem(address), offset);
    address = NULL;
  };
  return term_cons(term_node_TLval(result), resultLoc, NULL /* names */);
}

term
TermOrPredicate::makeShift(term memoryAccess, logic_type laccessType,
    term shift, location loc, Parser::Arguments& context) {
  if (memoryAccess->node->tag_term_node == TCOMPREHENSION
      || memoryAccess->node->tag_term_node == TUNION
      || memoryAccess->node->tag_term_node == TINTER
      || memoryAccess->node->tag_term_node == TEMPTY_SET) {
    if (memoryAccess->node->tag_term_node == TCOMPREHENSION) {
      memoryAccess->node->cons_term_node.TComprehension.subexpr
        = makeShift(memoryAccess->node->cons_term_node.TComprehension.subexpr,
            laccessType, shift, loc, context);
    }
    else if (memoryAccess->node->tag_term_node == TUNION) {
      /* term */ list subiterator = memoryAccess->node->cons_term_node.TUnion
          .tlist;
      while (subiterator != NULL) {
        subiterator->element.container = makeShift((term)
            subiterator->element.container, laccessType, shift, loc, context);
        subiterator = subiterator->next;
      };
    }
    else if (memoryAccess->node->tag_term_node == TINTER) {
      /* term */ list subiterator = memoryAccess->node
          ->cons_term_node.TUnion.tlist;
      while (subiterator != NULL) {
        subiterator->element.container = makeShift((term)
            subiterator->element.container, laccessType, shift, loc, context);
        subiterator = subiterator->next;
      };
    };
    // else if (memoryAccess->node->tag_term_node == TEMPTY_SET) {}
    return memoryAccess;
  };
  
  switch (memoryAccess->node->tag_term_node) {
    case TSTARTOF:
      { term_lval lval = memoryAccess->node->cons_term_node.TStartOf.subexpr;
        memoryAccess->node->cons_term_node.TStartOf.subexpr = NULL;
        free_term(memoryAccess);
        addOffset(lval->offset, term_offset_TIndex(shift,
              term_offset_TNoOffset()));
        return term_cons(term_node_TLval(lval), copy_loc(loc), NULL);
      };
    case TLVAL:
      { term_lval lval = memoryAccess->node->cons_term_node.TLval.value;
        addOffset(lval->offset, term_offset_TIndex(shift,
              term_offset_TNoOffset()));
        return memoryAccess;
      };
    case TLET:
      if (!isArrayType(laccessType, Substitution(), context))
        break;
      if (memoryAccess->node->cons_term_node.TLet.value->node->tag_term_node
          != TLVAL)
        break;
      { term_lval lval = memoryAccess->node->cons_term_node.TLet.value->node
            ->cons_term_node.TLval.value;
        addOffset(lval->offset, term_offset_TIndex(shift,
            term_offset_TNoOffset()));
        return memoryAccess;
      };
    case TAT:
      { term_node point = memoryAccess->node->cons_term_node.TAt.node->node;
        if (point->tag_term_node == TSTARTOF
            && point->cons_term_node.TStartOf.subexpr->base_support
                ->tag_term_lhost == TVAR
            && point->cons_term_node.TStartOf.subexpr->base_support
                ->cons_term_lhost.TVar.var->lv_kind == LVFORMAL
            /* && v.vformal && lab = old_label && env.Lenv.is_funspec */) {
          term_lval lval = point->cons_term_node.TStartOf.subexpr;
          point->cons_term_node.TStartOf.subexpr = NULL;
          logic_label lab = memoryAccess->node->cons_term_node.TAt.label;
          memoryAccess->node->cons_term_node.TAt.label = NULL;
          addOffset(lval->offset, term_offset_TIndex(
              /*makeAtHere(*/ shift /*)*/, term_offset_TNoOffset()));
          term result = term_cons(term_node_TAt(term_cons(term_node_TLval(lval),
              copy_loc(memoryAccess->node->cons_term_node.TAt.node->loc), NULL),
                lab), copy_loc(loc), NULL);
          free_term(memoryAccess->node->cons_term_node.TAt.node);
          free_term(memoryAccess);
          return result;
        };
        if (point->tag_term_node == TLVAL
            && point->cons_term_node.TLval.value->base_support->tag_term_lhost
                == TVAR
            && point->cons_term_node.TLval.value->base_support->cons_term_lhost
                .TVar.var->lv_kind == LVFORMAL
            /* && v.vformal && lab = old_label && env.Lenv.is_funspec */
            && isArrayType(laccessType, Substitution(), context)) {
          term_lval lval = point->cons_term_node.TLval.value;
          point->cons_term_node.TLval.value = NULL;
          logic_label lab = memoryAccess->node->cons_term_node.TAt.label;
          memoryAccess->node->cons_term_node.TAt.label = NULL;
          addOffset(lval->offset, term_offset_TIndex(
              /*makeAtHere(*/ shift /*)*/, term_offset_TNoOffset()));
          term result = term_cons(term_node_TAt(term_cons(term_node_TLval(lval),
              copy_loc(memoryAccess->node->cons_term_node.TAt.node->loc), NULL),
                  lab), copy_loc(loc), NULL);
          free_term(memoryAccess->node->cons_term_node.TAt.node);
          free_term(memoryAccess);
          return result;
        };
      };
      break;
    default:
      break;
  };
  return makeMemory(term_cons(term_node_TBinOp(BOPLUS, memoryAccess, shift),
      copy_loc(loc), NULL), term_offset_TNoOffset());
}

logic_type
TermOrPredicate::logicArithmeticConversion(logic_type t1, logic_type t2,
    Parser::Arguments& context) {
  if ((t1->tag_logic_type >= LINT && t1->tag_logic_type <= LCNAMED)
      && (t2->tag_logic_type >= LINT && t2->tag_logic_type <= LCNAMED)) {
    if (isIntegralType(t1, context) && isIntegralType(t2, context))
      return logic_type_Linteger();
    return logic_type_Lreal();
  };
  if (t1->tag_logic_type >= LINT && t1->tag_logic_type <= LCNAMED) {
    if (t2->tag_logic_type == LINTEGER) {
      if (isIntegralType(t1, context))
        return logic_type_Linteger();
      if (isArithmeticType(t1, context))
        return logic_type_Lreal();
    };
    if (t2->tag_logic_type == LREAL) {
      if (isArithmeticType(t1, context))
        return logic_type_Lreal();
    };
  };
  if (t2->tag_logic_type >= LINT && t2->tag_logic_type <= LCNAMED) {
    if (t1->tag_logic_type == LINTEGER) {
      if (isIntegralType(t2, context))
        return logic_type_Linteger();
      if (isArithmeticType(t2, context))
        return logic_type_Lreal();
    };
    if (t1->tag_logic_type == LREAL) {
      if (isArithmeticType(t2, context))
        return logic_type_Lreal();
    };
  };
  if (t1->tag_logic_type == LINTEGER && t2->tag_logic_type == LINTEGER)
    return logic_type_Linteger();
  if ((t1->tag_logic_type == LINTEGER || t1->tag_logic_type == LREAL)
      && (t2->tag_logic_type == LINTEGER || t2->tag_logic_type == LREAL))
    return logic_type_Lreal();
  if (isSetType(t1) && !isSetType(t2))
    return
      make_set_type(logicArithmeticConversion(remove_set_type(t1),t2,context));
  context.addErrorMessage("arithmetic conversion "
      "between non arithmetic types!");
  return NULL;
}

logic_type
TermOrPredicate::integralPromotion(logic_type ltype, Parser::Arguments& context)
{ if (ltype->tag_logic_type >= LINT && ltype->tag_logic_type <= LCNAMED) {
    if (isIntegralType(ltype, context))
      return logic_type_Linteger();
  };
  if (ltype->tag_logic_type == LINTEGER)
    return logic_type_Linteger();
  if (isSetType(ltype))
    return make_set_type(integralPromotion(remove_set_type(ltype),context));
  context.addErrorMessage("logic integral promotion on non-integral type.");
  return NULL;
}

logic_type
TermOrPredicate::carithmeticConversion(logic_type first, logic_type second,
    Parser::Arguments& context) { // c.f. ISO 6.3.1.8
  logic_type newFirst = NULL, newSecond = NULL;
  GuardLogicType guardFirst(newFirst), guardSecond(newSecond);
  if (first->tag_logic_type == LCNAMED)
    first = newFirst = context.logicArithmeticPromotion(first->cons_logic_type
        .LCnamed.name);
  if (second->tag_logic_type == LCNAMED)
    second = newSecond = context.logicArithmeticPromotion(second
        ->cons_logic_type.LCnamed.name);

  if ((first->tag_logic_type == LFLOAT)
      && first->cons_logic_type.Lfloat.kind == FLONGDOUBLE)
    return logic_type_dup(first);
  if ((second->tag_logic_type == LFLOAT)
      && second->cons_logic_type.Lfloat.kind == FLONGDOUBLE)
    return logic_type_dup(second);
  if ((first->tag_logic_type == LFLOAT)
      && first->cons_logic_type.Lfloat.kind == FDOUBLE)
    return logic_type_dup(first);
  if ((second->tag_logic_type == LFLOAT)
      && second->cons_logic_type.Lfloat.kind == FDOUBLE)
    return logic_type_dup(second);
  if (first->tag_logic_type == LFLOAT)
    return logic_type_dup(first);
  if (second->tag_logic_type == LFLOAT)
    return logic_type_dup(second);
  
  assert((first->tag_logic_type == LINT || first->tag_logic_type == LENUM)
      && (second->tag_logic_type == LINT || second->tag_logic_type == LENUM));
  ikind ifirst = (first->tag_logic_type == LINT)
            ? first->cons_logic_type.Lint.kind : IINT,
        isecond = (second->tag_logic_type == LINT)
            ? second->cons_logic_type.Lint.kind : IINT;
  if (ifirst == IULONG)
    return logic_type_dup(first);
  if (isecond == IULONG)
    return logic_type_dup(second);
  if (ifirst == ILONG)
    return isSignedInteger(second, context) ? logic_type_dup(first)
        : logic_type_Lint(IULONG);
  if (isecond == ILONG)
    return isSignedInteger(first, context) ? logic_type_dup(second)
        : logic_type_Lint(IULONG);
  bool isFirstSigned = isSignedInteger(first, context),
      isSecondSigned = isSignedInteger(second, context);
  if (!isFirstSigned || !isSecondSigned)
    return logic_type_Lint(IUINT);
  return logic_type_Lint(IINT);
}

logic_type
TermOrPredicate::conditionalConversion(logic_type first, logic_type second,
    Parser::Arguments& context) {
  logic_type commonType = isCompatibleType(first, second, Substitution(),
      Substitution(), context);
  if (commonType)
    return logic_type_dup(commonType);
  while (first->tag_logic_type == LREFERENCE)
     first = first->cons_logic_type.Lreference.subtype;
  while (second->tag_logic_type == LREFERENCE)
     second = second->cons_logic_type.Lreference.subtype;
  if ((first->tag_logic_type >= LINT && first->tag_logic_type <= LCNAMED)
      && (second->tag_logic_type >= LINT && second->tag_logic_type <= LCNAMED))
  { if (isIntegralType(first, Substitution(), context)
        && isIntegralType(second, Substitution(), context)) {
      if (isSignedInteger(first, context) != isSignedInteger(second, context))
        return logic_type_Linteger();
      return carithmeticConversion(first, second, context);
    }
    if (isArithmeticType(first, context) && isArithmeticType(second, context))
      return logic_type_Lreal();
    if (isPointerType(first, Substitution(), context)) {
      if (isPointerType(second, Substitution(), context)) {
        logic_type subtypeFirst = typeOfPointed(first, Substitution(), context);
        logic_type subtypeSecond = typeOfPointed(second, Substitution(),
            context);
        GuardLogicType guardFirst(subtypeFirst), guardSecond(subtypeSecond);
        if (isSameType(subtypeFirst, subtypeSecond, Substitution(),
              Substitution(), context))
          return logic_type_dup(first);
      };
      if (isIntegralType(second, Substitution(), context))
        return logic_type_dup(first);
      if (isArrayType(second, Substitution(), context)) {
        context.addErrorMessage("pointer types are not convertibles!");
        return NULL;
      };
    }
    else if (isPointerType(second, Substitution(), context)) {
      if (isIntegralType(first, Substitution(), context))
        return logic_type_dup(second);
    };
    if (isArrayType(first, Substitution(), context)) {
      if (isArrayType(second, Substitution(), context)) {
        logic_type subtypeFirst = typeOfArrayElement(first,
            Substitution(), context);
        logic_type subtypeSecond = typeOfArrayElement(second,
            Substitution(), context);
        GuardLogicType guardFirst(subtypeFirst), guardSecond(subtypeSecond);
        if (isSameType(subtypeFirst, subtypeSecond, Substitution(),
              Substitution(), context))
          return logic_type_dup(first);

        context.addErrorMessage("array types are not convertibles!");
        return NULL;
      };
    };
    context.addErrorMessage("invalid implicit conversion: " + str(second) + " to " + str(first)); // FIXME - not sure of order
    return NULL;
  };

  if (first->tag_logic_type == LINTEGER && (second->tag_logic_type >= LINT
        && second->tag_logic_type <= LCNAMED)) {
    if (isIntegralType(second, Substitution(), context))
      return logic_type_Linteger();
    if (isArithmeticType(second, context))
      return logic_type_Lreal();
  };
  if (second->tag_logic_type == LINTEGER && (first->tag_logic_type >= LINT
        && first->tag_logic_type <= LCNAMED)) {
    if (isIntegralType(first, Substitution(), context))
      return logic_type_Linteger();
    if (isArithmeticType(first, context))
      return logic_type_Lreal();
  };
  if (context.is_builtin_boolean(first) &&
      isIntegralType(second, Substitution(), context))
    return logic_type_dup(first);
  if (context.is_builtin_boolean(second) &&
      isIntegralType(first, Substitution(), context))
    return logic_type_dup(second);
  if (first->tag_logic_type == LREAL && (second->tag_logic_type >= LINT
        && second->tag_logic_type <= LCNAMED)) {
    if (isArithmeticType(second, context))
      return logic_type_Lreal();
  };
  if (second->tag_logic_type == LREAL && (first->tag_logic_type >= LINT
        && first->tag_logic_type <= LCNAMED)) {
    if (isArithmeticType(first, context))
      return logic_type_Lreal();
  };
  if (first->tag_logic_type == LNAMED && second->tag_logic_type == LNAMED) {
    if (qualified_name_equal(first->cons_logic_type.Lnamed.name,
          second->cons_logic_type.Lnamed.name)) {
      /* logic_type */ list firstArgIter
          = first->cons_logic_type.Lnamed.template_arguments;
      /* logic_type */ list secondArgIter
          = second->cons_logic_type.Lnamed.template_arguments;
      bool areEqual = true;
      while (areEqual && firstArgIter) {
        if (!secondArgIter)
          areEqual = false;
        else {
          areEqual = logic_type_equal(
              (logic_type) firstArgIter->element.container,
              (logic_type) secondArgIter->element.container);
          firstArgIter = firstArgIter->next;
          secondArgIter = secondArgIter->next;
        };
      };
      if (areEqual && !secondArgIter)
        return logic_type_dup(first);
    };
    if (isSetType(first)) {
      if (isSetType(second))
        return
          make_set_type(
            conditionalConversion(
              remove_set_type(first), remove_set_type(second), context));
      return
        make_set_type(
          conditionalConversion(remove_set_type(first),second,context));
    } else if (isSetType(second))
      return
        make_set_type(
          conditionalConversion(first,remove_set_type(second),context));
  }
  else if (first->tag_logic_type == LVARIABLE
      && second->tag_logic_type == LVARIABLE) {
    if (qualified_name_equal(first->cons_logic_type.Lvariable.name,
          second->cons_logic_type.Lvariable.name))
      return logic_type_dup(first);
  }
  else if (first->tag_logic_type == LINTEGER) {
    if (second->tag_logic_type == LINTEGER)
      return logic_type_Linteger();
    if (second->tag_logic_type == LREAL)
      return logic_type_Lreal();
  }
  else if (second->tag_logic_type == LINTEGER && first->tag_logic_type == LREAL)
    return logic_type_Lreal();
  context.addErrorMessage("types are not convertible");
  return NULL;
}

bool
TermOrPredicate::hasImplicitConversion(logic_type ltypeResult, term node,
    logic_type ltype, Parser::Arguments& context) {
  assert((ltype->tag_logic_type >= LINT && ltype->tag_logic_type <= LCNAMED)
        && (ltypeResult->tag_logic_type >= LINT
          && ltypeResult->tag_logic_type <= LCNAMED));

  logic_type newltypeResult = NULL, newltype = NULL;
  GuardLogicType guardResult(newltypeResult), guardArgument(newltype);
  if (ltype->tag_logic_type == LCNAMED)
    ltype = newltype = context.makeLogicType(ltype->cons_logic_type
        .LCnamed.name);
  if (ltypeResult->tag_logic_type == LCNAMED)
    ltypeResult = newltypeResult = context.makeLogicType(ltypeResult
        ->cons_logic_type.LCnamed.name);
  
  if ((ltype->tag_logic_type == LINT || ltype->tag_logic_type == LENUM)
      && (ltypeResult->tag_logic_type == LINT
        || ltypeResult->tag_logic_type == LENUM)) {
    if (ltype->tag_logic_type == LENUM)
      return ltypeResult->tag_logic_type >= LINT;
    if (ltypeResult->tag_logic_type == LENUM)
      return false;
    if ((int) ltype->cons_logic_type.Lint.kind
        == (int) ltypeResult->cons_logic_type.Lint.kind)
      return true;
    return
      compatible_int_kind(
        ltypeResult->cons_logic_type.Lint.kind,
        ltype->cons_logic_type.Lint.kind,
        context);
  };

  if (ltypeResult->tag_logic_type == LPOINTER) {
    if (ltype->tag_logic_type == LPOINTER) {
      if (isLogicNull(node))
        return true;
      if (isSameType(ltypeResult->cons_logic_type.Lpointer.subtype,
            ltype->cons_logic_type.Lpointer.subtype,
          Substitution(), Substitution(), context))
        return true;
      if (ltype->cons_logic_type.Lpointer.subtype->tag_logic_type == LVOID)
        return true;
    };
    return false;
  };
  if (ltypeResult->tag_logic_type == LARRAY) {
    if (ltype->tag_logic_type == LARRAY)
      return isSameType(ltypeResult->cons_logic_type.Larray.subtype,
            ltype->cons_logic_type.Larray.subtype,
          Substitution(), Substitution(), context);
    return false;
  };
  if (ltypeResult->tag_logic_type == LFLOAT)
    return (ltype->tag_logic_type == LFLOAT)
        && (ltypeResult->cons_logic_type.Lfloat.kind
            >= ltype->cons_logic_type.Lfloat.kind);
  return false;
}

term
TermOrPredicate::implicitConversion(logic_type& ltypeResult, term node,
    logic_type ltype, bool isOverloaded, Substitution substitutionFirst,
    Substitution substitutionSecond, Parser::Arguments& context, bool emitMsg) {
  if (ltype->tag_logic_type == LREFERENCE
      && ltypeResult->tag_logic_type != LREFERENCE) {
    do {
      ltype = ltype->cons_logic_type.Lreference.subtype;
    } while (ltype->tag_logic_type == LREFERENCE);
    // logic_type lresultType = NULL;
    // node = makeMemoryShift(ltype, node, term_offset_TNoOffset(),
    //     copy_loc(node->loc), lresultType, context);
    // free_logic_type(ltype);
    // ltype = lresultType;
  };
  if (ltypeResult->tag_logic_type == LNAMED || ltype->tag_logic_type == LNAMED)
  { bool hasAdvanced = false;
    bool doesAdvance;
    do {
      doesAdvance = false;
      if (ltypeResult->tag_logic_type == LNAMED &&
          !(isSetType(ltypeResult)||context.is_builtin_boolean(ltypeResult))) {
        GlobalContext::LogicType* typeDefinition = context.findGlobalLogicType(
            ltypeResult->cons_logic_type.Lnamed.name);
        if (typeDefinition && is_type_synonym(typeDefinition->type_info())) {
          /* string */ list formalParameters
              = typeDefinition->type_info()->params;
          /* logic_type */ list actualParameters
              = ltypeResult->cons_logic_type.Lnamed.template_arguments;
          ltypeResult = extract_synonym_def(typeDefinition->type_info());
          substitutionFirst.pushLevel();
          Substitution::MapLogicType& map = substitutionFirst.map();
          while (formalParameters) {
            if (actualParameters == NULL) {
              context.addErrorMessage("Logic type used "
                  "with wrong number of parameters");
              assert(false);
            };
            map.insert(std::make_pair(
                std::string((const char*) formalParameters->element.container),
                (logic_type) actualParameters->element.container));
            formalParameters = formalParameters->next;
            actualParameters = actualParameters->next;
          };
          if (actualParameters != NULL) {
            context.addErrorMessage("Logic type used "
                "with wrong number of parameters");
            assert(false);
          };
          hasAdvanced = doesAdvance = true;
        };
      };
      if (ltype->tag_logic_type == LNAMED
          && !(isSetType(ltype) || context.is_builtin_boolean(ltype))) {
        GlobalContext::LogicType* typeDefinition
          = context.findGlobalLogicType(ltype->cons_logic_type.Lnamed.name);
        if (is_type_synonym(typeDefinition->type_info())) {
          /* string */ list formalParameters
              = typeDefinition->type_info()->params;
          /* logic_type */ list actualParameters
              = ltype->cons_logic_type.Lnamed.template_arguments;
          ltype = extract_synonym_def(typeDefinition->type_info());
          substitutionSecond.pushLevel();
          Substitution::MapLogicType& map = substitutionSecond.map();
          while (formalParameters) {
            if (actualParameters == NULL) {
              context.addErrorMessage("Logic type used "
                  "with wrong number of parameters");
              assert(false);
            };
            map.insert(std::make_pair(
                std::string((const char*) formalParameters->element.container),
                (logic_type) actualParameters->element.container));
            formalParameters = formalParameters->next;
            actualParameters = actualParameters->next;
          };
          if (actualParameters != NULL) {
            context.addErrorMessage("Logic type used "
                "with wrong number of parameters");
            assert(false);
          };
          hasAdvanced = doesAdvance = true;
        };
      };
    } while (doesAdvance);
    if (hasAdvanced)
      return implicitConversion(ltypeResult, node, ltype,
         isOverloaded, substitutionFirst, substitutionSecond, context, emitMsg);
  };
  if (ltypeResult->tag_logic_type == LVARIABLE
      || ltype->tag_logic_type == LVARIABLE) {
    bool hasFirstVar = false, hasSecondVar = false;
    if (ltypeResult->tag_logic_type == LVARIABLE
        && !ltypeResult->cons_logic_type.Lvariable.name->prequalification) {
      // LVFormal type variable ?
      std::string name = ltypeResult->cons_logic_type.Lvariable.name->decl_name;
      const Substitution::MapLogicType& map = substitutionFirst.map();
      Substitution::MapLogicType::const_iterator found = map.find(name);
      if (found != map.end()) {
        hasFirstVar = true;
        ltypeResult = found->second;
      };
    };
    if (ltype->tag_logic_type == LVARIABLE
        && !ltype->cons_logic_type.Lvariable.name->prequalification) {
      // LVFormal type variable ?
      std::string name = ltype->cons_logic_type.Lvariable.name->decl_name;
      const Substitution::MapLogicType& map = substitutionSecond.map();
      Substitution::MapLogicType::const_iterator found = map.find(name);
      if (found != map.end()) {
        hasSecondVar = true;
        ltype = found->second;
      };
    };
    if (hasFirstVar || hasSecondVar) {
      if (hasFirstVar)
        substitutionFirst.popLevel();
      if (hasSecondVar)
        substitutionSecond.popLevel();
      return implicitConversion(ltypeResult, node, ltype,
         isOverloaded, substitutionFirst, substitutionSecond, context, emitMsg);
    };
  };
  
  if (isPointerType(ltypeResult,substitutionFirst,context) &&
      ltype->tag_logic_type == LARROW) {
    if (isCompatibleType(
          ltypeResult,ltype,substitutionFirst, substitutionSecond,context)) {
      return term_dup(node);
    } else {
      if (emitMsg) context.addErrorMessage(
        "incompatible conversion between pointer and function");
      return NULL;
    }
  }
  
  // Conversion from logic boolean type to C++ integral type
  // (possibly including bool). Use x?1:0 instead of (ctype)x.
  if (isIntegralType(ltypeResult,context) && context.is_builtin_boolean(ltype)){
    if (context.is_builtin_boolean(ltypeResult))
      return node;
    term zero = tzero(node->loc);
    term one = tone(node->loc);
    term result =
      term_cons(term_node_TIf(node,one,zero), copy_loc(node->loc),NULL);
    if (isCType(ltypeResult)) {
      result =
        term_cons(
          term_node_TCastE(logic_type_dup(ltypeResult),result),
          copy_loc(node->loc),NULL);
    }
    return result;
  };

  if (ltype->tag_logic_type >= LINT && ltype->tag_logic_type <= LCNAMED) {
    if (ltypeResult->tag_logic_type >= LINT
        && ltypeResult->tag_logic_type <= LCNAMED) {
      if (isSameType(ltypeResult, ltype, substitutionFirst, substitutionSecond,
            context))
        return node;
      if (hasImplicitConversion(ltypeResult, node, ltype, context)) {
        logic_type ltypeCopy = ltype;
        ltype = NULL;
        logic_type castType = logic_type_dup(ltypeResult);
        return applyTermCast(castType, node, ltypeCopy, context);
      };
      if (isOverloaded)
        return NULL;
      if (isArrayType(ltype, Substitution(), context)
          && isPointerType(ltypeResult, Substitution(), context)) {
        logic_type fst = typeOfPointed(ltype, Substitution(), context);
        logic_type snd = typeOfArrayElement(ltypeResult, Substitution(),
            context);
        GuardLogicType guardFst(fst), guardSnd(snd);
        if (isSameType(fst, snd, Substitution(), Substitution(), context)) {
          if (isCArray(node,ltype,context)) {
            if (emitMsg) context.addErrorMessage(
              "In ACSL, there is no implicit conversion between \
               a C array and a pointer. Either introduce an explicit \
               cast or take the address of the first element of the \
               converted term");
            return NULL;
          };
          if (emitMsg) context.addErrorMessage(
            "The converted term is a logic array. Only C arrays can be \
             converted to pointers, and this conversion must be \
             explicit (cast or take the address of the first element)");
          return NULL;
        };
      };
      if (emitMsg) context.addErrorMessage("invalid implicit conversion: " + str(ltype) + " to " + str(ltypeResult));
      return NULL;
    };
    if (context.is_builtin_boolean(ltypeResult)) {
      if (isIntegralType(ltype, context))
        return term_cons(term_node_TLogic_coerce(logic_type_dup(ltypeResult),
              node), copy_loc(node->loc), NULL);
    };
    if (ltypeResult->tag_logic_type == LINTEGER) {
      if (isIntegralType(ltype, context))
        return term_cons(term_node_TLogic_coerce(logic_type_dup(ltypeResult),
              node), copy_loc(node->loc), NULL);
    }
    else if (ltypeResult->tag_logic_type == LREAL) {
      if (isArithmeticType(ltype, context))
        return term_cons(term_node_TLogic_coerce(logic_type_dup(ltypeResult),
              node), copy_loc(node->loc), NULL);
    };
  }
  else if (ltype->tag_logic_type == LINTEGER) {
    if (ltypeResult->tag_logic_type == LINTEGER)
      return node;
    if (ltypeResult->tag_logic_type == LREAL)
      return term_cons(term_node_TLogic_coerce(logic_type_dup(ltypeResult),
            node), copy_loc(node->loc), NULL);
    if (context.is_builtin_boolean(ltypeResult))
      return term_cons(term_node_TLogic_coerce(logic_type_dup(ltypeResult),
            node), copy_loc(node->loc), NULL);
    if (ltypeResult->tag_logic_type >= LINT
        && ltypeResult->tag_logic_type <= LCNAMED) {
      if (isPointerType(ltypeResult, Substitution(), context)
          && isLogicNull(node))
        return term_cons(term_node_TCastE(logic_type_dup(ltypeResult), node),
            copy_loc(node->loc), NULL);
    };
  }
  else if (context.is_builtin_boolean(ltype)) {
    if (context.is_builtin_boolean(ltypeResult))
      return node;
    if (ltypeResult->tag_logic_type == LINTEGER
        || ltypeResult->tag_logic_type == LREAL)
      return term_cons(term_node_TLogic_coerce(logic_type_dup(ltypeResult),
            node), copy_loc(node->loc), NULL);
    if (ltypeResult->tag_logic_type >= LINT
        && ltypeResult->tag_logic_type <= LCNAMED) {
      if (isIntegralType(ltypeResult, context))
        return term_cons(term_node_TCastE(logic_type_dup(ltypeResult), node),
            copy_loc(node->loc), NULL);
      if (isPointerType(ltypeResult, Substitution(), context)
          && isLogicNull(node))
        return term_cons(term_node_TCastE(logic_type_dup(ltypeResult), node),
            copy_loc(node->loc), NULL);
    };
  };
  if (isSetType(ltypeResult)) {
    if (isPointerType(ltype, Substitution(), context)
        && isPlainPointerType((logic_type) ltypeResult
          ->cons_logic_type.Lnamed.template_arguments->element.container,
        Substitution(), context)) {
      logic_type pointed = typeOfPointed(ltype, Substitution(), context);
      GuardLogicType guardPointed(pointed);
      if (pointed->tag_logic_type == LINT
          && pointed->cons_logic_type.Lint.kind >= ICHAR_U
          && pointed->cons_logic_type.Lint.kind <= ISCHAR)
        return node;
    };
    logic_type lsubtypeResult=
        (logic_type) ltypeResult->cons_logic_type.
          Lnamed.template_arguments->element.container;
    term result = implicitConversion(lsubtypeResult, node, ltype,
        isOverloaded, substitutionFirst, substitutionSecond, context);
    ltypeResult->cons_logic_type.
          Lnamed.template_arguments->element.container = lsubtypeResult;

    if (lsubtypeResult) free_logic_type(lsubtypeResult);
    return result;
  };
  if (ltypeResult->tag_logic_type == LNAMED
      && ltype->tag_logic_type == LNAMED) {
    if (qualified_name_equal(ltypeResult->cons_logic_type.Lnamed.name,
          ltype->cons_logic_type.Lnamed.name))
      return node; // ltypeResult could change
  };
  if (ltype->tag_logic_type == LREAL && ltypeResult->tag_logic_type == LREAL)
    return node;
  if (ltype->tag_logic_type == LVARIABLE
      && ltypeResult->tag_logic_type == LVARIABLE
      && qualified_name_equal(ltype->cons_logic_type.Lvariable.name,
          ltypeResult->cons_logic_type.Lvariable.name))
    return node;
  if (ltype->tag_logic_type == LARROW && ltypeResult->tag_logic_type == LARROW)
    return node;
  if (emitMsg) context.addErrorMessage("invalid implicit conversion: " + str(ltype) + " to " + str(ltypeResult));
  return NULL;
}

term
TermOrPredicate::implicitConversion(logic_type& ltypeResult, term node,
    logic_type ltype, bool isOverloaded, Parser::Arguments& context)
{ return implicitConversion(ltypeResult, node, ltype, isOverloaded,
      Substitution(), Substitution(), context);
}

bool
TermOrPredicate::isLogicVoidPointerType(logic_type ltype,
    Parser::Arguments& context) {
  if (ltype->tag_logic_type == LCNAMED) {
    logic_type type = context.makeLogicType(ltype->cons_logic_type
        .LCnamed.name);
    GuardLogicType guardType(type);
    return type->tag_logic_type == LPOINTER
      && type->cons_logic_type.Lpointer.subtype->tag_logic_type == LVOID;
  }
  else if (ltype->tag_logic_type == LPOINTER) {
    if (ltype->cons_logic_type.Lpointer.subtype->tag_logic_type == LVOID)
      return true;
    if (ltype->cons_logic_type.Lpointer.subtype->tag_logic_type == LCNAMED) {
      logic_type type = context.makeLogicType(ltype->cons_logic_type
          .Lpointer.subtype->cons_logic_type.LCnamed.name);
      GuardLogicType guardType(type);
      return type->tag_logic_type == LVOID;
    };
  };
  return false;
}

void
TermOrPredicate::applyOverloadOperatorIfAny(Operator& operation,
    Parser::Arguments& context) {
  logic_type ltypeArgument = NULL;
  term targument = NULL;
  predicate_named pargument = NULL;
  operation.retrieveFirstArgument(ltypeArgument, targument, pargument);
  if (ltypeArgument && ltypeArgument->tag_logic_type >= LARRAY) {
    DLexer::OperatorPunctuatorToken concreteToken
      = operation.queryOperatorToken();
    std::ostringstream name;
    name << "operator";
    concreteToken.writeSign(name);
    OperatorPunctuatorToken::Type operatorType = concreteToken.getType();
    if (operatorType == OperatorPunctuatorToken::TOpenBracket)
      name << ']';
    else if (operatorType == OperatorPunctuatorToken::TOpenParen)
      name << ')';
    GlobalContext::NestedContext*
      foundLogic = context.findLogicName(name.str());
    if (!foundLogic) {
      tkind templateParameters = NULL;
      qualified_name classArgument = getClassType(ltypeArgument,
          &templateParameters);
      if (classArgument)
        foundLogic = context.findLogicName(classArgument, name.str(),
            &templateParameters);
    };
    if (foundLogic && foundLogic->isOverloadedLogicFunctions()
        && foundLogic->asOverloadedLogicFunctions().isOperator()) {
      Functions::const_iterator logicFunctionsEnd
        = foundLogic->asOverloadedLogicFunctions().getFunctions().end();
      logic_info candidate = NULL;
      bool isMethodCandidate = false;
      int argumentsNumber = operation.queryArgumentsNumber();
      logic_type ltypeSecondArgument = NULL;
      term tsecondArgument = NULL;
      predicate_named psecondArgument = NULL;
      bool isOk = true;
      if (argumentsNumber > 1) {
        operation.retrieveSecondArgument(ltypeSecondArgument, tsecondArgument,
            psecondArgument);
        isOk = ltypeSecondArgument && tsecondArgument;
      }
      for (Functions::const_iterator logicFunctionsIter
            = foundLogic->asOverloadedLogicFunctions().getFunctions().begin();
          isOk && logicFunctionsIter != logicFunctionsEnd; ++logicFunctionsIter)
      { /* logic_arg_decl */ list arguments
            = logicFunctionsIter->second->profile;
        assert(arguments && ((argumentsNumber == 1) ?
            !arguments->next : (bool) arguments->next));
        logic_type ltypeArgumentFunction = ((logic_arg_decl)
            arguments->element.container)->la_type;
        if (logicFunctionsIter->first) {
          assert(ltypeArgumentFunction->tag_logic_type == LPOINTER);
          ltypeArgumentFunction = ltypeArgumentFunction->cons_logic_type
              .Lpointer.subtype;
        };
        // logic_type_inherits
        if
          (logic_type_compatible(
            ltypeArgument,
            ltypeArgumentFunction,
            context)
           ) {
          if (argumentsNumber == 1) {
            if (!candidate) {
              candidate = logicFunctionsIter->second;
              isMethodCandidate = logicFunctionsIter->first;
            }
            else {
              context.addErrorMessage(
                std::string("multiple overload operator for ") + name.str());
              return;
            };
          }
          else {
            logic_type ltypeSecondArgumentFunction = ((logic_arg_decl)
                arguments->next->element.container)->la_type;
            if
              (logic_type_compatible(
                ltypeSecondArgument,
                ltypeSecondArgumentFunction,
                context))
              {
                if (!candidate) {
                  candidate = logicFunctionsIter->second;
                  isMethodCandidate = logicFunctionsIter->first;
                }
                else {
                  context.addErrorMessage(
                    std::string("multiple overload operator for ")
                    + name.str());
                  return;
                };
              };
          };
        }
      };
      if (candidate) {
        if (!isMethodCandidate)
          operation._type = Operator::TCall;
        else
          operation._type = Operator::TStructCall;
        operation._leftSubExpressions = 0;
        if (operation._pfirstArgument) {
          free_predicate_named(operation._pfirstArgument);
          operation._pfirstArgument = NULL;
        };
        if (operation._psecondArgument) {
          free_predicate_named(operation._psecondArgument);
          operation._psecondArgument = NULL;
        };
        assert(operation._ltypeFirstArgument && operation._tfirstArgument);
        if (!isMethodCandidate)
          operation._arguments.push_back(std::make_pair(
              operation._ltypeFirstArgument, operation._tfirstArgument));
        if (argumentsNumber > 1) {
          assert(operation._ltypeSecondArgument && operation._tsecondArgument);
          operation._arguments.push_back(std::make_pair(
                operation._ltypeSecondArgument, operation._tsecondArgument));
        };
        operation.setIdentifier(foundLogic);
        if (!operation._startLocation) {
          operation._startLocation = copy_loc(operation._tfirstArgument->loc);
          if (argumentsNumber > 1)
            extend_location_with(operation._startLocation,
                operation._tsecondArgument->loc);
        };
        if (!isMethodCandidate) {
          operation._tfirstArgument = NULL;
          operation._ltypeFirstArgument = NULL;
        };
        operation._tsecondArgument = NULL;
        operation._ltypeSecondArgument = NULL;
      };
    };
  };
}

  logic_info TermOrPredicate::disambiguate(
    const std::string& name, const Functions& possibleFunctions,
    Parser::Arguments& context) {
  Functions::const_iterator it = possibleFunctions.begin();
  logic_info best = NULL; // in case the list is empty, we return NULL anyway
  while (it != possibleFunctions.end()) {
    if (!best) { best = it->second; it++; continue; } // first element
    list curr_params = best->profile;
    list it_params = it->second->profile;
    int score = 0;
    // -1 implies that maxFound is more precise than current,
    //  0 that both are currently equivalent
    // +1 that current is more precise
    // We currently do not perform a sophisticated verification here:
    // if for some formals maxFound is more precise than current and
    // for others it is the reverse, we decide that the call is 
    // ambiguous and fail.
    while(curr_params && it_params) {
      logic_type curr_type = 
        ((logic_arg_decl)curr_params->element.container)->la_type;
      logic_type it_type =
        ((logic_arg_decl)it_params->element.container)->la_type;
      curr_params = curr_params->next;
      it_params = it_params->next;
      if (logic_type_equal(curr_type,it_type)) continue;
      if
        (logic_type_compatible(curr_type,it_type, context)) {
        // it_type is more precise than curr_type
        if (score == -1) {
          context.addErrorMessage(
            "Ambiguity when choosing overloaded function " + name + ".");
          return NULL;
        }
        score = 1;
      } else if
          (logic_type_compatible(it_type, curr_type, context)) {
        // curr_type is more precise than it_type
        if (score == 1) {
          context.addErrorMessage(
            "Ambiguity when choosing overloaded function " + name + ".");
          return NULL;
        }
        score = -1;
      } else {
        // incompatible types
        context.addErrorMessage(
          "Ambiguity when choosing overloaded function " + name + ".");
        return NULL;
      }
    }
    if (score == 0) {
      // both functions are equivalent
      context.addErrorMessage(
        "Ambiguity when choosing overloaded function " + name + ".");
      return NULL;
    }
    if (score == 1) {
      // found a better candidate
      best = it->second;
    }
    it++;
  }
  return best;
}

/* term */ list TermOrPredicate::create_argument_list(
  Operator& operation, logic_info f, Parser::Arguments& context) {
  Operator::Type type = operation.getType();
  /* term */ list arguments = NULL, endArguments = NULL;
  if (operation._tfirstArgument) {
    assert(type == Operator::TStructCall || type == Operator::TArrowStructCall);
    // When calling a logic member function/predicate, the first
    // argument is an object. In case of a arrow call, we need to
    // dereference the pointer.
    if (type == Operator::TArrowStructCall) {
      logic_type ltypeResult = NULL;
      operation._tfirstArgument = makeMemoryShift(
        operation._ltypeFirstArgument, operation._tfirstArgument,
        term_offset_TNoOffset(),
        copy_loc(operation._tfirstArgument->loc), ltypeResult, context);
      operation._ltypeFirstArgument = ltypeResult;
    };
    arguments = endArguments =
      cons_container(operation._tfirstArgument, NULL);
    operation._tfirstArgument = NULL;
    free_logic_type(operation._ltypeFirstArgument);
    operation._ltypeFirstArgument = NULL;
  } else {
    // checks whether we have to insert an implicit this argument
    // if we are calling a member of the same class than ourselves.
    assert(type == Operator::TCall);
    logic_type thisType = context.queryThisType();
    /* qualification */ list id_qual = f->li_name->prequalification;
    if (thisType && id_qual) {
      if (is_same_qualification(context.createPrequalification(),id_qual))
        {
          arguments = endArguments =
            cons_container(
              term_cons(
                term_node_TLval(context.thisLval()),
                copy_loc(operation._startLocation),
                NULL),
              NULL);
          if (thisType->tag_logic_type == LPOINTER) {
            logic_type obj_type = thisType->cons_logic_type.Lpointer.subtype;
            thisType->cons_logic_type.Lpointer.subtype = NULL;
            free_logic_type(thisType);
            operation._ltypeFirstArgument = obj_type;
          }
          else {
            operation._ltypeFirstArgument = thisType;
          }
        }
    }
  }
  if (!operation._arguments.empty()) {
    std::list<std::pair<logic_type, term> >::iterator
      endIter = operation._arguments.end();
    std::list<std::pair<logic_type, term> >::iterator
      iter = operation._arguments.begin();
    /* logic_arg_decl */ list copyParams = f->profile;
    if (!arguments) {
      if (!isCompatibleType(
            ((logic_arg_decl) copyParams->element.container)->la_type,
            iter->first,
            Substitution(), Substitution(), context)) {
        logic_type argumentType = logic_type_dup(
          ((logic_arg_decl) copyParams->element.container)->la_type);
        iter->second =
          implicitConversion(
            argumentType, iter->second,
            iter->first, false, Substitution(), Substitution(), context);
        free_logic_type(argumentType);
      }
      else
        free_logic_type(iter->first);
      iter->first = NULL;
      arguments = endArguments = cons_container(iter->second, NULL);
      iter->second = NULL;
      ++iter;
    };
    copyParams = copyParams->next;
    while (iter != endIter) {
      if (!isCompatibleType(
            ((logic_arg_decl) copyParams->element.container)->la_type,
            iter->first, Substitution(), Substitution(), context))
        {
          logic_type argumentType = logic_type_dup(
            ((logic_arg_decl) copyParams->element.container)->la_type);
          iter->second =
            implicitConversion(
              argumentType, iter->second,
              iter->first, false, Substitution(), Substitution(),
              context);
          free_logic_type(argumentType);
        }
      else
        free_logic_type(iter->first);
      iter->first = NULL;
      endArguments->next = cons_container(iter->second, NULL);
      endArguments = endArguments->next;
      iter->second = NULL;
      ++iter;
      copyParams = copyParams->next;
    };
    operation._arguments.clear();
  };
  return arguments;
}

bool
TermOrPredicate::apply(Operator& operation, logic_type& ltypeResult,
    term& expressionResult, predicate_named& predicateResult,
    /*, bool& isRValue, bool& isConstant, int *intResult, double* doubleResult,
     */ Parser::Arguments& context, unsigned& possibleTypes) {
  // assert(operation._tfirstArgument != NULL
  //     || operation._pfirstArgument != NULL);
  // isConstant = operation.isConstant();
  if (operation.isOverloadable())
    applyOverloadOperatorIfAny(operation, context);
  if (operation.isCast()) {
    assert(operation._startLocation);
    logic_type resultType = operation.extractTypeCast();
    GuardLogicType guardType(resultType);
    logic_type ltypeArgument = NULL;
    term targument = NULL;
    predicate_named pargument = NULL;
    operation.extractLastArgument(ltypeArgument, targument, pargument
        /* , isRValue, intResult, doubleResult*/);
    
    // if (!isRValue) { ...
    //   targument = ...;
    //   pargument = ...;
    //   isRValue = true;
    // };
    if (!targument) {
      if (pargument) free_predicate_named(pargument);
      context.addErrorMessage("cannot use cast/coerce operator "
          "within a predicate");
      return false;
    };
    if (pargument) free_predicate_named(pargument);
    if (!isCType(resultType)) {
      context.addErrorMessage("cannot cast to logic type");
      return false;
    };
    logic_type cast_type = logic_type_dup(resultType);
    expressionResult = applyTermCast(cast_type, targument, ltypeArgument,
        context);
    expressionResult->loc->linenum1 = operation._startLocation->linenum1; 
    expressionResult->loc->charnum1 = operation._startLocation->charnum1; 
    free_location(operation._startLocation);
    operation._startLocation = NULL;
    free_logic_type(ltypeArgument);
    ltypeResult = resultType;
    resultType = NULL;

    // if (operation.isConstant()) {
    //   // assert(intResult && doubleResult);
    //   if (isFloating(argumentType)) {
    //     // if (!isFloating(resultType))
    //     //   *intResult = (int) *doubleResult;
    //   }
    //   else if (isFloating(resultType)) {
    //     // *doubleResult = (double) *intResult;
    //   };
    // };
    return true;
  };
  
  int argumentsNumber = operation.queryArgumentsNumber();

  Operator::Type type = operation.getType();
  if (type == Operator::TCall || type == Operator::TStructCall
      || type == Operator::TArrowStructCall) {
    assert(operation._startLocation);
    if (operation._identifier
        && operation._identifier->isOverloadedLogicFunctions()) {
      typedef GlobalContext::OverloadedLogicFunctions::Functions Functions;
      const Functions& possibleFunctions
        = operation._identifier->asOverloadedLogicFunctions().getFunctions();
      Functions::const_iterator f_iter = possibleFunctions.begin();
      Functions candidates;
      while(f_iter != possibleFunctions.end()) {
        logic_info candidate = f_iter->second;
        list params = candidate->profile;
        if (type == Operator::TStructCall || type == Operator::TArrowStructCall
            || (
              context.queryThisType() && candidate->li_name->prequalification &&
              is_same_qualification(context.createPrequalification(),
                                    candidate->li_name->prequalification))
            )
          { // first param is for the this pointer. discard it
            if (!params) {
              context.addErrorMessage(
                operation._identifier->getName() +
                " is a member function but has no implicit this argument.");
              return false; }
            params = params->next;
          }
        std::list<std::pair<logic_type, term> >::iterator
          endIter = operation._arguments.end();
        std::list<std::pair<logic_type, term> >::iterator
          iter = operation._arguments.begin();
        while (iter != endIter && params != NULL) {
          if (!isCompatibleType(
                ((logic_arg_decl) params->element.container)->la_type,
                iter->first,
                Substitution(), Substitution(), context)) {
            logic_type argumentType = logic_type_dup(
              ((logic_arg_decl) params->element.container)->la_type);
            term convert =
              implicitConversion(
                argumentType, iter->second,
                iter->first, true, Substitution(), Substitution(), 
                context, false);
            free_logic_type(argumentType);
            if (!convert) break; // candidate is not suitable.
          }
          ++iter;
          params = params->next;
        };
        if (iter == endIter && params == NULL)
          // we have a compatible candidate
          candidates.push_back(*f_iter);
        f_iter++;
      };
      if (candidates.empty()) {
        context.addErrorMessage(
          "No suitable candidate found for function " +
          operation._identifier->getName() + ".");
        return false;
      }
      logic_info f =
        disambiguate(operation._identifier->getName(),candidates,context);
      if (!f) return false;
      list arguments = create_argument_list(operation,f,context);
      /* logic_label_pair */ list labelsTable = NULL;
      if (operation._labelsArguments) {
        if (!f->arg_labels) {
          context.addErrorMessage("The logic function "
            + operation._identifier->getName()
            + " does not hold any label argument.");
        }
        else {
          /* logic_label */ list labelParameters = f->arg_labels;
          ForwardReferenceList labelsTableList(labelsTable);
          while (operation._labelsArguments && labelParameters) {
            labelsTableList.insertContainer(logic_label_pair_cons(
              logic_label_dup((logic_label) labelParameters->element.container),
              (logic_label) operation._labelsArguments->element.container));
            operation._labelsArguments = operation._labelsArguments->next;
            labelParameters = labelParameters->next;
          };
          if (operation._labelsArguments || labelParameters) {
            context.addErrorMessage("The argument labels does not match for the"
              " logic function " + operation._identifier->getName() + ".");
          };
        };
        while (operation._labelsArguments) {
          free_logic_label((logic_label) operation._labelsArguments
              ->element.container);
          /* logic_label */ list temp = operation._labelsArguments;
          operation._labelsArguments = operation._labelsArguments->next;
          free(temp);
        };
      }
      else if (f->arg_labels) {
        // Done by frama-c.
        // context.addErrorMessage("The call to the logic function "
        //   + operation._identifier->getName()
        //   + " does not provide any label argument.");
      };

      if (f->returned_type->is_some) { // term recognition
        expressionResult =
          term_cons(
            term_node_TApp(
              qualified_name_dup(f->li_name),
              labelsTable, arguments,
              f->li_extern_c),
            operation._startLocation, NULL);
        operation._startLocation = NULL;
        ltypeResult = logic_type_dup((logic_type)
            f->returned_type->content.container);
        if (isPlainBooleanType(ltypeResult, context)) {
          location zeroLoc = copy_loc(expressionResult->loc);
          zeroLoc->linenum1 = zeroLoc->linenum2;
          zeroLoc->charnum1 = zeroLoc->charnum2;
          term zero = tzero(zeroLoc);
          predicate relation;
          if (ltypeResult->tag_logic_type == LINTEGER)
            relation = predicate_Prel(RNEQ, term_dup(expressionResult), zero);
          else
            relation = predicate_Prel(RNEQ, term_cons(term_node_TLogic_coerce(
              logic_type_Linteger(), term_dup(expressionResult)),
              copy_loc(expressionResult->loc), NULL), zero);
          predicateResult = predicate_named_cons(NULL,
              copy_loc(expressionResult->loc), relation);
        };
      }
      else {
        predicateResult =
          predicate_named_cons(
            NULL, operation._startLocation,
            predicate_PApp(
              qualified_name_dup(f->li_name),
              labelsTable, arguments,
              f->li_extern_c));
        operation._startLocation = NULL;
      };
      return true;
    }
    else if (operation._identifier
        && operation._identifier->isLogicConstructor()) {
      if (!(possibleTypes & (1U << LTRTerm))) {
        std::string errorMessage("symbol ");
        errorMessage.append(operation._identifier->getName());
        errorMessage.append(" is a logic constructor, not a predicate");
        context.addErrorMessage(errorMessage);
        return false;
      };
      logic_ctor_info info = operation._identifier->asLogicConstructor()
          .getInfo();
      // /* logic_type */ list params = info->ctor_params;
      // /* logic_type */ list copyParams = NULL, endCopyParams = NULL;
      // if (params != NULL) {
      //   copyParams = endCopyParams = cons_container(logic_type_dup(
      //         (logic_type) params->element.container), NULL);
      //   params = params->next;
      //   while (params) {
      //     endCopyParams->next = cons_container(logic_type_dup(
      //         (logic_type) params->element.container), NULL);
      //     endCopyParams = endCopyParams->next;
      //     params = params->next;
      //   };
      // };
      /* term */ list arguments = NULL, endArguments = NULL;
      /* logic_type */ list templateArguments = NULL,
                            endTemplateArguments = NULL;
      if (!operation._arguments.empty()) {
        std::list<std::pair<logic_type, term> >::iterator
            endIter = operation._arguments.end();
        std::list<std::pair<logic_type, term> >::iterator
            iter = operation._arguments.begin();
        // TODO: perform an implicit conversions on iter->second
        //     by comparing iter->first with elements of copyParams
        arguments = endArguments = cons_container(iter->second, NULL);
        iter->second = NULL;
        templateArguments = endTemplateArguments
            = cons_container(iter->first, NULL);
        iter->first = NULL;
        while (++iter != endIter) {
          endArguments->next = cons_container(iter->second, NULL);
          endArguments = endArguments->next;
          iter->second = NULL;
          endTemplateArguments->next = cons_container(iter->first, NULL);
          endTemplateArguments = endTemplateArguments->next;
          iter->first = NULL;
        };
        operation._arguments.clear();
      };
      expressionResult = term_cons(term_node_TDataCons(
            qualified_name_dup(info->ctor_name), /* copyParams, */ arguments),
          operation._startLocation, NULL);
      operation._startLocation = NULL;
      ltypeResult =
        logic_type_Lnamed(
          qualified_name_dup(info->constype),
          info->is_extern_c,
          templateArguments);
      return true;
    }
    context.addErrorMessage("unknown function call");
    return false;
  };
  if (argumentsNumber == 1) {
    logic_type ltypeArgument = NULL;
    term targument = NULL;
    predicate_named pargument = NULL;
    operation.extractLastArgument(ltypeArgument, targument, pargument
        /* , isRValue, intResult, doubleResult*/);

    // if (!isRValue) {
    //   // term_lval_cons ...
    //   // argument = term_node_TLval(lval)
    //   isRValue = true;
    // };
#if defined(__clang__) || defined(__GNUC__)
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wswitch"
#endif
    switch (type) {
      case Operator::TUnaryPlus:
        if (!targument) {
          if (pargument) {
            free_predicate_named(pargument);
            context.addErrorMessage("predicates do not support "
                "unary + operations");
          };
          return false;
        };
        assert(operation._startLocation);
        if (pargument) free_predicate_named(pargument);
        extend_location_with(operation._startLocation, targument->loc);
        free_location(targument->loc);
        targument->loc = operation._startLocation;
        operation._startLocation = NULL;
        expressionResult = targument;
        ltypeResult = ltypeArgument;
        return true;
      case Operator::TUnaryMinus:
        assert(operation._startLocation);
        if (!targument) {
          if (pargument) {
            free_predicate_named(pargument);
            context.addErrorMessage("predicates do not support "
                "unary - operation");
          };
          return false;
        };
        if (pargument) free_predicate_named(pargument);
        { ltypeArgument = logicArithmeticPromotion(ltypeArgument, context);
          extend_location_with(operation._startLocation, targument->loc);
          expressionResult = term_cons(term_node_TUnOp(uokind_UOOpposite(),
                targument), operation._startLocation, NULL /* names */);
          operation._startLocation = NULL;
          ltypeResult = ltypeArgument;
          // names = NULL;
        };
        // if (operation.isConstant()) {
        //   // *intResult = -*intResult;
        //   // *doubleResult = -*doubleResult;
        // };
        return true;
      case Operator::TNot:
        assert(operation._startLocation);
        if (targument) {
          extend_location_with(operation._startLocation, targument->loc);
          targument = typeBoolTerm(ltypeArgument, targument, context);
          expressionResult = term_cons(term_node_TUnOp(uokind_UOLogicalNegate(),
              targument), operation._startLocation, NULL /* names */);
          operation._startLocation = NULL;
          ltypeResult = ltypeArgument;
          // names = NULL;
        };
        if (pargument) {
          if (!operation._startLocation)
            operation._startLocation = copy_loc(expressionResult->loc);
          extend_location_with(operation._startLocation, pargument->pred_loc);
          if ((pargument->pred_content->tag_predicate == PREL)
              && pargument->pred_content->cons_predicate.Prel.cmpop == RNEQ
              && isLogicZero(pargument->pred_content->cons_predicate
                .Prel.sndarg)) {
            pargument->pred_content->cons_predicate.Prel.cmpop = REQ;
            free_location(pargument->pred_loc);
            pargument->pred_loc = operation._startLocation;
          }
          else
            pargument = predicate_named_cons(NULL /* names */,
                operation._startLocation, predicate_Pnot(pargument));
          operation._startLocation = NULL;
          predicateResult = pargument;
          // names = NULL;
        };
        // if (operation.isConstant()) {
        //   // *intResult = !*intResult;
        // };
        return true;
      case Operator::TComplement:
        if (!targument) {
          if (pargument) {
            free_predicate_named(pargument);
            context.addErrorMessage("predicates do not support "
                "unary ~ operation");
          };
          return false;
        };
        assert(operation._startLocation);
        extend_location_with(operation._startLocation, targument->loc);
        if (pargument) free_predicate_named(pargument);
        { ltypeResult = logicArithmeticPromotion(ltypeArgument, context);
          expressionResult = term_cons(term_node_TUnOp(uokind_UOBitNegate(),
                targument), operation._startLocation, NULL /* names */);
          operation._startLocation = NULL;
          // names = NULL;
        };
        // if (operation.isConstant()) {
        //   // *intResult = ~*intResult;
        // };
        return true;
      case Operator::TDereference:
        if (!targument) {
          if (pargument) {
            free_predicate_named(pargument);
            context.addErrorMessage("predicates do not support "
                "unary * operation");
          };
          return false;
        };
        assert(operation._startLocation);
        extend_location_with(operation._startLocation, targument->loc);
        if (pargument) free_predicate_named(pargument);
        { bool isValid = false;
          if (isArrayType(ltypeArgument, Substitution(), context)) {
            targument = makeLogicStartOf(targument, context);
            isValid = true;
          }
          else if (isPointerType(ltypeArgument, Substitution(), context))
            isValid = true;
          if (isValid) {
            ltypeResult = NULL;
            expressionResult = makeMemoryShift(ltypeArgument, targument,
                term_offset_TNoOffset(), operation._startLocation,
                ltypeResult, context);
            free_location(operation._startLocation);
            operation._startLocation = NULL;
            return true;
          };
        };
        context.addErrorMessage("invalid type for `unary *'");
        return false;
      case Operator::TAddressOf:
        if (!targument) {
          if (pargument) {
            free_predicate_named(pargument);
            context.addErrorMessage("predicates do not support "
                "'unary &' operation");
          };
          return false;
        };
        assert(operation._startLocation);
        extend_location_with(operation._startLocation, targument->loc);
        if (pargument) free_predicate_named(pargument);
        ltypeResult = NULL;
        expressionResult = termLValAddressOf(ltypeArgument, targument,
            operation._startLocation, ltypeResult, context);
        operation._startLocation = NULL;
        return true;
      case Operator::TNaming:
        // add naming to the local alias table;
        assert(operation._startLocation);
        free_location(operation._startLocation);
        operation._startLocation = NULL;
        { list *endTermNames = NULL, *endPredicateNames = NULL;
          if (targument) {
            endTermNames = &targument->names;
            while (*endTermNames)
              endTermNames= &(*endTermNames)->next;
            *endTermNames = cons_container(strdup(operation._fieldName.c_str()),
                NULL);
            ltypeResult = ltypeArgument;
            expressionResult = targument;
          };
          if (pargument) {
            endPredicateNames = &pargument->pred_name;
            while (*endPredicateNames)
              endPredicateNames= &(*endPredicateNames)->next;
            *endPredicateNames = cons_container(strdup(
                  operation._fieldName.c_str()), NULL);
            predicateResult = pargument;
          };
        };
        return true;
      case Operator::TStructAccess:
        if (!targument) {
          if (pargument) {
            free_predicate_named(pargument);
            context.addErrorMessage("predicates do not support "
                "struct access operation");
          };
          return false;
        };
        assert(operation._startLocation);
        if (pargument) free_predicate_named(pargument);
        { term_offset offset = NULL;
          logic_type ltype = NULL;
          if (!retrieveTypeOfField(ltypeArgument, operation._fieldName, offset,
              ltype, context))
            return false;
          free_logic_type(ltypeArgument);
          expressionResult = makeDot(targument, operation._startLocation,
              offset, context);
          operation._startLocation = NULL;
          ltypeResult = ltype;
        };
        return true;
      case Operator::TArrowStructAccess:
        if (!targument) {
          if (pargument) {
            free_predicate_named(pargument);
            context.addErrorMessage("predicates do not support "
                "indirect struct access operation");
          };
          return false;
        };
        assert(operation._startLocation);
        if (pargument) free_predicate_named(pargument);
        if (isCPointerType(ltypeArgument, context)
            || isCArrayType(ltypeArgument, context)) {
          if (isCArrayType(ltypeArgument, context))
            targument = makeLogicStartOf(targument, context);

          logic_type structType = typeOfPointed(ltypeArgument, Substitution(),
              context);
          term_offset offset = NULL;
          ltypeResult = NULL;
          if (!retrieveTypeOfField(structType, operation._fieldName, offset,
              ltypeResult, context))
            return false;
          free_logic_type(ltypeArgument);
          expressionResult = makeMemoryShift(structType, targument, offset,
              operation._startLocation, ltypeResult, context);
          free_logic_type(structType);
          operation._startLocation = NULL;
          return true;
        };
        context.addErrorMessage("invalid type for `operator ->'");
        return false;
      case Operator::TIndirectMethodAccess:
        // shift + indirection
        assert(false); // unimplemented
        return false;
      case Operator::TArrowIndirectMethodAccess:
        // shift + indirection
        assert(false); // unimplemented
        return false;
      case Operator::TArrayAccess:
        if (!targument) {
          if (pargument) {
            free_predicate_named(pargument);
            context.addErrorMessage("predicates do not support "
                "unary * operation");
          };
          return false;
        };
        if (pargument) free_predicate_named(pargument);
        if (operation._arguments.size() != 1) {
          context.addErrorMessage("bad number of arguments for array access");
          return false;
        };
        if (isPointerType(ltypeArgument, Substitution(), context)
            && isIntegralType(operation._arguments.back().first, Substitution(),
                              context)) {
          logic_type lindexType = operation._arguments.back().first;
          ltypeResult = typeOfPointed(ltypeArgument, Substitution(), context);
          if (isSetType(lindexType) && !isSetType(ltypeArgument))
            ltypeArgument = make_set_type(ltypeArgument);
        }
        else if (
          isPointerType(operation._arguments.back().first,
                        Substitution(), context)
          && isIntegralType(ltypeArgument, Substitution(), context))
          {
          logic_type ltemp = ltypeArgument;
          ltypeArgument = operation._arguments.back().first;
          operation._arguments.back().first = ltemp;
          term temp = targument;
          targument = operation._arguments.back().second;
          operation._arguments.back().second = temp;
          if (isArrayType(ltypeArgument, Substitution(), context)
              && isCArray(targument,ltypeArgument,context)) {
	    targument = makeLogicStartOf(targument, context);
            ltypeResult =
              typeOfArrayElement(ltypeArgument, Substitution(),context); 
          } else {
            ltypeResult = typeOfPointed(ltypeArgument, Substitution(), context);
          }
          logic_type lindexType = operation._arguments.back().first;
          if (isSetType(lindexType) && !isSetType(ltypeArgument))
            ltypeArgument = make_set_type(ltypeArgument);
        }
        else if (
          isArrayType(ltypeArgument, Substitution(), context)
          && isIntegralType(operation._arguments.back().first, Substitution(),
                            context))
          ltypeResult = typeOfArrayElement(ltypeArgument, Substitution(),
                                           context);
        else if (isArrayType(operation._arguments.back().first, Substitution(),
              context)
            && isIntegralType(ltypeArgument, Substitution(), context)) {
          logic_type ltemp = ltypeArgument;
          ltypeArgument = operation._arguments.back().first;
          operation._arguments.back().first = ltemp;
          term temp = targument;
          targument = operation._arguments.back().second;
          operation._arguments.back().second = temp;
          ltypeResult = typeOfArrayElement(ltypeArgument, Substitution(),
              context);
        }
        else {
          if (isArrayType(operation._arguments.back().first, Substitution(),
                context)
              || isArrayType(ltypeArgument, Substitution(), context))
            context.addErrorMessage("subscript is not an integer range");
          else
            context.addErrorMessage("subscripted value is neither array "
                "nor pointer");
          free_logic_type(operation._arguments.back().first);
          free_term(operation._arguments.back().second);
          operation._arguments.clear();
          return true;
        };
        free_logic_type(operation._arguments.back().first);
        { location loc = copy_loc(targument->loc);
          extend_location_with(loc, operation._arguments.back().second->loc);
          expressionResult = makeShift(targument, ltypeArgument,
              operation._arguments.back().second, loc, context);
        };
        free_logic_type(ltypeArgument);
        operation._arguments.clear();
        return true;
      case Operator::TForall:
        if (!pargument) {
          if (targument) {
            free_term(targument);
            context.addErrorMessage("terms do not support "
                "forall quantification");
          };
          if (ltypeArgument)
            free_logic_type(ltypeArgument);
          return false;
        };
        assert(operation._startLocation);
        extend_location_with(operation._startLocation, pargument->pred_loc);
        if (targument)
          free_term(targument);
        if (ltypeArgument)
          free_logic_type(ltypeArgument);
        predicateResult = predicate_named_cons(NULL, operation._startLocation,
            predicate_Pforall(operation._binders, pargument));
        operation._startLocation = NULL;
        { /* logic_var_def */ list binderIter = operation._binders;
          while (binderIter != NULL) {
            logic_var_def def = (logic_var_def) binderIter->element.container;
            context.removeLocalBinding(def->lv_name->decl_name);
            binderIter = binderIter->next;
          };
        };
        operation._binders = NULL;
        return true;
      case Operator::TExists:
        if (!pargument) {
          if (targument) {
            free_term(targument);
            context.addErrorMessage("terms do not support "
                "exists quantification");
          };
          if (ltypeArgument)
            free_logic_type(ltypeArgument);
          return false;
        };
        assert(operation._startLocation);
        extend_location_with(operation._startLocation, pargument->pred_loc);
        if (targument)
          free_term(targument);
        if (ltypeArgument)
          free_logic_type(ltypeArgument);
        predicateResult = predicate_named_cons(NULL, operation._startLocation,
            predicate_Pexists(operation._binders, pargument));
        operation._startLocation = NULL;
        { /* logic_var_def */ list binderIter = operation._binders;
          while (binderIter != NULL) {
            logic_var_def def = (logic_var_def) binderIter->element.container;
            context.removeLocalBinding(def->lv_name->decl_name);
            binderIter = binderIter->next;
          };
        };
        operation._binders = NULL;
        return true;
    };
#if defined(__clang__) || defined(__GNUC__)
#pragma GCC diagnostic pop
#endif
  }
  else if (argumentsNumber == 2) {
    Operator::Type type = operation.getType();
    // bool isFirstRValue = false, isSecondRValue = false;
    // int firstIntResult = 0, secondIntResult = 0;
    // double firstDoubleResult = 0, secondDoubleResult = 0;
    logic_type ltypeSecondArgument = NULL;
    term tsecondArgument = NULL;
    predicate_named psecondArgument = NULL;
    operation.extractSecondArgument(
      ltypeSecondArgument, tsecondArgument,
      psecondArgument /*,isSecondRValue,&secondIntResult,&secondDoubleResult*/);
    logic_type ltypeFirstArgument = NULL;
    term tfirstArgument = NULL;
    predicate_named pfirstArgument = NULL;
    operation.extractFirstArgument(ltypeFirstArgument, tfirstArgument,
        pfirstArgument /*, isFirstRValue, &firstIntResult,
        &firstDoubleResult*/);
    //assert(!operation._startLocation);
    
    if (type >= Operator::TEqual && type <= Operator::TGreater) {
      //if (predicateResult || expressionResult || ltypeResult)
      //  return false;targument = 
      // will be used to deal with sequences of relations of the form
      // a <= b <= c;
      predicateResult = NULL;
      expressionResult = NULL;
      ltypeResult = NULL;
      std::list<Operator::Relation>::const_iterator
        iter = operation._endRelationList.end();
      term tnewFirstArgument = NULL;
      logic_type ltypeNewFirstArgument = NULL;
      bool firstIsPredicate = pfirstArgument && !tfirstArgument;
      bool secondIsPredicate = psecondArgument && !tsecondArgument;
      if (pfirstArgument)
        { free_predicate_named(pfirstArgument); pfirstArgument = NULL; }
      if (psecondArgument)
        { free_predicate_named(psecondArgument); psecondArgument = NULL; }
      do {
        bool doesCopyArg;
        if (iter != operation._endRelationList.end()) {
          type = iter->_type;
          std::list<Operator::Relation>::const_iterator copyIter(iter);
          ++copyIter;
          doesCopyArg = (copyIter != operation._endRelationList.end());
          ltypeFirstArgument = ltypeNewFirstArgument;
          ltypeNewFirstArgument = NULL;
          tfirstArgument = tnewFirstArgument;
          tnewFirstArgument = NULL;
          ltypeSecondArgument = iter->_ltype;
          tsecondArgument = iter->_node;
        }
        else
          doesCopyArg = (!operation._endRelationList.empty());
        if (doesCopyArg) {
          tnewFirstArgument = term_dup(tsecondArgument);
          ltypeNewFirstArgument = logic_type_dup(ltypeFirstArgument);
        };

        relation operationRelation;
        bokind expressionRelation;
        switch (type) {
          case Operator::TEqual:
            operationRelation = REQ; expressionRelation = BOEQUAL;
            break;
          case Operator::TDifferent:
            operationRelation = RNEQ; expressionRelation = BODIFFERENT;
            break;
          case Operator::TLessOrEqual:
            operationRelation = RLE; expressionRelation = BOLESSOREQUAL;
            break;
          case Operator::TGreaterOrEqual:
            operationRelation = RGE; expressionRelation = BOGREATEROREQUAL;
            break;
          case Operator::TLess:
            operationRelation = RLT; expressionRelation = BOLESS;
            break;
          case Operator::TGreater:
            operationRelation = RGT; expressionRelation = BOGREATER;
            break;
          default:
            operationRelation = REQ;
            expressionRelation = BOEQUAL;
        };
        predicate_named oldPredicateResult = predicateResult;
        term oldExpressionResult = expressionResult;
        predicateResult = NULL;
        expressionResult = NULL;

        if (!(ltypeSecondArgument && tsecondArgument
            && ltypeFirstArgument && tfirstArgument)) {
          std::string op = operation.queryOperatorName();
          if (firstIsPredicate) context.addErrorMessage("the first argument of operator " + op + " should be a term, not a predicate");
          if (secondIsPredicate) context.addErrorMessage("the second argument of operator " + op + " should be a term, not a predicate");
          return false;
        }
        bool hasResult = false;
        if (isArithmeticType(ltypeFirstArgument, context)
            && isArithmeticType(ltypeSecondArgument, context)) {
          // [TODO] partial unification
          logic_type ltypeConversion = conditionalConversion(ltypeFirstArgument,
              ltypeSecondArgument, context);
          if (!ltypeConversion)
            return false;
          tfirstArgument = implicitConversion(ltypeConversion, tfirstArgument,
              ltypeFirstArgument, false, Substitution(), Substitution(),
              context);
          if (!tfirstArgument)
             return false;
          tsecondArgument =
            implicitConversion(
              ltypeConversion, tsecondArgument, ltypeSecondArgument,
              false, Substitution(), Substitution(), context);
          free_logic_type(ltypeConversion);
          if (!tsecondArgument)
             return false;
          if ((possibleTypes & (1U << LTRTerm))) {
            location loc = copy_loc(tfirstArgument->loc);
            extend_location_with(loc, tsecondArgument->loc);
            expressionResult = term_cons(term_node_TBinOp(expressionRelation,
              tfirstArgument, tsecondArgument), loc, NULL);
          };
          if (possibleTypes & (1U << LTRPredicate)) {
            location loc = copy_loc(tfirstArgument->loc);
            extend_location_with(loc, tsecondArgument->loc);
            predicateResult = predicate_named_cons(NULL, loc,
              predicate_Prel(operationRelation,
              (possibleTypes & (1U << LTRTerm))
                  ? term_dup(tfirstArgument) : tfirstArgument,
              (possibleTypes & (1U << LTRTerm))
                  ? term_dup(tsecondArgument) : tsecondArgument));
          };
          hasResult = true;
        }
        else if (type == Operator::TEqual || type == Operator::TDifferent) {
          if ((isPointerType(ltypeFirstArgument, Substitution(), context) ||
               isArrayType(ltypeFirstArgument, Substitution(), context))
              && isLogicNull(tsecondArgument)) {
            if (isArrayType(ltypeFirstArgument, Substitution(), context)
                && isCArray(tfirstArgument,ltypeFirstArgument,context)) {
              tfirstArgument = makeLogicStartOf(tfirstArgument, context);
              ltypeFirstArgument =
                logic_type_Lpointer(
                  typeOfArrayElement(
                    ltypeFirstArgument, Substitution(), context));
            }
            tsecondArgument = makeCast(ltypeFirstArgument, tsecondArgument,
                ltypeSecondArgument, Substitution(), Substitution(), context);
            if ((possibleTypes & (1U << LTRTerm))) {
              location loc = copy_loc(tfirstArgument->loc);
              extend_location_with(loc, tsecondArgument->loc);
              expressionResult = term_cons(term_node_TBinOp(expressionRelation,
                tfirstArgument, tsecondArgument), loc, NULL);
            };
            if (possibleTypes & (1U << LTRPredicate)) {
              location loc = copy_loc(tfirstArgument->loc);
              extend_location_with(loc, tsecondArgument->loc);
              predicateResult = predicate_named_cons(NULL, loc,
                predicate_Prel(operationRelation,
                (possibleTypes & (1U << LTRTerm))
                    ? term_dup(tfirstArgument) : tfirstArgument,
                (possibleTypes & (1U << LTRTerm))
                    ? term_dup(tsecondArgument) : tsecondArgument));
            };
            free_logic_type(ltypeFirstArgument);
            hasResult = true;
          }
          else if (
            (isPointerType(ltypeSecondArgument, Substitution(), context) ||
             isArrayType(ltypeSecondArgument, Substitution(), context))
            && isLogicNull(tfirstArgument)) {
            if (
                isArrayType(ltypeSecondArgument, Substitution(), context)
                && isCArray(tsecondArgument,ltypeSecondArgument,context)) {
              tsecondArgument = makeLogicStartOf(tsecondArgument, context);
              ltypeSecondArgument =
                logic_type_Lpointer(
                  typeOfArrayElement(
                    ltypeSecondArgument, Substitution(), context));
            }
            tfirstArgument = makeCast(ltypeSecondArgument, tfirstArgument,
              ltypeFirstArgument, Substitution(), Substitution(), context);
            if ((possibleTypes & (1U << LTRTerm))) {
              location loc = copy_loc(tfirstArgument->loc);
              extend_location_with(loc, tsecondArgument->loc);
              expressionResult = term_cons(term_node_TBinOp(expressionRelation,
                tfirstArgument, tsecondArgument), loc, NULL);
            }
            if (possibleTypes & (1U << LTRPredicate)) {
              location loc = copy_loc(tfirstArgument->loc);
              extend_location_with(loc, tsecondArgument->loc);
              predicateResult = predicate_named_cons(NULL, loc,
                predicate_Prel(operationRelation,
                (possibleTypes & (1U << LTRTerm))
                    ? term_dup(tfirstArgument) : tfirstArgument,
                (possibleTypes & (1U << LTRTerm))
                    ? term_dup(tsecondArgument) : tsecondArgument));
            };
            free_logic_type(ltypeSecondArgument);
            hasResult = true;
          }
          else if (isArrayType(ltypeFirstArgument, Substitution(), context)
              && isArrayType(ltypeSecondArgument, Substitution(), context)) {
            logic_type subtypeFirst = typeOfArrayElement(ltypeFirstArgument,
                Substitution(), context);
            logic_type subtypeSecond = typeOfArrayElement(ltypeSecondArgument,
                Substitution(), context);
            GuardLogicType guardFirst(subtypeFirst), guardSecond(subtypeSecond);
            if (!isSameType(subtypeFirst, subtypeSecond, Substitution(),
                  Substitution(), context)) {
              context.addErrorMessage("comparison of incompatible array types");
              goto LContinueRelation;
            };
            if ((possibleTypes & (1U << LTRTerm))) {
              location loc = copy_loc(tfirstArgument->loc);
              extend_location_with(loc, tsecondArgument->loc);
              expressionResult = term_cons(term_node_TBinOp(expressionRelation,
                tfirstArgument, tsecondArgument), loc, NULL);
            };
            if (possibleTypes & (1U << LTRPredicate)) {
              location loc = copy_loc(tfirstArgument->loc);
              extend_location_with(loc, tsecondArgument->loc);
              predicateResult = predicate_named_cons(NULL, loc,
                predicate_Prel(operationRelation,
                (possibleTypes & (1U << LTRTerm))
                    ? term_dup(tfirstArgument) : tfirstArgument,
                (possibleTypes & (1U << LTRTerm))
                    ? term_dup(tsecondArgument) : tsecondArgument));
            };
            free_logic_type(ltypeFirstArgument);
            free_logic_type(ltypeSecondArgument);
            hasResult = true;
          };
        };
        if (!hasResult && 
            (isPointerType(ltypeFirstArgument, Substitution(), context)
             || isArrayType(ltypeFirstArgument, Substitution(), context))
            && 
            (isPointerType(ltypeSecondArgument, Substitution(), context)
             || isArrayType(ltypeSecondArgument, Substitution(), context))) {
          if (isArrayType(ltypeFirstArgument,Substitution(), context) && 
              isCArray(tfirstArgument,ltypeFirstArgument,context) &&
              !isArrayType(ltypeSecondArgument,Substitution(), context)) {
	    tfirstArgument = makeLogicStartOf(tfirstArgument, context);
            ltypeFirstArgument =
              logic_type_Lpointer(
                typeOfArrayElement(ltypeFirstArgument,Substitution(), context));
          }
          if (!isArrayType(ltypeFirstArgument, Substitution(), context)
              && isArrayType(ltypeSecondArgument,Substitution(), context)
              && isCArray(tsecondArgument,ltypeSecondArgument,context)) {
	    tsecondArgument = makeLogicStartOf(tsecondArgument, context);
            ltypeSecondArgument =
              logic_type_Lpointer(
                typeOfArrayElement(
                  ltypeSecondArgument, Substitution(), context));
          }
          logic_type subtypeFirst = NULL;
          if (isArrayType(ltypeFirstArgument,Substitution(),context))
            subtypeFirst =  
              typeOfArrayElement(ltypeFirstArgument,Substitution(), context);
          else
           subtypeFirst =
             typeOfPointed(ltypeFirstArgument, Substitution(), context);
          logic_type subtypeSecond = NULL;
          if (isArrayType(ltypeSecondArgument,Substitution(), context))
            subtypeSecond =
              typeOfArrayElement(ltypeSecondArgument, Substitution(), context);
          else
            subtypeSecond =
              typeOfPointed(ltypeSecondArgument, Substitution(), context);
          GuardLogicType guardFirst(subtypeFirst), guardSecond(subtypeSecond);
          if (isSameType(subtypeFirst, subtypeSecond, Substitution(),
                Substitution(), context)
              || ((type == Operator::TEqual || type == Operator::TDifferent)
                && isLogicVoidPointerType(ltypeFirstArgument, context)
                && isLogicVoidPointerType(ltypeSecondArgument, context))) {
            if (possibleTypes & (1U << LTRTerm)) {
              location loc = copy_loc(tfirstArgument->loc);
              extend_location_with(loc, tsecondArgument->loc);
              expressionResult = term_cons(term_node_TBinOp(expressionRelation,
                tfirstArgument, tsecondArgument), loc, NULL);
            };
            if (possibleTypes & (1U << LTRPredicate)) {
              location loc = copy_loc(tfirstArgument->loc);
              extend_location_with(loc, tsecondArgument->loc);
              predicateResult = predicate_named_cons(NULL, loc,
                predicate_Prel(operationRelation,
                (possibleTypes & (1U << LTRTerm))
                    ? term_dup(tfirstArgument) : tfirstArgument,
                (possibleTypes & (1U << LTRTerm))
                    ? term_dup(tsecondArgument) : tsecondArgument));
            };
            free_logic_type(ltypeFirstArgument);
            free_logic_type(ltypeSecondArgument);
            hasResult = true;
          };
        };
        if (!hasResult && (type == Operator::TEqual
              || type == Operator::TDifferent)) {
          // [TODO] partial unification
          logic_type ltypeConversion = conditionalConversion(ltypeFirstArgument,
              ltypeSecondArgument, context);
          if (!ltypeConversion) {
            std::string error("unknown type comparison for the operator ");
            if (type == Operator::TEqual)
              error += "==";
            else 
              error += "!=";
            context.addErrorMessage(error);
            return false;
          }
          tfirstArgument =
            implicitConversion(
              ltypeConversion, tfirstArgument, ltypeFirstArgument,
              false, Substitution(), Substitution(), context);
          if (!tfirstArgument)
             return false;
          tsecondArgument =
            implicitConversion(
              ltypeConversion, tsecondArgument, ltypeSecondArgument,
              false, Substitution(), Substitution(), context);
          free_logic_type(ltypeConversion);
          if (!tsecondArgument)
             return false;
          if (possibleTypes & (1U << LTRTerm)) {
            location loc = copy_loc(tfirstArgument->loc);
            extend_location_with(loc, tsecondArgument->loc);
            expressionResult = term_cons(term_node_TBinOp(expressionRelation,
              tfirstArgument, tsecondArgument), loc, NULL);
          };
          if (possibleTypes & (1U << LTRPredicate)) {
            location loc = copy_loc(tfirstArgument->loc);
            extend_location_with(loc, tsecondArgument->loc);
            predicateResult = predicate_named_cons(NULL, loc,
              predicate_Prel(operationRelation,
              (possibleTypes & (1U << LTRTerm))
                  ? term_dup(tfirstArgument) : tfirstArgument,
              (possibleTypes & (1U << LTRTerm))
                  ? term_dup(tsecondArgument) : tsecondArgument));
          };
        }
        else if (!hasResult) {
          context.addErrorMessage("comparison of incompatible types");
          goto LContinueRelation;
        };

        if (oldExpressionResult) {
          location loc = copy_loc(oldExpressionResult->loc);
          extend_location_with(loc, expressionResult->loc);
          expressionResult = term_cons(term_node_TBinOp(BOLOGICALAND,
            oldExpressionResult, expressionResult), loc, NULL);
          oldExpressionResult = NULL;
        }
        if (oldPredicateResult) {
          location loc = copy_loc(oldPredicateResult->pred_loc);
          extend_location_with(loc, predicateResult->pred_loc);
          predicateResult = predicate_named_cons(NULL, loc, 
            predicate_Pand(oldPredicateResult, predicateResult));
          oldPredicateResult = NULL;
        }
LContinueRelation:
        tfirstArgument = tsecondArgument = NULL;
        ltypeFirstArgument = ltypeSecondArgument = NULL;
        if (iter != operation._endRelationList.end())
          ++iter;
        else if (doesCopyArg)
          iter = operation._endRelationList.begin();
      } while (iter != operation._endRelationList.end());
      operation._endRelationList.clear();
      if (expressionResult) {
        ltypeResult = context.boolean_type();
      };
      return true;
    };

    // if (!isFirstRValue) {
    //   // term_lval_cons ...
    //   // firstArgument = term_node_TLval(lval)
    //   isFirstRValue = true;
    // };
    // if (!isSecondRValue) {
    //   // term_lval_cons ...
    //   // secondArgument = term_node_TLval(lval)
    //   isSecondRValue = true;
    // };

    int binaryKind = -1;
    bool shouldBeIntegral = false;
    bool shouldBeBoolean = false;
    logic_type ltypeFirstElementArgument = NULL,
               ltypeSecondElementArgument = NULL;
#if defined(__clang__) || defined(__GNUC__)
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wswitch"
#endif
    switch (type) {
      case Operator::TPlus:
      case Operator::TMinus:
        binaryKind = (type == Operator::TPlus) ? BOPLUS : BOMINUS;
        // if (operation.isConstant()) {
        //   // if (intResult)
        //   //   *intResult = firstIntResult + secondIntResult;
        //   // if (doubleResult)
        //   //   *doubleResult = firstDoubleResult + secondDoubleResult;
        // };
        if (!tfirstArgument || !tsecondArgument) {
          if (pfirstArgument || psecondArgument) {
            context.addErrorMessage("predicates do not support "
                "binary '+' operation");
            if (pfirstArgument) free_predicate_named(pfirstArgument);
            if (psecondArgument) free_predicate_named(psecondArgument);
          };
          return false;
        };
        if (pfirstArgument) free_predicate_named(pfirstArgument);
        if (psecondArgument) free_predicate_named(psecondArgument);
        pfirstArgument = psecondArgument = NULL;
        ltypeFirstElementArgument = isSetType(ltypeFirstArgument);
        if (!ltypeFirstElementArgument)
          ltypeFirstElementArgument = ltypeFirstArgument;
        ltypeSecondElementArgument = isSetType(ltypeSecondArgument);
        if (!ltypeSecondElementArgument)
          ltypeSecondElementArgument = ltypeSecondArgument;
        if (isArithmeticType(ltypeFirstElementArgument, context)) {
          if (isArithmeticType(ltypeSecondElementArgument, context))
            break;
          if ((type == Operator::TPlus)
              && (isPointerType(ltypeSecondElementArgument, Substitution(),
                                context)
                  || (isArrayType(ltypeSecondElementArgument, Substitution(),
                                  context)
		      && isCArray(tsecondArgument,ltypeSecondArgument,context))
               // No pointer arithmetic over logical arrays
               )) {
            if (isCArray(tsecondArgument,ltypeSecondArgument,context))
              tsecondArgument = makeLogicStartOf(tsecondArgument, context);
            if (tsecondArgument->node->tag_term_node == TSTARTOF) {
              term_lval lval = tsecondArgument->node->cons_term_node
                  .TStartOf.subexpr;
              addOffset(lval->offset,
                  term_offset_TIndex(tfirstArgument, term_offset_TNoOffset()));
              location loc = copy_loc(tfirstArgument->loc);
              extend_location_with(loc, tsecondArgument->loc);
              expressionResult = term_cons(term_node_TAddrOf(lval), loc, NULL);
              tsecondArgument->node->cons_term_node.TStartOf.subexpr = NULL;
              free_term(tsecondArgument);
              logic_type elem_type =
                typeOfArrayElement(ltypeSecondArgument,Substitution(), context);
              ltypeResult = logic_type_Lpointer(elem_type);
              if (ltypeFirstElementArgument != ltypeFirstArgument)
                ltypeResult= make_set_type(ltypeResult);
              free_logic_type(ltypeFirstArgument);
              free_logic_type(ltypeSecondArgument);
              return true;
            };
            ltypeResult = ltypeSecondArgument;
            if (!isSetType(ltypeResult)
                && ((ltypeSecondElementArgument != ltypeSecondArgument)
                  || (ltypeFirstElementArgument != ltypeFirstArgument)))
              ltypeResult = make_set_type(ltypeResult);
            logic_type integralPromotionType = integralPromotion(
                ltypeFirstArgument, context);
            if (!integralPromotionType)
               return false;
            location loc = copy_loc(tfirstArgument->loc);
            extend_location_with(loc, tsecondArgument->loc);
            expressionResult = term_cons(term_node_TBinOp((bokind) binaryKind
                /* BOPLUSPI */, tsecondArgument, makeCast(integralPromotionType,
                  tfirstArgument, ltypeFirstArgument,
                  Substitution(), Substitution(), context)), loc, NULL);
            free_logic_type(integralPromotionType);
            return true;
          };
        };
        if (isArithmeticType(ltypeSecondElementArgument, context)) {
          if ((type == Operator::TPlus)
              && 
              (isPointerType(ltypeFirstElementArgument, Substitution(), context)
              ||
               (isArrayType(ltypeFirstElementArgument, Substitution(), context)
                && isCArray(tfirstArgument,ltypeFirstArgument,context))
               // No pointer arithmetic over logical arrays
               )) {
            if (isCArray(tfirstArgument,ltypeFirstArgument,context))
              tfirstArgument = makeLogicStartOf(tfirstArgument, context);
            if ((type == Operator::TPlus)
                && tfirstArgument->node->tag_term_node == TSTARTOF) {
              term_lval lval
                = tfirstArgument->node->cons_term_node.TStartOf.subexpr;
              location loc = copy_loc(tfirstArgument->loc);
              extend_location_with(loc, tsecondArgument->loc);
              addOffset(lval->offset,
                  term_offset_TIndex(tsecondArgument, term_offset_TNoOffset()));
              expressionResult = term_cons(term_node_TAddrOf(lval), loc, NULL);
              tfirstArgument->node->cons_term_node.TStartOf.subexpr = NULL;
              free_term(tfirstArgument);
              logic_type elem_type =
                typeOfArrayElement(ltypeFirstArgument,Substitution(),context);
              ltypeResult = logic_type_Lpointer(elem_type);
              if (ltypeSecondElementArgument != ltypeSecondArgument)
                ltypeResult= make_set_type(ltypeResult);
              free_logic_type(ltypeSecondArgument);
              free_logic_type(ltypeFirstArgument);
              return true;
            };
            ltypeResult = ltypeFirstArgument;
            if (!isSetType(ltypeResult)
                && ((ltypeFirstElementArgument != ltypeFirstArgument)
                    || (ltypeSecondElementArgument != ltypeSecondArgument)))
              ltypeResult = make_set_type(ltypeResult);
            logic_type integralPromotionType
              = integralPromotion(ltypeSecondArgument, context);
            if (!integralPromotionType)
               return false;
            location loc = copy_loc(tfirstArgument->loc);
            extend_location_with(loc, tsecondArgument->loc);
            expressionResult = term_cons(term_node_TBinOp((bokind) binaryKind
                /* BOPLUSPI */, tfirstArgument, makeCast(integralPromotionType,
                  tsecondArgument, ltypeSecondArgument,
                  Substitution(), Substitution(), context)), loc, NULL);
            free_logic_type(integralPromotionType);
            return true;
          };
        };
        if ((type == Operator::TMinus)
          && 
          (isPointerType(ltypeFirstElementArgument, Substitution(), context) ||
            (isArrayType(ltypeFirstElementArgument, Substitution(), context) &&
	     isCArray(tfirstArgument,ltypeFirstElementArgument,context)))
            && 
          (isPointerType(ltypeSecondElementArgument, Substitution(), context) ||
            (isArrayType(ltypeSecondElementArgument, Substitution(), context) &&
	     isCArray(tsecondArgument,ltypeSecondArgument,context)))) {
          if (isCArray(tfirstArgument,ltypeFirstArgument,context)) {
            tfirstArgument = makeLogicStartOf(tfirstArgument, context);
            ltypeFirstArgument =
              logic_type_Lpointer(
                typeOfArrayElement(ltypeFirstArgument,Substitution(), context));
          }
          if (isCArray(tsecondArgument,ltypeSecondArgument,context)) {
            tsecondArgument = makeLogicStartOf(tsecondArgument, context);
            ltypeSecondArgument =
              logic_type_Lpointer(
                typeOfArrayElement(ltypeSecondArgument,Substitution(),context));
          }
          ltypeResult = logic_type_Linteger();
          location loc = copy_loc(tfirstArgument->loc);
          extend_location_with(loc, tsecondArgument->loc);
          expressionResult = term_cons(term_node_TBinOp((bokind) binaryKind
              /* BOPLUSPI */, tfirstArgument, makeCast(ltypeFirstArgument,
                tsecondArgument, ltypeSecondArgument,
                Substitution(), Substitution(), context)), loc, NULL);
          if (!isSetType(ltypeResult)
              && ((ltypeFirstElementArgument != ltypeFirstArgument)
                  || (ltypeSecondElementArgument != ltypeSecondArgument)))
            ltypeResult = make_set_type(ltypeResult);
          free_logic_type(ltypeFirstArgument);
          free_logic_type(ltypeSecondArgument);
          return true;
        };
        context.addErrorMessage("invalid operands to binary addition");
        return false;
      case Operator::TTimes:
        binaryKind = BOTIMES;
        // if (operation.isConstant()) {
        //   // if (intResult)
        //   //   *intResult = firstIntResult * secondIntResult;
        //   // if (doubleResult)
        //   //   *doubleResult = firstDoubleResult * secondDoubleResult;
        // };
        break;
      case Operator::TDivide:
        binaryKind = BODIVIDE;
        // if (operation.isConstant()) {
        //   // if (intResult)
        //   //   *intResult = firstIntResult / secondIntResult;
        //   // if (doubleResult)
        //   //   *doubleResult = firstDoubleResult / secondDoubleResult;
        // };
        break;
      case Operator::TModulo:
        binaryKind = BOMODULO;
        shouldBeIntegral = true;
        // if (operation.isConstant()) {
        //   // if (intResult)
        //   //   *intResult = firstIntResult % secondIntResult;
        // };
        break;
      case Operator::TLeftShift:
        binaryKind = BOLEFTSHIFT;
        shouldBeIntegral = true;
        // if (operation.isConstant()) {
        //   // if (intResult)
        //   //   *intResult = firstIntResult << secondIntResult;
        // };
        break;
      case Operator::TRightShift:
        binaryKind = BORIGHTSHIFT;
        shouldBeIntegral = true;
        // if (operation.isConstant()) {
        //   // if (intResult)
        //   //   *intResult = firstIntResult >> secondIntResult;
        // };
        break;
      case Operator::TLogicalAnd:
        binaryKind = BOLOGICALAND;
        shouldBeBoolean = true;
        if (pfirstArgument && psecondArgument) {
          location loc = copy_loc(pfirstArgument->pred_loc);
          extend_location_with(loc, psecondArgument->pred_loc);
          predicateResult = predicate_named_cons(NULL, loc,
              predicate_Pand(pfirstArgument, psecondArgument));
          pfirstArgument = psecondArgument = NULL;
        }
        // if (operation.isConstant()) {
        //   // if (intResult)
        //   //   *intResult = firstIntResult && secondIntResult;
        // };
        break;
      case Operator::TLogicalOr:
        binaryKind = BOLOGICALOR;
        shouldBeBoolean = true;
        if (pfirstArgument && psecondArgument) {
          location loc = copy_loc(pfirstArgument->pred_loc);
          extend_location_with(loc, psecondArgument->pred_loc);
          predicateResult = predicate_named_cons(NULL, loc,
              predicate_Por(pfirstArgument, psecondArgument));
          pfirstArgument = psecondArgument = NULL;
        };
        // if (operation.isConstant()) {
        //   // if (intResult)
        //   //   *intResult = firstIntResult || secondIntResult;
        // };
        break;
      case Operator::TLogicalImply:
        if (!pfirstArgument && ltypeFirstArgument && tfirstArgument) {
            pfirstArgument =
              convertTermToPredicate(ltypeFirstArgument,tfirstArgument,context);
        }
        if (!psecondArgument && ltypeSecondArgument && tsecondArgument) {
          psecondArgument =
            convertTermToPredicate(ltypeSecondArgument,tsecondArgument,context);
        }
        if (tfirstArgument) free_term(tfirstArgument);
        if (ltypeFirstArgument) free_logic_type(ltypeFirstArgument);
        if (tsecondArgument) free_term(tsecondArgument);
        if (ltypeSecondArgument) free_logic_type(ltypeSecondArgument);
        if (!(pfirstArgument && psecondArgument))
          return false;
        shouldBeBoolean = true;
        { location loc = copy_loc(pfirstArgument->pred_loc);
          extend_location_with(loc, psecondArgument->pred_loc);
          predicateResult = predicate_named_cons(NULL, loc,
              predicate_Pimplies(pfirstArgument, psecondArgument));
        };
        return true;
      case Operator::TLogicalEquiv:
        if (tfirstArgument) free_term(tfirstArgument);
        if (ltypeFirstArgument) free_logic_type(ltypeFirstArgument);
        if (tsecondArgument) free_term(tsecondArgument);
        if (ltypeSecondArgument) free_logic_type(ltypeSecondArgument);
        if (!(pfirstArgument && psecondArgument))
          return false;
        shouldBeBoolean = true;
        { location loc = copy_loc(pfirstArgument->pred_loc);
          extend_location_with(loc, psecondArgument->pred_loc);
          predicateResult = predicate_named_cons(NULL, loc,
              predicate_Piff(pfirstArgument, psecondArgument));
        };
        return true;
      case Operator::TLogicalXOr:
        if (tfirstArgument) free_term(tfirstArgument);
        if (ltypeFirstArgument) free_logic_type(ltypeFirstArgument);
        if (tsecondArgument) free_term(tsecondArgument);
        if (ltypeSecondArgument) free_logic_type(ltypeSecondArgument);
        if (!(pfirstArgument && psecondArgument))
          return false;
        shouldBeBoolean = true;
        { location loc = copy_loc(pfirstArgument->pred_loc);
          extend_location_with(loc, psecondArgument->pred_loc);
          predicateResult = predicate_named_cons(NULL, loc,
              predicate_Pxor(pfirstArgument, psecondArgument));
        };
        return true;
      case Operator::TBitAnd:
        binaryKind = BOBITAND;
        shouldBeIntegral = true;
        // if (operation.isConstant()) {
        //   // if (intResult)
        //   //   *intResult = firstIntResult & secondIntResult;
        // };
        break;
      case Operator::TBitOr:
        binaryKind = BOBITOR;
        shouldBeIntegral = true;
        // if (operation.isConstant()) {
        //   // if (intResult)
        //   //   *intResult = firstIntResult | secondIntResult;
        // };
        break;
      case Operator::TBitImply:
        binaryKind = BOBITOR;
        shouldBeIntegral = true;
        tfirstArgument = typeBoolTerm(ltypeFirstArgument, tfirstArgument,
            context);
        tfirstArgument = term_cons(term_node_TUnOp(uokind_UOLogicalNegate(),
              tfirstArgument), copy_loc(tfirstArgument->loc), NULL /* names */);
        break;
      case Operator::TBitEquiv:
        binaryKind = BOBITEXCLUSIVEOR;
        shouldBeIntegral = true;
        tfirstArgument = typeBoolTerm(ltypeFirstArgument, tfirstArgument,
            context);
        tfirstArgument = term_cons(term_node_TUnOp(uokind_UOLogicalNegate(),
              tfirstArgument), copy_loc(tfirstArgument->loc), NULL /* names */);
        break;
      case Operator::TBitXOr:
        binaryKind = BOBITEXCLUSIVEOR;
        shouldBeIntegral = true;
        // if (operation.isConstant()) {
        //   // if (intResult)
        //   //   *intResult = firstIntResult ^ secondIntResult;
        // };
        break;
      case Operator::TSubType:
        if (pfirstArgument) free_predicate_named(pfirstArgument);
        if (psecondArgument) free_predicate_named(psecondArgument);
        if (!(tfirstArgument && tsecondArgument))
          return false;
        free_logic_type(ltypeFirstArgument);
        free_logic_type(ltypeSecondArgument);
        { location loc = copy_loc(tfirstArgument->loc);
          extend_location_with(loc, tsecondArgument->loc);
          predicateResult = predicate_named_cons(NULL, loc,
              predicate_Psubtype(tfirstArgument, tsecondArgument));
        };
        return true;
      case Operator::TCoerce:
        if (pfirstArgument) free_predicate_named(pfirstArgument);
        if (psecondArgument) free_predicate_named(psecondArgument);
        if (!(tfirstArgument && tsecondArgument))
          return false;
        ltypeResult = logic_type_Linteger();
        if (tsecondArgument) {
          location loc = copy_loc(tfirstArgument->loc);
          extend_location_with(loc, tsecondArgument->loc);
          expressionResult = term_cons(term_node_TCoerceE(
              tfirstArgument, tsecondArgument), loc, NULL);
          ltypeResult = ltypeSecondArgument;
        }
        else {
          assert(operation._startLocation);
          expressionResult = term_cons(term_node_TCoerce(tfirstArgument,
                ltypeSecondArgument), operation._startLocation, NULL);
          ltypeResult = logic_type_dup(ltypeSecondArgument);
          operation._startLocation = NULL;
          return false; // [TODO] impossible case!!!
        };
        free_logic_type(ltypeFirstArgument);
        return true;
      case Operator::TLet:
        if (pfirstArgument) free_predicate_named(pfirstArgument);
        if (!tfirstArgument)
          return false;
        // normalize_lambda_term
        // normalizeLambdaTerm(tfirstArgument, ltypeFirstArgument, context);
        context.addLocalBinding(operation._fieldName,
          logic_var_def_cons(
            qualified_name_cons(NULL, strdup(operation._fieldName.c_str())),
            ltypeFirstArgument, LVLOCAL));
        /* logic_arg_decl */ list profile = NULL;
        location loc = copy_loc(tfirstArgument->loc);
        if (tfirstArgument->node->tag_term_node == TLAMBDA) {
          /* logic_var_def */ list quantifiers
            = tfirstArgument->node->cons_term_node.TLambda.quantifiers;
          if (quantifiers) {
            list endProfile = NULL;
            logic_var_def var = (logic_var_def) quantifiers->element.container;
            endProfile = profile = cons_container(logic_arg_decl_cons(
              logic_type_dup(var->lv_type),
              strdup(var->lv_name->decl_name)), NULL);
            while ((quantifiers = quantifiers->next) != NULL) {
              var = (logic_var_def) quantifiers->element.container;
              endProfile->next = cons_container(logic_arg_decl_cons(
                logic_type_dup(var->lv_type),
                strdup(var->lv_name->decl_name)), NULL);
              endProfile = endProfile->next;
            };
          };
          term newFirstArgument
            = tfirstArgument->node->cons_term_node.TLambda.subexpr;
          tfirstArgument->node->cons_term_node.TLambda.subexpr = NULL;
          quantifiers = tfirstArgument->node->cons_term_node
              .TLambda.quantifiers;
          while (quantifiers) {
            free_logic_var_def((logic_var_def) quantifiers->element.container);
            list next = quantifiers->next;
            free(quantifiers);
            quantifiers = next;
          };
          free_term(tfirstArgument);
          tfirstArgument = newFirstArgument;
        };

        logic_info info =
          logic_info_cons(
            qualified_name_cons(NULL, strdup(operation._fieldName.c_str())),
            context.isExternCContext(),
            NULL, NULL, opt_none(), profile, logic_body_LBterm(tfirstArgument));
        if (tsecondArgument) {
          extend_location_with(loc, tsecondArgument->loc);
          expressionResult = term_cons(term_node_TLet(
              psecondArgument ? logic_info_dup(info) : info, tsecondArgument),
              psecondArgument ? copy_loc(loc) : loc, NULL);
          ltypeResult = ltypeSecondArgument;
          if (!psecondArgument)
            loc = NULL;
        }
        if (psecondArgument) {
          extend_location_with(loc, psecondArgument->pred_loc);
          predicateResult = predicate_named_cons(NULL, loc,
            predicate_Plet(info, psecondArgument));
          loc = NULL;
        };
        return true;
    };
#if defined(__clang__) || defined(__GNUC__)
#pragma GCC diagnostic pop
#endif
    if (binaryKind >= 0) {
      if (!predicateResult && (!tfirstArgument || !tsecondArgument)) {
        context.addErrorMessage("predicates do not support "
            "arithmetic binary operation");
        return false;
      };
      if (pfirstArgument) free_predicate_named(pfirstArgument);
      if (psecondArgument) free_predicate_named(psecondArgument);
      if (!tfirstArgument || !tsecondArgument) // predicateResult
        return true;
      if (shouldBeBoolean) {
        if (isPlainBooleanType(ltypeFirstArgument, context)
            && isPlainBooleanType(ltypeSecondArgument, context)) {
          if (!context.is_builtin_boolean(ltypeFirstArgument))
            tfirstArgument = typeBoolTerm(ltypeFirstArgument, tfirstArgument,
                context);
          if (!context.is_builtin_boolean(ltypeSecondArgument))
            tsecondArgument = typeBoolTerm(ltypeSecondArgument, tsecondArgument,
                context);
          ltypeResult = context.boolean_type();
          location loc = copy_loc(tfirstArgument->loc);
          extend_location_with(loc, tsecondArgument->loc);
          expressionResult = term_cons(term_node_TBinOp((bokind) binaryKind,
            tfirstArgument, tsecondArgument), loc, NULL);
          free_logic_type(ltypeFirstArgument);
          free_logic_type(ltypeSecondArgument);
          return true;
        };
      }
      else if (shouldBeIntegral
          ? (isIntegralType(ltypeFirstArgument, context)
              && isArithmeticType(ltypeSecondArgument, context))
          : (isArithmeticType(ltypeFirstArgument, context)
              && isArithmeticType(ltypeSecondArgument, context))) {
        ltypeResult = logicArithmeticConversion(ltypeFirstArgument,
            ltypeSecondArgument, context);
        location loc = copy_loc(tfirstArgument->loc);
        extend_location_with(loc, tsecondArgument->loc);
        expressionResult = term_cons(term_node_TBinOp((bokind) binaryKind,
          makeCast(ltypeResult, tfirstArgument, ltypeFirstArgument,
            Substitution(), Substitution(), context),
          makeCast(ltypeResult, tsecondArgument, ltypeSecondArgument,
            Substitution(), Substitution(), context)), loc, NULL);
        return true;
      }
      return predicateResult;
    };
    return false;
  }
  else { // argumentsNumber == 3
    Operator::Type type = operation.getType();
    // bool isFirstRValue = false, isSecondRValue = false,
    //      isThirdRValue = false;
    // int firstIntResult = 0, secondIntResult = 0, thirdIntResult = 0;
    // double firstDoubleResult = 0, secondDoubleResult = 0,
    //        thirdDoubleResult = 0;
    logic_type ltypeThirdArgument = NULL;
    term tthirdArgument = NULL;
    predicate_named pthirdArgument = NULL;
    operation.extractLastArgument(ltypeThirdArgument, tthirdArgument,
        pthirdArgument /*, isThirdRValue,&thirdIntResult,&thirdDoubleResult*/);
    logic_type ltypeSecondArgument = NULL;
    term tsecondArgument = NULL;
    predicate_named psecondArgument = NULL;
    operation.extractLastArgument(ltypeSecondArgument, tsecondArgument,
        psecondArgument /*,isSecondRValue,&secondIntResult,
        &secondDoubleResult*/);
    logic_type ltypeFirstArgument = NULL;
    term tfirstArgument = NULL;
    predicate_named pfirstArgument = NULL;
    operation.extractLastArgument(ltypeFirstArgument, tfirstArgument,
        pfirstArgument /*,isFirstRValue,&firstIntResult,&firstDoubleResult*/);
    if (type == Operator::TConditional) {
      tfirstArgument = typeBoolTerm(ltypeFirstArgument, tfirstArgument,
          context);
      if (pfirstArgument) free_predicate_named(pfirstArgument);
      free_logic_type(ltypeFirstArgument);
      if (!(tsecondArgument || psecondArgument))
        return false;
      if (tsecondArgument) {
        if (!tthirdArgument)
          return false;
        if (!((possibleTypes & (1U <<LTRTerm))
            && tthirdArgument && ltypeSecondArgument && ltypeThirdArgument))
          return false;
        ltypeResult = conditionalConversion(ltypeSecondArgument,
            ltypeThirdArgument, context);
        if (!ltypeResult)
          return false;
        tsecondArgument =
          implicitConversion(
            ltypeResult, tsecondArgument, ltypeSecondArgument,
            false, Substitution(), Substitution(), context);
        if (!tsecondArgument) return false;
        tthirdArgument =
          implicitConversion(
            ltypeResult, tthirdArgument, ltypeThirdArgument,
            false, Substitution(), Substitution(), context);
        if (!tthirdArgument)
           return false;
        location loc = copy_loc(tfirstArgument->loc);
        extend_location_with(loc, tthirdArgument->loc);
        // implicitConversion has done the makeCast job.
        expressionResult = term_cons(term_node_TIf(tfirstArgument,
          tsecondArgument, tthirdArgument), loc, NULL);
      };
      if (psecondArgument) {
        if (!pthirdArgument)
          return false;
        if (!((possibleTypes & (1U <<LTRPredicate)) && pthirdArgument))
          return false;
        assert((possibleTypes & (1U <<LTRPredicate)) && pthirdArgument);
        location loc = copy_loc(tfirstArgument->loc);
        extend_location_with(loc, pthirdArgument->pred_loc);
        predicateResult = predicate_named_cons(NULL, loc, predicate_Pif(
            tsecondArgument ? term_dup(tfirstArgument) : tfirstArgument,
            psecondArgument, pthirdArgument));
      };
      return true;
    }
    else
      return false;
  };
  return true;
}

bool
TermOrPredicate::clearStack(logic_type& ltypeResult, term& expressionResult,
    predicate_named& predicateResult /* , bool& isRValue, bool& isConstant,
    int* intResult, double* doubleResult*/, Parser::Arguments& context) {
  if (_doesRequireValue) {
    context.addErrorMessage("expecting a term or predicate");
    return false;
  }
  ltypeResult = NULL;
  expressionResult = NULL;
  predicateResult = NULL;

  if (_operatorStack.size() == 1) {
    Operator* operation = &_operatorStack.back();
    if (!operation->isValid()) {
      operation->extractLastArgument(ltypeResult, expressionResult,
          predicateResult /*, isRValue, int* intResult, double* doubleResult*/);
      operation = NULL;
      _operatorStack.clear();
    };
  };
  // isConstant = true;
  unsigned possibleSubtypeResult = getSubExpressionPossibleTypes();
  while (!_operatorStack.empty()) {
    Operator lastOperator = _operatorStack.back();
    _operatorStack.pop_back();
    if (expressionResult || predicateResult) {
      setLastArgument(lastOperator, ltypeResult, expressionResult,
          predicateResult /* , isRValue, isConstant, intResult, doubleResult*/);
      expressionResult = NULL;
      predicateResult = NULL;
      ltypeResult = NULL;
    };
      
    if (!lastOperator.isFinished()){
      context.addErrorMessage("unexpected end of expression");
      return false;
    };
    if (!apply(lastOperator, ltypeResult, expressionResult, predicateResult,
        /* , isRValue, isConstant, intResult, doubleResult, */ context,
        possibleSubtypeResult))
      return false;
    if (lastOperator._startLocation) {
      free_location(lastOperator._startLocation);
      lastOperator._startLocation = NULL;
    }
  };
  _doesRequireValue = true;
  return true;
}

class TermOrPredicate::TermOrPredicateMemoryExtension : public TermOrPredicate {
private:
  typedef TermOrPredicate inherited;
  logic_label _firstLabel, _secondLabel;
  logic_type _secondLtype, _thirdLtype;
  term _secondNode;
  term _thirdNode;
  /* term */ list _addresses;
  /* term */ list _endAddresses;
  friend class TermOrPredicate;

public:
  TermOrPredicateMemoryExtension()
    : _firstLabel(NULL), _secondLabel(NULL), 
      _secondLtype(NULL), _thirdLtype(NULL),
      _secondNode(NULL), _thirdNode(NULL),
      _addresses(NULL), _endAddresses(NULL) {}
  TermOrPredicateMemoryExtension(const TermOrPredicateMemoryExtension& source)
    : inherited(source), _firstLabel(NULL), _secondLabel(NULL),
      _secondLtype(NULL), _thirdLtype(NULL),
      _secondNode(NULL), _thirdNode(NULL), _addresses(NULL), _endAddresses(NULL)
    {}
  ~TermOrPredicateMemoryExtension()
    { if (_firstLabel) free_logic_label(_firstLabel);
      if (_secondLabel) free_logic_label(_secondLabel);
      if (_secondLtype) free_logic_type(_secondLtype);
      if (_thirdLtype) free_logic_type(_thirdLtype);
      if (_secondNode) free_term(_secondNode);
      if (_thirdNode) free_term(_thirdNode);
      while (_addresses) {
        free_term((term) _addresses->element.container);
        _addresses = _addresses->next;
      };
    }

  void setTerm() { _possibleTypeResults = (1U << LTRTerm); }
  void setSet() { _possibleTypeResults = (1U << LTRSet); }
  void addLabel(logic_label label)
    { if (_firstLabel == NULL) _firstLabel = label;
      else {
        assert(_secondLabel == NULL);
        _secondLabel = label;
      };
    }
  bool hasLabel() const { return _firstLabel; }
  bool hasSecondLabel() const { return _secondLabel; }
  bool hasSecondNode() const { return _secondNode; }
  logic_label extractLabel()
    { assert(_firstLabel);
      logic_label result = _firstLabel;
      _firstLabel = NULL;
      return result;
    }
  /* logic_label */ option extractLabelOption()
    { option result;
      if (!_firstLabel)
        result = opt_none();
      else {
        logic_label temp = _firstLabel;
        _firstLabel = NULL;
        result = opt_some_container(temp);
      };
      return result;
    }
  logic_label extractFirstLabel()
    { assert(_firstLabel);
      logic_label result = _firstLabel;
      _firstLabel = NULL;
      return result;
    }
  /* logic_label */ option extractFirstLabelOption()
    { option result;
      if (!_firstLabel)
        result = opt_none();
      else {
        logic_label temp = _firstLabel;
        _firstLabel = NULL;
        result = opt_some_container(temp);
      };
      return result;
    }
  logic_label extractSecondLabel()
    { assert(_secondLabel);
      logic_label result = _secondLabel;
      _secondLabel = NULL;
      return result;
    }
  /* logic_label */ option extractSecondLabelOption()
    { option result;
      if (!_secondLabel)
        result = opt_none();
      else {
        logic_label temp = _secondLabel;
        _secondLabel = NULL;
        result = opt_some_container(temp);
      };
      return result;
    }
  logic_label firstLabel() const { return _firstLabel; }
  logic_label secondLabel() const { return _secondLabel; }
  logic_type extractSecondLtype() {
    logic_type result = _secondLtype; _secondLtype = NULL; return result; }
  logic_type extractThirdLtype() {
    logic_type result = _thirdLtype; _thirdLtype = NULL; return result; }
  term extractSecondNode()
    { term result = _secondNode; _secondNode = NULL; return result; }
  term extractThirdNode()
    { term result = _thirdNode; _thirdNode = NULL; return result; }
  logic_type& secondLtype() { return _secondLtype; }
  logic_type& thirdLtype() { return _thirdLtype; }
  term& secondNode() { return _secondNode; }
  void setSecondLtype (logic_type ltype) {
    assert(!_secondLtype); _secondLtype = ltype; }
  void setThirdLtype (logic_type ltype) {
    assert(!_thirdLtype); _thirdLtype = ltype; }
  void setSecondNode(term node) { assert(!_secondNode); _secondNode = node; }
  void setThirdNode(term node) { assert(!_thirdNode); _thirdNode = node; }
  int queryAdditionalNodesNumber() const
    { return _secondNode ? (_thirdNode ? 2 : 1) : 0; }
  void addAddress(term location)
    { if (_addresses == NULL)
        _addresses = _endAddresses = cons_container(location, NULL);
      else {
        _endAddresses->next = cons_container(location, NULL);
        _endAddresses = _endAddresses->next;
      };
    }
  /* term */ list extractAddresses()
    { /* term */ list result = _addresses;
      _addresses = _endAddresses = NULL;
      return result;
    }
  RuleResult* clone() const override
    { return new TermOrPredicateMemoryExtension(*this); }
};

class TermOrPredicate::TermOrPredicateList : public TermOrPredicate {
private:
  /* term */ list _components, _endComponents;
  enum Conversion
    { CNoConversion, CIntegral, CArithmetic, CPointer };
  logic_type _commonType;
  Conversion _logicConversion;

  static logic_type partialUnification(logic_type lfirst, logic_type lsecond,
      Substitution firstSub, Substitution secondSub,
      Parser::Arguments& context);
  void updateCommonTypeWith(logic_type ltype, Parser::Arguments& context);

public:
  TermOrPredicateList()
    : _components(NULL), _endComponents(NULL), _commonType(NULL),
      _logicConversion(CNoConversion) {}
  ~TermOrPredicateList()
    { while (_components) {
        free_term((term) _components->element.container);
        _components = _components->next;
      };
      if (_commonType)
        free_logic_type(_commonType);
    }

  void addComponent(term subterm, logic_type ltype, Parser::Arguments& context)
    { if (_components == NULL)
        _components = _endComponents = cons_container(subterm, NULL);
      else {
        _endComponents->next = cons_container(subterm, NULL);
        _endComponents = _endComponents->next;
      };
      updateCommonTypeWith(ltype, context);
    }
  /* term */ list extractComponents(logic_type& commonType)
    { /* term */ list result = _components;
      _components = _endComponents = NULL;
      if (_logicConversion != CNoConversion) {
        /* term */ list iter = _components;
        while (iter) {
          term node = (term) iter->element.container;
          logic_type coercionType;
          if (_logicConversion == CIntegral)
            coercionType = logic_type_Linteger();
          else if (_logicConversion == CArithmetic)
            coercionType = logic_type_Lreal();
          else
            coercionType = logic_type_Lpointer(logic_type_Lint(ICHAR));
          node = logicCoerce(coercionType, node);
          iter->element.container = node;
          free_logic_type(coercionType);
          iter = iter->next;
        };
      };

      commonType = _commonType;
      _commonType = NULL;
      return result;
    }
  RuleResult* clone() const override { return new TermOrPredicateList(*this); }
};

void
TermOrPredicate::TermOrPredicateList::updateCommonTypeWith(logic_type ltype,
    Parser::Arguments& context) {
  logic_type newType = NULL;
  if (!_commonType)
    _commonType = ltype;
  else if ((newType = isCompatibleType(_commonType, ltype, Substitution(),
        Substitution(), context)) == NULL) {
    if (_logicConversion == CNoConversion && isCType(_commonType)) {
      if (isCType(ltype)) {
        if (isIntegralType(ltype, context)
            && isIntegralType(_commonType, context)) {
          free_logic_type(_commonType);
          _commonType = logic_type_Linteger();
          _logicConversion = CIntegral;
        }
        else if (isArithmeticType(ltype, context)
            && isArithmeticType(_commonType, context)) {
          free_logic_type(_commonType);
          _commonType = logic_type_Lreal();
          _logicConversion = CArithmetic;
        }
        else if (isPointerType(ltype, Substitution(), context)
            && isPointerType(_commonType, Substitution(), context)) {
          free_logic_type(_commonType);
          _commonType = logic_type_Lpointer(logic_type_Lint(ICHAR));
          _logicConversion = CPointer;
        }
        else
          assert(false); // unimplemented
        free_logic_type(ltype);
      }
      else if (ltype->tag_logic_type == LINTEGER
          || ltype->tag_logic_type == LREAL) {
        if (isIntegralType(_commonType, context)) {
          free_logic_type(_commonType);
          _commonType = ltype;
        }
        else if (isArithmeticType(_commonType, context)) {
          free_logic_type(_commonType);
          if (ltype->tag_logic_type == LINTEGER) {
            free_logic_type(ltype);
            _commonType = logic_type_Lreal();
          }
          else
            _commonType = ltype;
        }
      }
      else
        assert(false); // unimplemented
    }
    else if (isCType(ltype)) {
      if (isIntegralType(ltype, context)
          && _commonType->tag_logic_type == LINTEGER) {
        assert(_logicConversion <= CIntegral);
        _logicConversion = CIntegral;
      }
      else if (isArithmeticType(ltype, context)
          && _commonType->tag_logic_type == LREAL) {
        assert(_logicConversion <= CArithmetic);
        _logicConversion = CArithmetic;
      }
      else if (isPointerType(ltype, Substitution(), context)
          && isCPointerType(_commonType, context)) {
        assert(_logicConversion == CPointer
            || _logicConversion == CNoConversion);
        if (_logicConversion == CNoConversion) {
          free_logic_type(_commonType);
          _commonType = logic_type_Lpointer(logic_type_Lint(ICHAR));
        };
        _logicConversion = CPointer;
      }
      else
        assert(false); // unimplemented
      free_logic_type(ltype);
    }
    else
      _commonType = partialUnification(_commonType, ltype, Substitution(),
          Substitution(), context);
  }
  else
    _commonType = newType;
}

logic_type
TermOrPredicate::TermOrPredicateList::partialUnification(logic_type lfirst,
    logic_type lsecond, Substitution substitutionFirst,
    Substitution substitutionSecond, Parser::Arguments& context) {
  if (lfirst->tag_logic_type == LNAMED || lsecond->tag_logic_type == LNAMED) {
    bool hasAdvanced = false;
    bool doesAdvance;
    do {
      doesAdvance = false;
      if (lfirst->tag_logic_type == LNAMED) {
        GlobalContext::LogicType* typeDefinition
          = context.findGlobalLogicType(lfirst->cons_logic_type.Lnamed.name);
        if (typeDefinition && is_type_synonym(typeDefinition->type_info())) {
          /* string */ list formalParameters
            = typeDefinition->type_info()->params;
          /* logic_type */ list actualParameters
            = lfirst->cons_logic_type.Lnamed.template_arguments;
            lfirst = extract_synonym_def(typeDefinition->type_info());
          substitutionFirst.pushLevel();
          Substitution::MapLogicType& map = substitutionFirst.map();
          while (formalParameters) {
            if (actualParameters == NULL) {
              context.addErrorMessage("Logic type used "
                  "with wrong number of parameters");
              assert(false);
            };
            map.insert(std::make_pair(
                std::string((const char*) formalParameters->element.container),
                (logic_type) actualParameters->element.container));
            formalParameters = formalParameters->next;
            actualParameters = actualParameters->next;
          };
          if (actualParameters != NULL) {
            context.addErrorMessage("Logic type used "
                "with wrong number of parameters");
            assert(false);
          };
          hasAdvanced = doesAdvance = true;
        };
      };
      if (lsecond->tag_logic_type == LNAMED) {
        GlobalContext::LogicType* typeDefinition
          = context.findGlobalLogicType(lsecond->cons_logic_type.Lnamed.name);
        if (is_type_synonym(typeDefinition->type_info())) {
          /* string */ list formalParameters
              = typeDefinition->type_info()->params;
          /* logic_type */ list actualParameters
              = lsecond->cons_logic_type.Lnamed.template_arguments;
          lsecond = extract_synonym_def(typeDefinition->type_info());
          substitutionSecond.pushLevel();
          Substitution::MapLogicType& map = substitutionSecond.map();
          while (formalParameters) {
            if (actualParameters == NULL) {
              context.addErrorMessage("Logic type used "
                  "with wrong number of parameters");
              assert(false);
            };
            map.insert(std::make_pair(
                std::string((const char*) formalParameters->element.container),
                (logic_type) actualParameters->element.container));
            formalParameters = formalParameters->next;
            actualParameters = actualParameters->next;
          };
          if (actualParameters != NULL) {
            context.addErrorMessage("Logic type used "
                "with wrong number of parameters");
            assert(false);
          };
          hasAdvanced = doesAdvance = true;
        };
      };
    } while (doesAdvance);
    if (hasAdvanced)
      return partialUnification(lfirst, lsecond, substitutionFirst,
          substitutionSecond, context);
  };
  if (lfirst->tag_logic_type == LVARIABLE
      || lsecond->tag_logic_type == LVARIABLE) {
    bool hasFirstVar = false, hasSecondVar = false;
    if (lfirst->tag_logic_type == LVARIABLE
        && !lfirst->cons_logic_type.Lvariable.name->prequalification) {
      // LVFormal type variable ?
      std::string name = lfirst->cons_logic_type.Lvariable.name->decl_name;
      const Substitution::MapLogicType& map = substitutionFirst.map();
      Substitution::MapLogicType::const_iterator found = map.find(name);
      if (found != map.end()) {
        hasFirstVar = true;
        lfirst = found->second;
      };
    };
    if (lsecond->tag_logic_type == LVARIABLE
        && !lsecond->cons_logic_type.Lvariable.name->prequalification) {
      // LVFormal type variable ?
      std::string name = lsecond->cons_logic_type.Lvariable.name->decl_name;
      const Substitution::MapLogicType& map = substitutionSecond.map();
      Substitution::MapLogicType::const_iterator found = map.find(name);
      if (found != map.end()) {
        hasSecondVar = true;
        lsecond = found->second;
      };
    };
    if (hasFirstVar || hasSecondVar) {
      if (hasFirstVar)
        substitutionFirst.popLevel();
      if (hasSecondVar)
        substitutionSecond.popLevel();
      return partialUnification(lfirst, lsecond, substitutionFirst,
          substitutionSecond, context);
    };
    if (lfirst->tag_logic_type == LVARIABLE
        && lsecond->tag_logic_type == LVARIABLE
        && qualified_name_equal(lfirst->cons_logic_type.Lvariable.name,
          lsecond->cons_logic_type.Lvariable.name)) {
      free_logic_type(lsecond);
      return lfirst;
    }
    assert(false);
  };

  if (isSetType(lfirst)) {
    if (isSetType(lsecond)) {
      lfirst->cons_logic_type.Lnamed.template_arguments->element.container
          = partialUnification((logic_type) lfirst->cons_logic_type
                .Lnamed.template_arguments->element.container,
              (logic_type) lsecond->cons_logic_type
                .Lnamed.template_arguments->element.container,
              substitutionFirst, substitutionSecond, context);
      free(lsecond->cons_logic_type.Lnamed.template_arguments);
      lsecond->cons_logic_type.Lnamed.template_arguments = NULL;
      free_logic_type(lsecond);
      return lfirst;
    };
    lfirst->cons_logic_type.Lnamed.template_arguments->element.container
      = partialUnification((logic_type) lfirst->cons_logic_type
            .Lnamed.template_arguments->element.container,
          lsecond, substitutionFirst, substitutionSecond, context);
    return lfirst;
  };
  if (isSetType(lsecond)) {

  };

  switch (lfirst->tag_logic_type) {
    case LVOID:
    case LINTEGER:
    case LREAL:
    case LINT:
    case LFLOAT:
    case LARRAY:
    case LPOINTER:
    case LREFERENCE:
    case LENUM:
    case LSTRUCT:
    case LUNION:
    case LCNAMED:
      if (isCType(lsecond) || lsecond->tag_logic_type == LINTEGER
          || lsecond->tag_logic_type == LREAL) {
        free_logic_type(lsecond);
        return lfirst;
      };
      assert(false); // unimplemented = "incompatible types"
      break;
    case LVARIABLE:
      assert(false); // unimplemented = "incompatible types"
      break;
    case LNAMED:
      if (context.is_builtin_boolean(lfirst)) {
        if (context.is_builtin_boolean(lsecond)) {
          free_logic_type(lsecond);
          return lfirst;
        };
        assert(false);
      };
      if (lsecond->tag_logic_type != LNAMED)
        assert(false); // unimplemented
      if (!qualified_name_equal(lfirst->cons_logic_type.Lnamed.name,
            lsecond->cons_logic_type.Lnamed.name))
        assert(false); // unimplemented
      { list firstCursor = lfirst->cons_logic_type.Lnamed.template_arguments;
        list secondCursor = lsecond->cons_logic_type.Lnamed.template_arguments;
        lsecond->cons_logic_type.Lnamed.template_arguments = NULL;
        while (firstCursor != NULL) {
          if (secondCursor == NULL)
            return NULL;
          firstCursor->element.container
            = partialUnification((logic_type) firstCursor->element.container,
                (logic_type) secondCursor->element.container,
                substitutionFirst, substitutionSecond, context);
          list temp = secondCursor;
          firstCursor = firstCursor->next;
          secondCursor = secondCursor->next;
          free(temp);
        };
        free_logic_type(lsecond);
        return lfirst;
      };
    case LARROW:
      { /* logic_type */ list firstCursor = lfirst->cons_logic_type.Larrow.left;
        /* logic_type */ list secondCursor = lsecond
            ->cons_logic_type.Larrow.left;
        lsecond->cons_logic_type.Larrow.left = NULL;
        while (firstCursor != NULL) {
          if (secondCursor == NULL)
            assert(false);
          firstCursor->element.container = partialUnification(
              (logic_type) firstCursor->element.container,
              (logic_type) secondCursor->element.container,
              substitutionFirst, substitutionSecond, context);
          list temp = secondCursor;
          firstCursor = firstCursor->next;
          secondCursor = secondCursor->next;
          free(temp);
        };
        if (secondCursor != NULL)
          assert(false);
      };
      lfirst->cons_logic_type.Larrow.right = partialUnification(
          lfirst->cons_logic_type.Larrow.right,
          lsecond->cons_logic_type.Larrow.right,
          substitutionFirst, substitutionSecond, context);
      lsecond->cons_logic_type.Larrow.right = NULL;
      lsecond->tag_logic_type = LINTEGER;
      free_logic_type(lsecond);
      return lfirst;
  };
  assert(false);
  return NULL;
}

class TermOrPredicate::Binders
    : public ::Parser::Base::RuleResult, public ::Parser::Base {
private:
  /* logic_var_def */ ForwardList _result;
  logic_type _currentDeclType;
  logic_type _currentVarType;
  std::vector<logic_type*> _parentVarTypes;
  logic_type* _postInsertionType;
  // GlobalContext::NestedContext* _qualification;
  // const clang::DeclContext* _declContext;

public:
  Binders()
    : _result(), _currentDeclType(NULL), _currentVarType(NULL),
      _postInsertionType(NULL) /*, _qualification(NULL), _declContext(NULL) */
    {}
  ~Binders()
    { list l = _result.getFront();
      while (l) {
        free_logic_var_def((logic_var_def) l->element.container);
        l = l->next;
      };
      if (_currentDeclType) free_logic_type(_currentDeclType);
      if (_currentVarType) free_logic_type(_currentVarType);
    }
  ReadResult readToken(Parser::State& state, Parser::Arguments& argument);
  /* logic_var_def */ list extractResult()
    { /* logic_var_def */ list result = _result.getFront();
      _result.clear();
      return result;
    }
};

class TermOrPredicate::SetComprehension
    : public ::Parser::Base::RuleResult, public ::Parser::Base {
private:
  term _node;
  logic_type _ltype;
  /* logic_var_def */ list _binders;
  predicate_named _suchThatCondition;

public:
  // propose to read the quantifiers before the term!
  // unimplemented! => store the token list and read the node after
  //                   from this list
  SetComprehension(logic_type ltype, term node)
    : _node(node), _ltype(ltype), _binders(NULL), _suchThatCondition(NULL) {}
  ~SetComprehension()
    { if (_node) free_term(_node);
      if (_ltype) free_logic_type(_ltype);
      while (_binders) {
        free_logic_var_def((logic_var_def) _binders->element.container);
        _binders = _binders->next;
      };
      if (_suchThatCondition)
        free_predicate_named(_suchThatCondition);
    }
  ReadResult readToken(Parser::State& state, Parser::Arguments& argument);
  term extractSet(logic_type& ltype)
    { term result =
        term_cons(
          term_node_TComprehension(
            _node, _binders,
            _suchThatCondition ?
            opt_some_container(_suchThatCondition) : opt_none()),
          copy_loc(_node->loc), NULL);
      _node = NULL;
      if (!TermOrPredicate::isSetType(_ltype))
        ltype = make_set_type(_ltype);
      else
        ltype = _ltype;
      _ltype = NULL;
      _suchThatCondition = NULL;
      return result;
    }
};

class TermOrPredicate::Range
    : public ::Parser::Base::RuleResult, public ::Parser::Base {
private:
  location _loc;
  term _minNode;
  logic_type _minType;
  term _maxNode;
  logic_type _maxType;
  friend class TermOrPredicate;

public:
  Range(location loc)
    : _loc(loc), _minNode(NULL), _minType(NULL), _maxNode(NULL), _maxType(NULL)
    {}
  Range(logic_type ltype, term node)
    : _loc(copy_loc(node->loc)), _minNode(node), _minType(ltype),
      _maxNode(NULL), _maxType(NULL) {}
  ~Range()
    { if (_loc) free_location(_loc);
      if (_minNode) free_term(_minNode);
      if (_minType) free_logic_type(_minType);
      if (_maxNode) free_term(_maxNode);
      if (_maxType) free_logic_type(_maxType);
    }
  ReadResult readToken(Parser::State& state, Parser::Arguments& argument);
  term extractSet(logic_type& ltype, Parser::Arguments& context)
    { term result = term_cons(term_node_TRange(
          _minNode ? opt_some_container(_minNode) : opt_none(),
          _maxNode ? opt_some_container(_maxNode) : opt_none()),
        _loc, NULL);
      _loc = NULL;
      _minNode = _maxNode = NULL;
      if (!_minType && !_maxType) ltype = make_set_type(logic_type_Linteger());
      else if (_minType && _maxType) {
        ltype =
          make_set_type(
            TermOrPredicate::logicArithmeticConversion(
              _minType, _maxType, context));
      }
      else if (_minType)
        ltype = make_set_type(_minType);
      else
        ltype = make_set_type(_maxType);
      _minType = _maxType = NULL;
      return result;
    }
};

class TermOrPredicate::WithConstruct
    : public ::Parser::Base::RuleResult, public ::Parser::Base {
private:
  term _node;
  logic_type _ltype;
  std::list<std::pair<term_offset, logic_type> > _updates;

public:
  WithConstruct() : _node(NULL), _ltype(NULL) {}
  WithConstruct(logic_type ltype, term node) : _node(node), _ltype(ltype) {}
  ~WithConstruct()
    { if (_node) free_term(_node);
      if (_ltype) free_logic_type(_ltype);
      std::list<std::pair<term_offset, logic_type> >::iterator
          endUpdates = _updates.end();
      for (std::list<std::pair<term_offset, logic_type> >::iterator
          iter = _updates.begin(); iter != endUpdates; ++iter) {
        if (iter->first) free_term_offset(iter->first);
        if (iter->second) free_logic_type(iter->second);
        iter->first = NULL; iter->second = NULL;
      };
      _updates.clear();
    }
  ReadResult readToken(Parser::State& state, Parser::Arguments& argument);
  term extractResult(logic_type& type, Parser::Arguments& context)
    { assert(_updates.empty());
      term result = _node;
      _node = NULL;
      type = _ltype;
      _ltype = NULL;
      return result;
    }
};

Parser::ReadResult
TermOrPredicate::readToken(Parser::State& state, Parser::Arguments& arguments) {
  enum Delimiters
    { DBegin, DIdentifier, DParen, DAfterBrace, DAfterBraceTerm, DUpdate,
      DComprehension, DRange, DBeforeCloseBrace, DAfterPrimary,
      DAfterLogicIdentifier, DAfterLogicAndCContextIdentifier,
      DAfterQualifiedLogicIdentifier, DAfterQualifiedLogicAndCContextIdentifier,
      DAfterCContextIdentifier, DAfterQualifiedCContextIdentifier,
      DBeforeLogicIdentifierLabel, DAfterLogicIdentifierLabel, DBeforeStartCall,
      DStartCall, DCallArgument, DArrayIndex, DPointField, DPointStar,
      DAfterPoint, DBinders, DLet, DLetAssignment, DType, DSizeOf, DEndSizeOf,
      DBaseAddrLabel, DBlockLengthLabel, DOffsetLabel, DAllocationLabel,
      DAllocableLabel, DFreeableLabel, DFreshLabel, DInitializedLabel, DDanglingLabel,
      DValidLabel, DValidReadLabel, DValidFunctionLabel, DValidIndexLabel, DValidRangeLabel,
      DSeparated, DBaseAddrInLabel, DBlockLengthInLabel, DOffsetInLabel,
      DAllocationInLabel, DAllocableInLabel, DFreeableInLabel, DFreshInLabel,
      DInitializedInLabel, DDanglingInLabel, DValidInLabel, DValidReadInLabel, DValidFunctionInLabel, DValidIndexInLabel,
      DValidRangeInLabel, DBaseAddrEndLabel, DBlockLengthEndLabel,
      DOffsetEndLabel, DAllocationEndLabel, DAllocableEndLabel,
      DFreeableEndLabel, DFreshEndLabel, DInitializedEndLabel, DDanglingEndLabel, DValidEndLabel,
      DValidReadEndLabel, DValidFunctionEndLabel, DValidIndexEndLabel, DValidRangeEndLabel,
      DBeforeBaseAddrTerm, DBeforeBlockLengthTerm, DBeforeOffsetTerm,
      DBeforeAllocationTerm, DBeforeAllocableTerm, DBeforeFreeableTerm,
      DBeforeFreshTerm, DBeforeInitializedLocation, DBeforeDanglingLocation, DBeforeValidLocation,
      DBeforeValidReadLocation, DBeforeValidFunctionLocation, DBeforeValidIndexLocation,
      DBeforeValidRangeLocation, DBaseAddrTerm, DBlockLengthTerm, DOffsetTerm,
      DAllocationTerm, DAllocableTerm, DFreeableTerm, DFreshTerm,
      DInitializedLocation, DDanglingLocation, DValidLocation, DValidReadLocation, DValidFunctionLocation,
      DValidIndexLocation, DValidRangeLocation, DSeparatedLocation,
      DAtBegin, DOldBegin, DAtMiddle, DOldEnd, DAtLabel, DAtEnd,
      DSetBeforeInter, DSetBeforeUnion, DSetInter, DSetUnion,
      DSetBeforeSubset, DSetSubsetFirst, DSetSubsetSecond
    };

  ReadResult result = RRNeedChars;
  switch (state.point()) {
    DefineParseCase(Begin)
      assert(!_startLocation);
      { AbstractToken token = arguments.queryToken();
        if (!_loc)
          absorbLoc(arguments.newTokenLocation());
#if defined(__clang__) || defined(__GNUC__)
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wswitch"
#endif
        switch (token.getType()) {
          case KeywordToken::TType:
            // This keyword is not expected here and as it does not begin with a backslash
            // we treat it as an identifier
            _labelOrIdentifier = "type";
            _startLocation = arguments.newTokenLocation();
            arguments.extendLocationWithToken(_loc);
            DefineGotoCase(Identifier)
          case AbstractToken::TIdentifier:
            _labelOrIdentifier =
              ((const IdentifierToken&) arguments.getContentToken()).content();
            _startLocation = arguments.newTokenLocation();
            arguments.extendLocationWithToken(_loc);
            DefineGotoCase(Identifier)
          case AbstractToken::TKeyword: {
            const KeywordToken& keyword = (const KeywordToken&)token;
            switch (keyword.getType()) {
              case KeywordToken::TForall:
                if (excludeTypeAsResult()) {
                  pushPrefixUnaryOperator(
                    Operator::TForall, arguments.newTokenLocation());
                  Binders* binders = new Binders;
                  state.absorbRuleResult(binders);
                  DefineShift(Binders, *binders, &Binders::readToken)
                };
                break;
              case KeywordToken::TExists:
                if (excludeTypeAsResult()) {
                  pushPrefixUnaryOperator(
                    Operator::TExists, arguments.newTokenLocation());
                  Binders* binders = new Binders;
                  state.absorbRuleResult(binders);
                  // no need for _startLocation
                  DefineShift(Binders, *binders, &Binders::readToken)
                };
                break;
              case KeywordToken::TLet:
                if (excludeTypeAsResult()) {
                  pushPrefixBinaryOperator(
                    Operator::TLet, arguments.newTokenLocation());
                  // no need for _startLocation
                  DefineGotoCase(Let)
                };
                break;
              case KeywordToken::TBool:
              case KeywordToken::TChar:
              case KeywordToken::TConst:
              case KeywordToken::TVolatile:
              case KeywordToken::TDouble:
              case KeywordToken::TFloat:
              case KeywordToken::TInt:
              case KeywordToken::TLong:
              case KeywordToken::TShort:
              case KeywordToken::TSigned:
              case KeywordToken::TUnsigned:
              case KeywordToken::TVoid:
              case KeywordToken::TInteger:
              case KeywordToken::TReal:
              case KeywordToken::TWcharT:
              case KeywordToken::TChar16:
              case KeywordToken::TChar32:
                if (ensureTypeAsResult()) {
                  LogicType* rule = new LogicType;
                  state.absorbRuleResult(rule);
                  DefineShiftAndParse(Type, *rule, &LogicType::readToken);
                }
                break;
              case KeywordToken::TSizeof:
                if (excludeTypeAsResult()) {
                  _startLocation = arguments.newTokenLocation();
                  DefineGotoCase(SizeOf)
                };
                break;
              case KeywordToken::TNull:
                if (excludeTypeAsResult()) {
                  pushLastArgument(
                    logic_type_Lpointer(logic_type_Lvoid()),
                    term_cons(
                      term_node_TNull(), arguments.newTokenLocation(), NULL),
                    NULL);
                  if (_doesStopTypeAmbiguity)
                    DefineTReduce
                  arguments.extendLocationWithToken(_loc);
                  DefineGotoCase(AfterPrimary)
                }
                break;
              case KeywordToken::TTrue:
              case KeywordToken::TFalse:
                if (excludeTypeAsResult()) {
                  predicate pred =
                    (keyword.getType() == KeywordToken::TTrue)
                    ? predicate_Ptrue() : predicate_Pfalse();
                  term term =
                    (keyword.getType() == KeywordToken::TTrue)
                    ? term_true(arguments.newTokenLocation()) : 
                    term_false(arguments.newTokenLocation());
                  pushLastArgument(
                    arguments.boolean_type(),
                    term,
                    predicate_named_cons(
                      NULL, arguments.newTokenLocation(), pred));
                  if (_doesStopTypeAmbiguity)
                    DefineTReduce
                  arguments.extendLocationWithToken(_loc);
                  DefineGotoCase(AfterPrimary)
                }
                break;
              case KeywordToken::TResult:
                if (excludeTypeAsResult()) {
                  logic_type ltypeResult = arguments.createResultType();
                  if (!ltypeResult) {
                    DefineAddError("\\result can only be used in ensures "
                      "clause of a function contract or in returns clause "
                      "of a statement contract.")
                    arguments.extendLocationWithToken(_loc);
                    DefineGotoCase(AfterPrimary)
                  };
                  logic_type ltypeTerm = logic_type_dup(ltypeResult);
                  term expressionResult =
                    term_cons(
                      term_node_TLval(
                        term_lval_cons(
                          term_lhost_TResult(ltypeTerm),
                          term_offset_TNoOffset())),
                      arguments.newTokenLocation(), NULL);
                  predicate_named predicateResult = convertTermToPredicate(
                      ltypeTerm, expressionResult, arguments);
                  pushLastArgument(ltypeResult, expressionResult,
                      predicateResult);
                  arguments.extendLocationWithToken(_loc);
                  if (_doesStopTypeAmbiguity)
                    DefineTReduce
                  DefineGotoCase(AfterPrimary)
                }
                break;
              case KeywordToken::TExitStatus:
                if (excludeTypeAsResult()) {
                  logic_type lt = logic_type_Linteger();
                  logic_var status =
                    logic_var_cons(
                      qualified_name_cons(NULL, "\\exit_status"), LVBUILTIN);
                  term tres =
                    term_cons(
                      term_node_TLval(
                        term_lval_cons(
                          term_lhost_TVar(status),term_offset_TNoOffset())),
                      arguments.newTokenLocation(),NULL);
                  predicate_named pres =
                    convertTermToPredicate(lt,tres,arguments);
                  pushLastArgument(lt,tres,pres);
                  arguments.extendLocationWithToken(_loc);
                  if (_doesStopTypeAmbiguity)
                    DefineTReduce;
                  DefineGotoCase(AfterPrimary)
                }
                break;
              case KeywordToken::TAt:
                if (excludeTypeAsResult()) {
                  _startLocation = arguments.newTokenLocation();
                  DefineGotoCase(AtBegin)
                };
                break;
              case KeywordToken::TOld:
                if (excludeTypeAsResult()) {
                  _startLocation = arguments.newTokenLocation();
                  DefineGotoCase(OldBegin)
                };
                break;
              case KeywordToken::TBaseAddr:
                if (excludeTypeAsResult()) {
                  _startLocation = arguments.newTokenLocation();
                  DefineGotoCase(BaseAddrLabel)
                };
                break;
              case KeywordToken::TBlockLength:
                if (excludeTypeAsResult()) {
                  _startLocation = arguments.newTokenLocation();
                  DefineGotoCase(BlockLengthLabel)
                };
                break;
              case KeywordToken::TOffset:
                if (excludeTypeAsResult()) {
                  _startLocation = arguments.newTokenLocation();
                  DefineGotoCase(OffsetLabel)
                };
                break;
              case KeywordToken::TAllocation:
                if (excludeTypeAsResult()) {
                  _startLocation = arguments.newTokenLocation();
                  DefineGotoCase(AllocationLabel)
                };
                break;
              case KeywordToken::TLAutomatic:
              case KeywordToken::TLDynamic:
              case KeywordToken::TLRegister:
              case KeywordToken::TLStatic:
              case KeywordToken::TLUnallocated:
                if (excludeTypeAsResult()) {
                  pushLastArgument(
                    logic_type_Lpointer(logic_type_Lvoid()),
                    term_cons(
                      term_node_TNull(), arguments.newTokenLocation(), NULL),
                    NULL);
                  arguments.extendLocationWithToken(_loc);
                  DefineAddError("the keywords \\automatic, \\dynamic, "
                      "\\register, \\static, \\unallocated "
                      "are not yet implemented")
                  DefineGotoCase(AfterPrimary)
                }
                break;
              case KeywordToken::TAllocable:
                if (excludeTypeAsResult()) {
                  _startLocation = arguments.newTokenLocation();
                  DefineGotoCase(AllocableLabel)
                };
                break;
              case KeywordToken::TFreeable:
                if (excludeTypeAsResult()) {
                  _startLocation = arguments.newTokenLocation();
                  DefineGotoCase(FreeableLabel)
                };
                break;
              case KeywordToken::TFresh:
                if (excludeTypeAsResult()) {
                  _startLocation = arguments.newTokenLocation();
                  DefineGotoCase(FreshLabel)
                };
                break;
              case KeywordToken::TInitialized:
                if (excludeTypeAsResult()) {
                  _startLocation = arguments.newTokenLocation();
                  DefineGotoCase(InitializedLabel)
                };
                break;
              case KeywordToken::TDangling:
                if (excludeTypeAsResult()) {
                  _startLocation = arguments.newTokenLocation();
                  DefineGotoCase(DanglingLabel)
                };
                break;
              case KeywordToken::TValid:
                if (excludeTypeAsResult()) {
                  _startLocation = arguments.newTokenLocation();
                  DefineGotoCase(ValidLabel)
                };
                break;
              case KeywordToken::TValidRead:
                if (excludeTypeAsResult()) {
                  _startLocation = arguments.newTokenLocation();
                  DefineGotoCase(ValidReadLabel)
                };
                break;
              case KeywordToken::TValidFunction:
                if (excludeTypeAsResult()) {
                  _startLocation = arguments.newTokenLocation();
                  DefineGotoCase(ValidFunctionLabel)
                };
                break;
              case KeywordToken::TValidIndex:
                if (excludeTypeAsResult()) {
                  _startLocation = arguments.newTokenLocation();
                  DefineGotoCase(ValidIndexLabel)
                };
                break;
              case KeywordToken::TValidRange:
                if (excludeTypeAsResult()) {
                  _startLocation = arguments.newTokenLocation();
                  DefineGotoCase(ValidRangeLabel)
                };
                break;
              case KeywordToken::TSeparated:
                if (excludeTypeAsResult()) {
                  _startLocation = arguments.newTokenLocation();
                  DefineGotoCase(Separated)
                };
                break;
              case KeywordToken::TEmpty:
                if (excludeTypeAsResult()) {
                  pushLastArgument(
                    make_set_type(
                      logic_type_Lvariable(
                        qualified_name_cons(NULL, strdup("_")))),
                    term_cons(
                      term_node_TEmpty_set(), arguments.newTokenLocation(),
                      NULL),
                    NULL);
                  arguments.extendLocationWithToken(_loc);
                  if (_doesStopTypeAmbiguity)
                    DefineTReduce
                  DefineGotoCase(AfterPrimary)
                }
                break;
              case KeywordToken::TLUnion:
                if (excludeTypeAsResult()) {
                  _startLocation = arguments.newTokenLocation();
                  DefineGotoCase(SetBeforeUnion)
                };
                break;
              case KeywordToken::TLInter:
                if (excludeTypeAsResult()) {
                  _startLocation = arguments.newTokenLocation();
                  DefineGotoCase(SetBeforeInter)
                };
                break;
              case KeywordToken::TSubset:
                if (excludeTypeAsResult()) {
                  _startLocation = arguments.newTokenLocation();
                  DefineGotoCase(SetBeforeSubset)
                };
                break;
              default:
                break;
            };
            { arguments.lexer().assumeContentToken();
              DefineAddError(
                std::string("keyword '")
                .append(arguments.getContentToken().str())
                .append("' encountered when parsing term or predicate"));
            };
            DefineTReduce;
            }
          case AbstractToken::TLiteral:
            { LiteralToken::Type type = ((const LiteralToken&) token).getType();
              logic_constant constant = NULL;
              logic_type valueType = NULL;
              excludeTypeAsResult();
              term_node node = NULL;
              switch (type) {
                case LiteralToken::TInteger:
                  constant =
                    logic_constant_LCInt(
                      strdup(
                        ((const IntegerLiteralToken&)
                         arguments.getContentToken()).getValue().c_str()));
                  valueType = logic_type_Linteger();
                  node = term_node_TConst(constant);
                  break;
                case LiteralToken::TCharacter: {
                  const CharacterLiteralToken& token =
                    (const CharacterLiteralToken&) arguments.getContentToken();
                  if (token.isChar()) {
                    constant = logic_constant_LChr(token.getChar());
                    valueType = logic_type_Lint(ICHAR);
                    node =
                      term_node_TCastE(
                        logic_type_dup(valueType),
                        term_cons(
                          term_node_TConst(constant),
                          arguments.newTokenLocation(), NULL));
                  } else { //wide char
                    constant = logic_constant_LWChr(token.getWideChar());
                    valueType = logic_type_Lint(IWCHAR);
                    node =
                      term_node_TCastE(
                        logic_type_dup(valueType),
                        term_cons(
                          term_node_TConst(constant),
                          arguments.newTokenLocation(),NULL));
                  }
                  break;
                }
                case LiteralToken::TFloating:
                  { const char* real =
                      strdup(
                        ((const FloatingLiteralToken&)
                         arguments.getContentToken())
                        .getValueAsString().c_str());
                    constant = logic_constant_LCReal(real);
                  };
                  valueType = logic_type_Lreal();
                  node = term_node_TConst(constant);
                  break;
                case LiteralToken::TString:
                  constant = logic_constant_LStr(
                    strdup(((const StringLiteralToken&)
                        arguments.getContentToken()).content().c_str()));
                  valueType = logic_type_Lpointer(logic_type_Lint(ICHAR));
                  node = term_node_TConst(constant);
                  break;
                default:
                  assert(false);
              };
              pushLastArgument(
                valueType, term_cons(node,arguments.newTokenLocation(),NULL),
                NULL);
              arguments.extendLocationWithToken(_loc);
              if (_doesStopTypeAmbiguity)
                DefineTReduce
              DefineGotoCase(AfterPrimary)
            };
          case AbstractToken::TOperatorPunctuator:
            { OperatorPunctuatorToken::Type type
                = ((const OperatorPunctuatorToken&) token).getType();
              switch (type) {
                case OperatorPunctuatorToken::TOpenParen:
                  _startLocation = arguments.newTokenLocation();
                  { TermOrPredicate* subTerm = new TermOrPredicate;
                    state.absorbRuleResult(subTerm);
                    subTerm->_possibleTypeResults = _possibleTypeResults;
                    subTerm->_possibleTypeResults |= (1U << LTRType);
                      // for casts
                    assert(_doesRequireValue);
                    DefineShift(Paren, *subTerm, &TermOrPredicate::readToken);
                  };
                case OperatorPunctuatorToken::TOpenBrace:
                  _startLocation = arguments.newTokenLocation();
                  excludeTypeAsResult();
                  DefineGotoCase(AfterBrace)
                case OperatorPunctuatorToken::TRange:
                  _startLocation = arguments.newTokenLocation();
                  excludeTypeAsResult();
                  { Range* range=new Range(arguments.newTokenLocation());
                    state.absorbRuleResult(range);
                    DefineShift(Range, *range, &Range::readToken);
                  };
                case OperatorPunctuatorToken::TPlus:
                  excludeTypeAsResult();
                  pushPrefixUnaryOperator(
                    Operator::TUnaryPlus, arguments.newTokenLocation());
                  DefineGotoCase(Begin)
                case OperatorPunctuatorToken::TMinus:
                  excludeTypeAsResult();
                  pushPrefixUnaryOperator(
                    Operator::TUnaryMinus, arguments.newTokenLocation());
                  DefineGotoCase(Begin)
                case OperatorPunctuatorToken::TStar:
                  excludeTypeAsResult();
                  pushPrefixUnaryOperator(
                    Operator::TDereference, arguments.newTokenLocation());
                  DefineGotoCase(Begin)
                case OperatorPunctuatorToken::TTilda:
                  excludeTypeAsResult();
                  pushPrefixUnaryOperator(
                    Operator::TComplement, arguments.newTokenLocation());
                  DefineGotoCase(Begin)
                case OperatorPunctuatorToken::TNot:
                  excludeTypeAsResult();
                  pushPrefixUnaryOperator(
                    Operator::TNot, arguments.newTokenLocation());
                  DefineGotoCase(Begin)
                case OperatorPunctuatorToken::TAmpersand: {
                    excludeTypeAsResult();
                    pushPrefixUnaryOperator(
                      Operator::TAddressOf, arguments.newTokenLocation());
                    DefineGotoCase(Begin);
                  }
                // case OperatorPunctuatorToken::TPlusPlus:
                // case OperatorPunctuatorToken::TMinusMinus:
                default:
                  break;
              };
            };
        };
#if defined(__clang__) || defined(__GNUC__)
#pragma GCC diagnostic pop
#endif
        { std::ostringstream outToken;
          arguments.lexer().assumeContentToken();
          arguments.getContentToken().write(outToken,
              AbstractToken::PersistentFormat().setPretty());
          DefineAddError(std::string("unexpected token '")
              .append(outToken.str())
              .append("' when starting to parse a term"));
        };
        DefineTReduce
      };
    DefineParseCase(Identifier)
      assert(_startLocation && _labelOrIdentifier.size() > 0);
      { AbstractToken token
        = arguments.queryToken();
        if (token.getType() == AbstractToken::TOperatorPunctuator
            && ((const OperatorPunctuatorToken&) token).getType()
              == OperatorPunctuatorToken::TColon &&
            !(queryLastOperator().getType() == Operator::TConditional &&
              queryLastOperator().getLeftSubExpressions() == 2)
            ) {
          // We have an ambiguity here between named terms or predicates
          // and ternary operator ( exp ? x : y )
          // ACSL chooses to consider that in this case the colon is the one
          // of the ternary operator.
          excludeTypeAsResult();
          pushPrefixUnaryOperator(Operator::TNaming, _startLocation);
          Operator& syntacticNaming = _operatorStack.back();
          syntacticNaming._fieldName = _labelOrIdentifier;
          _labelOrIdentifier.clear();
          _startLocation = NULL;
          DefineGotoCase(Begin)
        };
      };
      { std::string identifier = _labelOrIdentifier;
        _labelOrIdentifier.clear();
        logic_var_def var = arguments.hasLocalBinding(identifier);
        if (var && excludeTypeAsResult()) {
          extend_location_with(_startLocation, _loc);
          pushLastArgument(logic_type_dup(var->lv_type),
            term_cons(term_node_TLval(term_lval_cons(
              term_lhost_TVar(logic_var_cons(
                qualified_name_dup(var->lv_name),
                var->lv_kind)), term_offset_TNoOffset())),
            _startLocation, NULL), NULL /* , true, false */); 
          _startLocation = NULL;
          if (_doesStopTypeAmbiguity)
            DefineReduceAndParse
          DefineGotoCaseAndParse(AfterPrimary)
        };
        logic_type arg_type = arguments.hasLogicFormal(identifier);
        if (arg_type && excludeTypeAsResult()) {
          extend_location_with(_startLocation,_loc);
          pushLastArgument(
           logic_type_dup(arg_type),
           term_cons(
            term_node_TLval(
              term_lval_cons(
               term_lhost_TVar(
                logic_var_cons(
                  qualified_name_cons(NULL,copy_string(identifier)),
                  LVFORMAL)),
               term_offset_TNoOffset())),
            _startLocation,
            NULL),
           NULL);
          _startLocation = NULL;
          if(_doesStopTypeAmbiguity)
           DefineReduceAndParse;
          DefineGotoCaseAndParse(AfterPrimary);
        }
        bool hasFoundLogicQualification = false;
        if ((_qualification = arguments.findLogicName(identifier)) != NULL) {
          if (_qualification->ssons() || _qualification->isLogicVariable()
              || _qualification->isOverloadedLogicFunctions())
            hasFoundLogicQualification = true;
        };
        const clang::TemplateArgument* templateArgument=NULL;
        const clang::NamedDecl* cidentifier = arguments.isCodeName(identifier,
            &templateArgument);
        if (cidentifier) {
          clang::Decl::Kind kind = cidentifier->getKind();
          if (kind >= clang::Decl::firstRecord
              && kind <= clang::Decl::lastRecord) {
            assert(llvm::dyn_cast<clang::RecordDecl>(cidentifier));
            _declContext = static_cast<const clang::RecordDecl*>(cidentifier);
            if (!hasFoundLogicQualification)
              DefineGotoCaseAndParse(AfterCContextIdentifier)
            else
              DefineGotoCaseAndParse(AfterLogicAndCContextIdentifier)
          };
          if (kind >= clang::Decl::firstType && kind <= clang::Decl::lastType) {
            if (ensureTypeAsResult()) {
              if (hasFoundLogicQualification)
                DefineGotoCaseAndParse(AfterLogicIdentifier)
              logic_type typeResult =
                  from_c_named_type(cidentifier,arguments.get_clang_utils());
              LogicType* rule = new LogicType;
              rule->setType(typeResult, _startLocation);
              state.absorbRuleResult(rule);
              _startLocation = NULL;
              DefineShiftAndParseFrom(Type, 10
                  /* LogicType::readToken::TypeSuffix */,
                  *rule, &LogicType::readToken);
            };
          };
          if (kind >= clang::Decl::firstFunction
              && kind <= clang::Decl::lastFunction) {
            AbstractToken token = arguments.queryToken();
            std::string errorMessage;
            if (token.getType() == AbstractToken::TOperatorPunctuator
                && ((const OperatorPunctuatorToken&) token).getType()
                == OperatorPunctuatorToken::TOpenParen) {
              if (hasFoundLogicQualification &&
                  _qualification->isOverloadedLogicFunctions()) {
                // logic function call
                DefineGotoCaseAndParse(AfterLogicIdentifier)
              } else {
                errorMessage =
                  std::string("calls to C++ functions/methods like '")
                  .append(identifier).append("' are not allowed in ACSL++");
                DefineAddError(errorMessage);
                pushLastArgument(
                  logic_type_Linteger(),tzero(_startLocation),NULL);
                DefineGotoCaseAndParse(AfterPrimary) }
            } else { 
              if(hasFoundLogicQualification) {
                DefineGotoCaseAndParse(AfterLogicIdentifier)
              } else {
                // Fct pointer. Can be used in comparisons.
                excludeTypeAsResult();
                const clang::FunctionDecl* funDecl =
                  static_cast<const clang::FunctionDecl*>(cidentifier);
                term_lhost fun =
                  term_lhost_TCFun(
                    arguments.get_clang_utils()->makeQualifiedName(*funDecl),
                    arguments.get_clang_utils()->makeSignature(*funDecl));
                pushLastArgument(
                  arguments.get_clang_utils()->makeLogicType(
                    arguments.tokenSourceLocation(),
                    funDecl->getType().getTypePtr()),
                  term_cons(
                    term_node_TLval(
                      term_lval_cons(fun, term_offset_TNoOffset())),
                    _startLocation, NULL),
                  NULL /* , true, false */);
                _startLocation = NULL;
                DefineGotoCaseAndParse(AfterPrimary)
              }
            }
          }
          if ((kind >= clang::Decl::firstTemplate
                && kind <= clang::Decl::lastTemplate)
              || kind == clang::Decl::NonTypeTemplateParm) {
            assert(templateArgument);
            switch (templateArgument->getKind()) {
              case clang::TemplateArgument::Type:
                if (ensureTypeAsResult()) {
                  if (hasFoundLogicQualification)
                    DefineGotoCaseAndParse(AfterLogicIdentifier)
                  logic_type typeResult =
                      arguments.get_clang_utils()->makeLogicType(
                        arguments.tokenSourceLocation(),
                        templateArgument->getAsType().getTypePtr());
                  LogicType* rule = new LogicType;
                  rule->setType(typeResult, _startLocation);
                  state.absorbRuleResult(rule);
                  _startLocation = NULL;
                  DefineShiftAndParseFrom(Type, 10
                      /* LogicType::readToken::TypeSuffix */,
                      *rule, &LogicType::readToken);
                };
                break;
              case clang::TemplateArgument::Integral:
                { llvm::APSInt value = templateArgument->getAsIntegral();
                  if (hasFoundLogicQualification)
                    DefineGotoCaseAndParse(AfterLogicIdentifier)
                  excludeTypeAsResult();
                  extend_location_with(_startLocation, _loc);
                  term constant =
                    tinteger(_startLocation,value.getLimitedValue(UINT64_MAX));
                  pushLastArgument(logic_type_Linteger(),constant,NULL);
                }
                if (_doesStopTypeAmbiguity)
                  DefineReduceAndParse
                DefineGotoCaseAndParse(AfterPrimary)
              default:
                break;
            };
          };
          
          switch (kind) {
            // case clang::Decl::Label:
            case clang::Decl::Namespace:
              assert(llvm::dyn_cast<clang::NamespaceDecl>(cidentifier));
              _declContext = static_cast<const clang::NamespaceDecl*>(
                  cidentifier);
              if (!hasFoundLogicQualification)
                DefineGotoCaseAndParse(AfterCContextIdentifier)
              else
                DefineGotoCaseAndParse(AfterLogicAndCContextIdentifier)
            case clang::Decl::NamespaceAlias:
              assert(llvm::dyn_cast<clang::NamespaceAliasDecl>(cidentifier));
              _declContext = static_cast<const clang::NamespaceAliasDecl*>(
                  cidentifier)->getNamespace();
              if (!hasFoundLogicQualification)
                DefineGotoCaseAndParse(AfterCContextIdentifier)
              else
                DefineGotoCaseAndParse(AfterLogicAndCContextIdentifier)
            case clang::Decl::Var:
            case clang::Decl::ParmVar:
              if (hasFoundLogicQualification)
                DefineGotoCaseAndParse(AfterLogicIdentifier)
              { assert(llvm::dyn_cast<clang::VarDecl>(cidentifier));
                excludeTypeAsResult();
                const clang::VarDecl* varDecl
                  = static_cast<const clang::VarDecl*>(cidentifier);
                logic_var_kind kind = LVCGLOBAL;
                if (cidentifier->getKind() == clang::Decl::ParmVar
                    || varDecl->isLocalVarDecl())
                  kind = LVCLOCAL;
                logic_var var = logic_var_cons(arguments.get_clang_utils()
                    ->makeQualifiedName(*varDecl), kind);
                pushLastArgument(
                  arguments.get_clang_utils()->makeLogicType(
                    arguments.tokenSourceLocation(),
                    varDecl->getType().getTypePtr()),
                  term_cons(term_node_TLval(term_lval_cons(term_lhost_TVar(var),
                    term_offset_TNoOffset())), _startLocation, NULL),
                  NULL /* , true, false */); 
              };
              _startLocation = NULL;
              if (_doesStopTypeAmbiguity)
                DefineReduceAndParse
              DefineGotoCaseAndParse(AfterPrimary)
            case clang::Decl::Field:
              if (hasFoundLogicQualification)
                DefineGotoCaseAndParse(AfterLogicIdentifier)
              { assert(llvm::dyn_cast<clang::FieldDecl>(cidentifier));
                excludeTypeAsResult();
                const clang::FieldDecl* fieldDecl
                  = static_cast<const clang::FieldDecl*>(cidentifier);
                term_lval termVal = arguments.thisLval();
                assert (termVal);
                addOffset(
                  termVal->offset,
                  term_offset_TField(copy_string(fieldDecl->getName().str()),
                                     term_offset_TNoOffset()));
                term result = term_cons(term_node_TLval(termVal),
                    copy_loc(_startLocation), NULL /* names */);
                pushLastArgument(
                  arguments.get_clang_utils()->makeLogicType(
                    arguments.tokenSourceLocation(),fieldDecl->getType().getTypePtr()),
                  result, NULL /* , true, false */); 
              };
              _startLocation = NULL;
              if (_doesStopTypeAmbiguity)
                DefineReduceAndParse
              DefineGotoCaseAndParse(AfterPrimary)
            case clang::Decl::IndirectField:
              if (hasFoundLogicQualification)
                DefineGotoCaseAndParse(AfterLogicIdentifier)
              { assert(llvm::dyn_cast<clang::IndirectFieldDecl>(cidentifier));
                excludeTypeAsResult();
                const clang::IndirectFieldDecl* fieldDecl
                  = static_cast<const clang::IndirectFieldDecl*>(cidentifier);
                term_lval termVal = arguments.thisLval();
                unsigned chainingSize = fieldDecl->getChainingSize() - 1;
                clang::IndirectFieldDecl::chain_iterator
                    chainIter = fieldDecl->chain_begin();
                term_offset offset = NULL;
                term_offset* endOffset = &offset;
                for (unsigned chainIndex = 0; chainIndex < chainingSize;
                    ++chainIndex) {
                  std::string name = arguments.get_clang_utils()
                    ->findAnonymousName(*chainIter);
                  if (name.length() == 0) {
                    DefineAddError(
                      std::string("unknown anonymous indirection '")
                        .append(fieldDecl->getName().str()).append("'"));
                    break;
                  };
                  *endOffset = term_offset_TField(copy_string(name), NULL);
                  endOffset = &(*endOffset)->cons_term_offset.TField.offset;
                  ++chainIter;
                }
                *endOffset = term_offset_TField(copy_string(
                    fieldDecl->getName().str()), term_offset_TNoOffset());
                addOffset(termVal->offset, offset);
                term result =
                  term_cons(term_node_TLval(termVal),
                            copy_loc(_startLocation), NULL /* names */);
                pushLastArgument(
                  arguments.get_clang_utils()->makeLogicType(
                    arguments.tokenSourceLocation(),
                    fieldDecl->getType().getTypePtr()),
                  result, NULL /* , true, false */); 
              };
              _startLocation = NULL;
              if (_doesStopTypeAmbiguity)
                DefineReduceAndParse
              DefineGotoCaseAndParse(AfterPrimary)
            case clang::Decl::EnumConstant:
              if (hasFoundLogicQualification)
                DefineGotoCaseAndParse(AfterLogicIdentifier)
              assert(llvm::dyn_cast<clang::EnumConstantDecl>(cidentifier));
              excludeTypeAsResult();
              { const clang::EnumConstantDecl* constantDecl
                    = static_cast<const clang::EnumConstantDecl*>(cidentifier);
                logic_constant constant = logic_constant_LCEnum((int64_t)
                  constantDecl->getInitVal().getLimitedValue(UINT64_MAX),
                  arguments.get_clang_utils()
                    ->makeQualifiedName(*constantDecl));
                extend_location_with(_startLocation, _loc);
                assert(llvm::dyn_cast<clang::EnumType>(
                  constantDecl->getType().getTypePtr()));
                pushLastArgument(logic_type_Lenum(
                  arguments.get_clang_utils()->makeQualifiedName(
                    *((const clang::EnumType*) constantDecl->getType()
                      .getTypePtr())->getDecl())),
                  term_cons(term_node_TConst(constant),
                  _startLocation, NULL), NULL /* , true, false */); 
              };
              _startLocation = NULL;
              if (_doesStopTypeAmbiguity)
                DefineReduceAndParse
              DefineGotoCaseAndParse(AfterPrimary)
            default:
              break;
          };
        };
        if (hasFoundLogicQualification)
          DefineGotoCaseAndParse(AfterLogicIdentifier);
        if (_qualification) {
          if (_qualification->isLogicType() && ensureTypeAsResult()) {
            logic_type_info ti = _qualification->asLogicType().type_info();
            logic_type typeResult =
              logic_type_Lnamed(
                qualified_name_dup(ti->type_name), ti->is_extern_c, NULL);
            LogicType* rule = new LogicType;
            rule->setType(typeResult, _startLocation);
            state.absorbRuleResult(rule);
            _startLocation = NULL;
            DefineShiftAndParseFrom(Type, 10
                /*LogicType::readToken::TypeSuffix */,
                *rule, &LogicType::readToken);
          };
          DefineGotoCaseAndParse(AfterLogicIdentifier)
        };
        DefineAddError(std::string("unknown identifier '").append(identifier)
            .append("'"));
        pushLastArgument(logic_type_Linteger(),tzero(_startLocation),NULL);
        DefineGotoCaseAndParse(AfterPrimary)
      };
    DefineParseCase(Paren)
      assert(_startLocation);
      { AbstractToken token = arguments.queryToken();
        Parser::State::RuleAccess::TCastFromRule<TermOrPredicate>
            subterm(state.getRuleResult());
        if (subterm->isType()) {
          if (token.getType() == AbstractToken::TOperatorPunctuator) {
            if (((const OperatorPunctuatorToken&) token).getType()
                == OperatorPunctuatorToken::TCloseParen) {
              pushPrefixUnaryOperator(Operator::TCast, _startLocation);
              _startLocation = NULL;
              _operatorStack.back().absorbTypeCast(subterm->_typeResult);
              subterm->_typeResult = NULL;
              state.freeRuleResult();
              excludeTypeAsResult();
              DefineGotoCase(Begin)
            };
          };
          std::ostringstream outToken;
          arguments.lexer().assumeContentToken();
          arguments.getContentToken().write(outToken,
              AbstractToken::PersistentFormat().setPretty());
          DefineAddError(std::string("unexpected token '")
              .append(outToken.str())
              .append("' in a logic cast"));
          DefineTReduce
        };
        // int intResult = 0; double doubleResult = 0;
        logic_type ltype = NULL;
        term termNode = NULL;
        predicate_named predicateNode = NULL;
        // bool isRValue = false;
        // bool isConstant = false;
        subterm->extractTermOrPredicate(arguments, ltype, termNode,
            predicateNode);
        state.freeRuleResult();
        if (termNode || predicateNode) {
          excludeTypeAsResult();
          pushLastArgument(ltype, termNode, predicateNode /* , isRValue,
            isConstant, isConstant ? &intResult : NULL,
            isConstant ? &doubleResult : NULL*/);

          if (token.getType() == AbstractToken::TOperatorPunctuator) {
            if (((const OperatorPunctuatorToken&) token).getType()
                == OperatorPunctuatorToken::TCloseParen) {
              arguments.extendLocationWithToken(_loc);
              free_location(_startLocation);
              _startLocation = NULL;
              if (_doesStopTypeAmbiguity)
                DefineTReduce
              DefineGotoCase(AfterPrimary)
            }
          };
        };
        std::ostringstream outToken;
        arguments.lexer().assumeContentToken();
        arguments.getContentToken().write(outToken,
            AbstractToken::PersistentFormat().setPretty());
        DefineAddError(std::string("unexpected token '")
            .append(outToken.str())
            .append("' when starting to parse a term"));
      };
      DefineTReduce
    DefineParseCase(AfterBrace)
      assert(_startLocation);
      { AbstractToken token = arguments.queryToken();
        if (token.getType() == AbstractToken::TOperatorPunctuator) {
          OperatorPunctuatorToken::Type type
            = ((const OperatorPunctuatorToken&) token).getType();
          if (type == OperatorPunctuatorToken::TPunct) {
            DefineAddError("unsupported aggregated struct construct");
            DefineGotoCase(BeforeCloseBrace)
          }
          else if (type == OperatorPunctuatorToken::TOpenBracket) {
            DefineAddError("unsupported aggregated array construct");
            DefineGotoCase(BeforeCloseBrace)
          };
        }
        TermOrPredicate* subTerm = new TermOrPredicate;
        state.absorbRuleResult(subTerm);
        DefineShiftAndParse(AfterBraceTerm, *subTerm,
            &TermOrPredicate::readToken);
      };
    DefineParseCase(AfterBraceTerm)
      assert(_startLocation);
      { AbstractToken token = arguments.queryToken();
        if (token.getType() == AbstractToken::TKeyword) {
          if (((const KeywordToken&) token).getType() == KeywordToken::TWith) {
            logic_type ltype = NULL;
            term termNode = NULL;
            { Parser::State::RuleAccess::TCastFromRule<TermOrPredicate>
                subterm(state.getRuleResult());
              termNode = subterm->extractTerm(arguments, ltype);
              state.freeRuleResult();
            };
            if (!termNode) {
              DefineAddError("expecting a term in update expression");
              DefineReduceAndParse
            };
            WithConstruct* updateWith = new WithConstruct(ltype, termNode);
            state.absorbRuleResult(updateWith);
            DefineShift(Update, *updateWith, &WithConstruct::readToken);
          };
        };
        if (token.getType() == AbstractToken::TOperatorPunctuator) {
          OperatorPunctuatorToken::Type type
            = ((const OperatorPunctuatorToken&) token).getType();
          if (type == OperatorPunctuatorToken::TCloseBrace) {
            logic_type ltype = NULL;
            term termNode;
            { Parser::State::RuleAccess::TCastFromRule<TermOrPredicate>
                subterm(state.getRuleResult());
              termNode = subterm->extractTermOrSet(arguments, ltype);
              state.freeRuleResult();
            };
            if (!termNode) {
              DefineAddError("expecting a predicate and not tsets");
              arguments.extendLocationWithToken(_loc);
              DefineReduceAndParse
            };
            if (isSetType(ltype))
              DefineAddError("syntax error "
                  "(set of set is not yet implemented)");
            ltype = make_set_type(ltype);
            arguments.extendLocationWithToken(_startLocation);
            pushLastArgument(ltype, term_cons(term_node_TUnion(cons_container(
              termNode, NULL)), _startLocation, NULL), NULL);
            _startLocation = NULL;
            arguments.extendLocationWithToken(_loc);
            if (_doesStopTypeAmbiguity)
              DefineTReduce
            DefineGotoCase(AfterPrimary)
          }
          else if (type == OperatorPunctuatorToken::TBitOr) {
            // unimplemented: this case should not happen since the '|' is
            // the bit or of terms!
            // desambiguation comes from the binder rules
            logic_type ltype = NULL;
            term termNode;
            { Parser::State::RuleAccess::TCastFromRule<TermOrPredicate>
                subterm(state.getRuleResult());
              termNode = subterm->extractTerm(arguments, ltype);
              state.freeRuleResult();
            };
            if (!termNode) {
              DefineAddError("expecting term before '|' operator");
              DefineReduceAndParse
            };
            arguments.extendLocationWithToken(_startLocation);
            SetComprehension* comprehension
              = new SetComprehension(ltype, termNode);
            state.absorbRuleResult(comprehension);
            DefineShift(Comprehension, *comprehension,
                &SetComprehension::readToken);
          }
        }
      };
      DefineAddError("expecting '}' or '|' in the set construct");
      state.freeRuleResult();
      DefineGotoCase(BeforeCloseBrace);
    DefineParseCase(Update)
      assert(_startLocation);
      { AbstractToken token = arguments.queryToken();
        if (token.getType() == AbstractToken::TOperatorPunctuator
            && ((const OperatorPunctuatorToken&) token).getType()
                == OperatorPunctuatorToken::TCloseBrace) {
          Parser::State::RuleAccess::TCastFromRule<WithConstruct>
            updateWith(state.getRuleResult());
          logic_type ltype = NULL;
          term termNode = updateWith->extractResult(ltype, arguments);
          state.freeRuleResult();
          pushLastArgument(ltype, termNode, NULL);
          free_location(_startLocation);
          _startLocation = NULL;
          arguments.extendLocationWithToken(_loc);
          if (_doesStopTypeAmbiguity)
            DefineTReduce
          DefineGotoCase(AfterPrimary)
        };
      };
      DefineAddError("expecting '}' at the end of an update '{ term "
          "\\with update }' construct.")
      DefineGotoCase(Update)
    DefineParseCase(Comprehension)
      assert(_startLocation);
      { AbstractToken token = arguments.queryToken();
        if (token.getType() == AbstractToken::TOperatorPunctuator
            && ((const OperatorPunctuatorToken&) token).getType()
                == OperatorPunctuatorToken::TCloseBrace) {
          arguments.extendLocationWithToken(_startLocation);
          Parser::State::RuleAccess::TCastFromRule<SetComprehension>
            comprehension(state.getRuleResult());
          logic_type ltype = NULL;
          term set = comprehension->extractSet(ltype);
          set->loc = _startLocation;
          _startLocation = NULL;
          state.freeRuleResult();
          pushLastArgument(ltype, set, NULL);
          arguments.extendLocationWithToken(_loc);
          if (_doesStopTypeAmbiguity)
            DefineTReduce
          DefineGotoCase(AfterPrimary)
        };
      };
      DefineAddError("expecting '}' at the end of an update '{ term "
          "\\with update }' construct.")
      DefineGotoCase(Comprehension)
    DefineParseCase(Range)
      assert(_startLocation);
      { Parser::State::RuleAccess::TCastFromRule<Range>
          range(state.getRuleResult());
        logic_type ltype = NULL;
        extend_location_with(_loc, range->_loc);
        term set = range->extractSet(ltype, arguments);
        state.freeRuleResult();
        pushLastArgument(ltype, set, NULL);
      };
      free_location(_startLocation);
      _startLocation = NULL;
      if (_doesStopTypeAmbiguity)
        DefineReduceAndParse
      DefineGotoCaseAndParse(AfterPrimary)
    DefineParseCase(BeforeCloseBrace)
      assert(_startLocation);
      { AbstractToken token = arguments.queryToken();
        if (token.getType() == AbstractToken::TOperatorPunctuator
            && ((const OperatorPunctuatorToken&) token).getType()
                == OperatorPunctuatorToken::TCloseBrace) {
          arguments.extendLocationWithToken(_loc);
          if (_doesStopTypeAmbiguity)
            DefineTReduce
          DefineGotoCase(AfterPrimary)
        };
      }
      free_location(_startLocation);
      _startLocation = NULL;
      DefineGotoCase(BeforeCloseBrace)
    DefineParseCase(AfterPrimary)
      assert(!_startLocation);
      { AbstractToken token = arguments.queryToken();
#if defined(__clang__) || defined(__GNUC__)
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wswitch"
#endif
        if (token.getType() == AbstractToken::TOperatorPunctuator) {
          OperatorPunctuatorToken::Type type
            = ((const OperatorPunctuatorToken&) token).getType();
          if ((type >=  OperatorPunctuatorToken::TPlus
                && type <= OperatorPunctuatorToken::TLogicalOr)
              || (type >=  OperatorPunctuatorToken::TImplies
                && type <= OperatorPunctuatorToken::TBitEquiv)
              || type == OperatorPunctuatorToken::TLTColon
              || type == OperatorPunctuatorToken::TColonGT) {
            int binaryType = -1;
            int relationType = -1;
            switch (type) {
              case OperatorPunctuatorToken::TPlus:
                binaryType = Operator::TPlus; break;
              case OperatorPunctuatorToken::TMinus:
                binaryType = Operator::TMinus; break;
              case OperatorPunctuatorToken::TStar:
                binaryType = Operator::TTimes; break;
              case OperatorPunctuatorToken::TDivide:
                binaryType = Operator::TDivide; break;
              case OperatorPunctuatorToken::TProcent:
                binaryType = Operator::TModulo; break;
              case OperatorPunctuatorToken::TBitXor:
                binaryType = Operator::TBitXOr; break;
              case OperatorPunctuatorToken::TAmpersand:
                binaryType = Operator::TBitAnd; break;
              case OperatorPunctuatorToken::TBitOr:
                binaryType = Operator::TBitOr; break;
              case OperatorPunctuatorToken::TLess:
                relationType = Operator::TLess; break;
              case OperatorPunctuatorToken::TGreater:
                relationType = Operator::TGreater; break;
              case OperatorPunctuatorToken::TLeftShift:
                binaryType = Operator::TLeftShift; break;
              case OperatorPunctuatorToken::TRightShift:
                binaryType = Operator::TRightShift; break;
              case OperatorPunctuatorToken::TEqual:
                relationType = Operator::TEqual; break;
              case OperatorPunctuatorToken::TDifferent:
                relationType = Operator::TDifferent; break;
              case OperatorPunctuatorToken::TLessOrEqual:
                relationType = Operator::TLessOrEqual; break;
              case OperatorPunctuatorToken::TGreaterOrEqual:
                relationType = Operator::TGreaterOrEqual; break;
              case OperatorPunctuatorToken::TLogicalAnd:
                binaryType = Operator::TLogicalAnd; break;
              case OperatorPunctuatorToken::TLogicalOr:
                binaryType = Operator::TLogicalOr; break;
              case OperatorPunctuatorToken::TImplies:
                binaryType = Operator::TLogicalImply; break;
              case OperatorPunctuatorToken::TEquiv:
                binaryType = Operator::TLogicalEquiv; break;
              case OperatorPunctuatorToken::TLogicalXor:
                binaryType = Operator::TLogicalXOr; break;
              case OperatorPunctuatorToken::TBitImplies:
                binaryType = Operator::TBitImply; break;
              case OperatorPunctuatorToken::TBitEquiv:
                binaryType = Operator::TBitEquiv; break;
              case OperatorPunctuatorToken::TLTColon:
                binaryType = Operator::TSubType; break;
              case OperatorPunctuatorToken::TColonGT:
                binaryType = Operator::TCoerce; break;
            };
            if (relationType >= 0) {
              Operator* lastOperator = &_operatorStack.back();
              if (lastOperator->isValid()
                  && lastOperator->getLeftSubExpressions() == 0) {
                unsigned possibleSubtypeResult=getSubExpressionPossibleTypes();
                std::list<Operator>::reverse_iterator
                  lastComparison = _operatorStack.rbegin();
                int countPop = 0;
                while (lastComparison->getPrecedence() > Operator::PComparison
                    && lastOperator->getLeftSubExpressions() <= 1)
                { ++lastComparison;
                  ++countPop;
                  if (lastComparison == _operatorStack.rend())
                    break;
                };
                if (lastComparison->isRelation()) {
                  while (--countPop >= 0) {
                    logic_type ltype = NULL;
                    term expressionResult = NULL;
                    predicate_named predicateResult = NULL;
                    bool ok = apply(*lastOperator, ltype, expressionResult,
                        predicateResult, arguments, possibleSubtypeResult); 
                    if (!ok) {
                      if (arguments.doesStopAfterTooManyErrors())
                        return RRFinished;
                      DefineReduce
                    };
                    if (lastOperator->_startLocation) {
                      free_location(lastOperator->_startLocation);
                      lastOperator->_startLocation = NULL;
                    }
                    _operatorStack.pop_back();
                    lastOperator = &_operatorStack.back();
                    setLastArgument(*lastOperator, ltype,
                        expressionResult, predicateResult);
                  };
                  assert(lastOperator->isRelation());
                  lastOperator->_endRelationList.push_back(Operator::Relation
                        ((Operator::Type) relationType, NULL, NULL));
                  lastOperator->setLeftSubExpressions(1);
                  _doesRequireValue = true;
                  DefineGotoCase(Begin)
                };
              };
              binaryType = relationType;
            };
            if (binaryType >= 0) {
              bool hasFailed = false;
              pushBinaryOperator((Operator::Type) binaryType, arguments,
                  hasFailed);
              if (hasFailed) {
                if (arguments.doesStopAfterTooManyErrors())
                  return RRFinished;
                DefineReduce
              };
              if(_startLocation) {
                free(_startLocation);
                _startLocation = NULL;
              }
              DefineGotoCase(Begin)
            };
            assert(false);
          };

          switch (((const OperatorPunctuatorToken&) token).getType()) {
            case OperatorPunctuatorToken::TOpenBracket:
              { bool hasFailed = false;
                pushPostfixUnaryOperator(Operator::TArrayAccess, arguments,
                    hasFailed);
                if (hasFailed) {
                  if (arguments.doesStopAfterTooManyErrors())
                    return RRFinished;
                  DefineReduceAndParse
                };
                TermOrPredicate* subTerm = new TermOrPredicate;
                state.absorbRuleResult(&subTerm->setTerm());
                DefineShift(ArrayIndex, *subTerm, &TermOrPredicate::readToken)
              };
            case OperatorPunctuatorToken::TQuery:
              { bool hasFailed = false;
                pushConditionalOperator(arguments, hasFailed);
                if (hasFailed) {
                  if (arguments.doesStopAfterTooManyErrors())
                    return RRFinished;
                  DefineReduce
                };
                DefineGotoCase(Begin)
              }
            case OperatorPunctuatorToken::TColon:
              { Operator* lastOperator = &_operatorStack.back();
                if (lastOperator->isValid()
                    && lastOperator->getLeftSubExpressions() == 0) {
                  unsigned possibleSubtypeResult
                    = getSubExpressionPossibleTypes();
                  while (!_operatorStack.empty() && 
                      (lastOperator = &_operatorStack.back())->getPrecedence()
                        >= Operator::PConditional) {
                    logic_type ltype = NULL;
                    term expressionResult = NULL;
                    predicate_named predicateResult = NULL;
                    bool ok = apply(*lastOperator, ltype, expressionResult,
                        predicateResult, arguments, possibleSubtypeResult); 
                    if (!ok) {
                      if (arguments.doesStopAfterTooManyErrors())
                        return RRFinished;
                      DefineReduce
                    };
                    if (lastOperator->_startLocation) {
                      free_location(lastOperator->_startLocation);
                      lastOperator->_startLocation = NULL;
                    }
                    _operatorStack.pop_back();
                    lastOperator = &_operatorStack.back();
                    setLastArgument(*lastOperator, ltype,
                        expressionResult, predicateResult);
                    if (lastOperator->isValid()
                        && lastOperator->getLeftSubExpressions() == 0) {
                      lastOperator = NULL;
                      _operatorStack.pop_back();
                    }
                    else
                      break;
                  };
                };
                if (lastOperator && lastOperator->isValid()
                    && lastOperator->getType() == Operator::TConditional
                    && lastOperator->getLeftSubExpressions() == 1) {
                  _doesRequireValue = true;
                  DefineGotoCase(Begin)
                };
              }
              DefineAddError("at this point a conditional operation ?:"
                  " was expected");
              DefineReduceAndParse
            case OperatorPunctuatorToken::TPunct:
              { bool hasFailed = false;
                pushPostfixUnaryOperator(Operator::TStructAccess, arguments,
                    hasFailed);
                if (hasFailed) {
                  if (arguments.doesStopAfterTooManyErrors())
                    return RRFinished;
                  DefineReduceAndParse
                };
              };
              _operatorStack.back().setLeftSubExpressions(1);
              _operatorStack.back().changeLocation(copy_loc(
                    _operatorStack.back()._tfirstArgument->loc));
              DefineGotoCase(PointField)
            case OperatorPunctuatorToken::TPunctStar:
              { bool hasFailed = false;
                pushPostfixUnaryOperator(Operator::TIndirectMethodAccess,
                    arguments, hasFailed);
                if (hasFailed) {
                  if (arguments.doesStopAfterTooManyErrors())
                    return RRFinished;
                  DefineReduceAndParse
                };
                _operatorStack.back().setLeftSubExpressions(1);
                TermOrPredicate* subTerm = new TermOrPredicate;
                state.absorbRuleResult(&subTerm->setTerm());
                DefineShift(PointStar, *subTerm, &TermOrPredicate::readToken)
              };
            case OperatorPunctuatorToken::TArrowStar:
              { bool hasFailed = false;
                pushPostfixUnaryOperator(Operator::TArrowIndirectMethodAccess,
                    arguments, hasFailed);
                if (hasFailed) {
                  if (arguments.doesStopAfterTooManyErrors())
                    return RRFinished;
                  DefineReduceAndParse
                };
                _operatorStack.back().setLeftSubExpressions(1);
                TermOrPredicate* subTerm = new TermOrPredicate;
                state.absorbRuleResult(&subTerm->setTerm());
                DefineShift(PointStar, *subTerm, &TermOrPredicate::readToken)
              };
            case OperatorPunctuatorToken::TArrow:
              { bool hasFailed = false;
                pushPostfixUnaryOperator(Operator::TArrowStructAccess,
                    arguments, hasFailed);
                if (hasFailed) {
                  if (arguments.doesStopAfterTooManyErrors())
                    return RRFinished;
                  DefineReduceAndParse
                };
              };
              _operatorStack.back().setLeftSubExpressions(1);
              _operatorStack.back().changeLocation(
                copy_loc(_operatorStack.back()._tfirstArgument->loc));
              DefineGotoCase(PointField)
            case OperatorPunctuatorToken::TRange:
              { logic_type ltype = NULL;
                term node = extractTerm(arguments, ltype); // for range
                if (!node) {
                  DefineAddError("expecting a term before '..'");
                  DefineReduceAndParse
                };
                _startLocation = copy_loc(node->loc);
                Range* range = new Range(ltype, node);
                state.absorbRuleResult(range);
                DefineShift(Range, *range, &Range::readToken);
              };
          };
        };
#if defined(__clang__) || defined(__GNUC__)
#pragma GCC diagnostic pop
#endif
      };

      { // int intResult = 0; double doubleResult = 0;
        // bool isRValue = false;
        // bool isConstant = false;
        if (!clearStack(_typeResult, _node, _predicate /* , isRValue,
            isConstant, &intResult, &doubleResult*/, arguments))
          if (arguments.doesStopAfterTooManyErrors()) return RRFinished;
      };
      DefineReduceAndParse

    DefineParseCase(AfterLogicIdentifier)
      assert(_startLocation);
      { AbstractToken token = arguments.queryToken();
        if (token.getType() == AbstractToken::TOperatorPunctuator) {
          OperatorPunctuatorToken::Type type
            = ((const OperatorPunctuatorToken&) token).getType();
          if (type == OperatorPunctuatorToken::TOpenBrace) {
            // handle labels for calls => in logic_parser.mly,
            // but not in the grammar of terms and of predicates
            // in acsl-implementation.pdf
            if (!_qualification
                  || (!_qualification->isOverloadedLogicFunctions()
                && !_qualification->isLogicConstructor())) {
              std::string errorMessage = "unbound function ";
              errorMessage.append(_qualification->getName());
              DefineAddError(errorMessage)
            };
            excludeTypeAsResult();
            pushLastArgument(NULL, NULL, NULL /* , true, false */); 
            bool hasFailed = false;
            pushPostfixUnaryOperator(Operator::TCall, arguments, hasFailed);
            _operatorStack.back().setLeftSubExpressions(-1)
              .setIdentifier(_qualification);
            _operatorStack.back().changeLocation(_startLocation);
            _startLocation = NULL;
            if (hasFailed) {
              if (arguments.doesStopAfterTooManyErrors())
                return RRFinished;
              DefineReduceAndParse
            };
            DefineGotoCase(AfterLogicIdentifierLabel)
          }
          else if (type == OperatorPunctuatorToken::TOpenParen) {
            if (!_qualification
                  || (!_qualification->isOverloadedLogicFunctions()
                && !_qualification->isLogicConstructor())) {
              std::string errorMessage = "unbound function ";
              errorMessage.append(_qualification->getName());
              DefineAddError(errorMessage)
            };
            excludeTypeAsResult();
            _doesRequireValue = true; // pushLastArgument requires this, but it is not necessarily set until pushPostfixUnaryOperator
            pushLastArgument(NULL, NULL, NULL /* , true, false */);
            bool hasFailed = false;
            pushPostfixUnaryOperator(Operator::TCall, arguments, hasFailed);
            _operatorStack.back().setLeftSubExpressions(-1)
              .setIdentifier(_qualification);
            _operatorStack.back().changeLocation(_startLocation);
            _startLocation = NULL;
            if (hasFailed) {
              if (arguments.doesStopAfterTooManyErrors())
                return RRFinished;
              DefineReduceAndParse
            };
            DefineGotoCase(StartCall)
          }
          else if (type == OperatorPunctuatorToken::TColonColon) {
            if (_qualification && !_qualification->ssons()) {
              std::string errorMessage = "unknown logic qualification ";
              errorMessage.append(_qualification->getName());
              DefineAddError(errorMessage)
            };
            DefineGotoCase(AfterQualifiedLogicIdentifier)
          };
        };
        if (_qualification->isLogicVariable()) {
          excludeTypeAsResult();
          pushLastArgument(NULL, NULL, NULL /* , true, false */); 
          _operatorStack.back().setLeftSubExpressions(-1)
            .setIdentifier(_qualification);
          _operatorStack.back().setLocation(_startLocation);
          _startLocation = NULL;
        }
        else if (_qualification->isOverloadedLogicFunctions()) {
          excludeTypeAsResult();
          pushLastArgument(NULL, NULL, NULL /* , true, false */); 
          _operatorStack.back().setLeftSubExpressions(-1)
            .setIdentifier(_qualification);
          _operatorStack.back().setLocation(_startLocation);
          _startLocation = NULL;
        }
        else {
          std::string errorMessage = "unable to build a term/predicate "
            "from qualification ";
          errorMessage.append(_qualification->getName());
          free_location(_startLocation);
          _startLocation = NULL;
          DefineAddError(errorMessage)
        };
        arguments.extendLocationWithToken(_loc);
        if (_doesStopTypeAmbiguity)
          DefineTReduce
        DefineGotoCaseAndParse(AfterPrimary)
      };
    DefineParseCase(AfterLogicAndCContextIdentifier)
      assert(_startLocation);
      { AbstractToken token = arguments.queryToken();
        if (token.getType() == AbstractToken::TOperatorPunctuator) {
          OperatorPunctuatorToken::Type type
            = ((const OperatorPunctuatorToken&) token).getType();
          if (type == OperatorPunctuatorToken::TOpenBrace) {
            // handle labels for calls => in logic_parser.mly,
            // but not in the grammar of terms and of predicates
            // in acsl-implementation.pdf
            if (!_qualification
                  || (!_qualification->isOverloadedLogicFunctions()
                && !_qualification->isLogicConstructor())) {
              std::string errorMessage = "unbound function ";
              errorMessage.append(_qualification->getName());
              DefineAddError(errorMessage)
            };
            excludeTypeAsResult();
            pushLastArgument(NULL, NULL, NULL /* , true, false */); 
            bool hasFailed = false;
            pushPostfixUnaryOperator(Operator::TCall, arguments, hasFailed);
            _operatorStack.back().setLeftSubExpressions(-1)
              .setIdentifier(_qualification);
            _operatorStack.back().changeLocation(_startLocation);
            _startLocation = NULL;
            if (hasFailed) {
              if (arguments.doesStopAfterTooManyErrors())
                return RRFinished;
              DefineReduceAndParse
            };
            DefineGotoCase(AfterLogicIdentifierLabel)
          }
          else if (type == OperatorPunctuatorToken::TOpenParen) {
            if (!_qualification
                  || (!_qualification->isOverloadedLogicFunctions()
                && !_qualification->isLogicConstructor())) {
              std::string errorMessage = "unbound function ";
              errorMessage.append(_qualification->getName());
              DefineAddError(errorMessage)
            };
            excludeTypeAsResult();
            pushLastArgument(NULL, NULL, NULL /* , true, false */);
            bool hasFailed = false;
            pushPostfixUnaryOperator(Operator::TCall, arguments, hasFailed);
            _operatorStack.back().setLeftSubExpressions(-1)
              .setIdentifier(_qualification);
            _operatorStack.back().changeLocation(_startLocation);
            _startLocation = NULL;
            if (hasFailed) {
              if (arguments.doesStopAfterTooManyErrors())
                return RRFinished;
              DefineReduceAndParse
            };
            DefineGotoCase(StartCall)
          }
          else if (type == OperatorPunctuatorToken::TColonColon) {
            if (_qualification && !_qualification->ssons())
              DefineGotoCase(AfterQualifiedCContextIdentifier)
            DefineGotoCase(AfterQualifiedLogicAndCContextIdentifier)
          };
        };
        if (_qualification->isLogicVariable()) {
          excludeTypeAsResult();
          pushLastArgument(NULL, NULL, NULL /* , true, false */); 
          _operatorStack.back().setLeftSubExpressions(-1)
            .setIdentifier(_qualification);
          _operatorStack.back().setLocation(_startLocation);
          _startLocation = NULL;
        }
        else if (_qualification->isOverloadedLogicFunctions()) {
          excludeTypeAsResult();
          pushLastArgument(NULL, NULL, NULL /* , true, false */); 
          _operatorStack.back().setLeftSubExpressions(-1)
            .setIdentifier(_qualification);
          _operatorStack.back().setLocation(_startLocation);
          _startLocation = NULL;
        }
        else {
          const clang::RecordDecl* recordDecl
            = llvm::dyn_cast<clang::RecordDecl>(_declContext);
          if (recordDecl) {
            logic_type typeResult =
              arguments.get_clang_utils()->makeLogicType(
                arguments.tokenSourceLocation(),
                recordDecl->getTypeForDecl());
            LogicType* rule = new LogicType;
            rule->setType(typeResult, _startLocation);
            state.absorbRuleResult(rule);
            free_location(_startLocation);
            _startLocation = NULL;
            DefineShiftAndParseFrom(Type, 10
              /*LogicType::readToken::TypeSuffix*/, *rule,
              &LogicType::readToken);
          };

          std::string errorMessage = "unable to build a term/predicate "
            "from qualification ";
          errorMessage.append(_qualification->getName());
          free_location(_startLocation);
          _startLocation = NULL;
          DefineAddError(errorMessage)
        };
        arguments.extendLocationWithToken(_loc);
        if (_doesStopTypeAmbiguity)
          DefineTReduce
        DefineGotoCaseAndParse(AfterPrimary)
      };
    DefineParseCase(AfterQualifiedLogicIdentifier)
      assert(_startLocation);
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
          if (_qualification->isLogicType() && ensureTypeAsResult()) {
            arguments.extendLocationWithToken(_loc);
            logic_type_info ti = _qualification->asLogicType().type_info();
            logic_type typeResult =
              logic_type_Lnamed(
                qualified_name_dup(ti->type_name), ti->is_extern_c, NULL);
            LogicType* rule = new LogicType;
            rule->setType(typeResult, _startLocation);
            state.absorbRuleResult(rule);
            free_location(_startLocation);
            _startLocation = NULL;
            DefineShiftFrom(Type, 10 /* LogicType::readToken::TypeSuffix */,
                *rule, &LogicType::readToken);
          };
          if (acceptSubExpressionTerm()) {
            if (_qualification->isLogicVariable()) {
              excludeTypeAsResult();
              pushLastArgument(NULL, NULL, NULL /* , true, false */); 
              _operatorStack.back().setLeftSubExpressions(-1).setIdentifier(
                  _qualification);
              _operatorStack.back().setLocation(_startLocation);
              _startLocation = NULL;
              arguments.extendLocationWithToken(_loc);
              if (_doesStopTypeAmbiguity)
                DefineTReduce
              DefineGotoCase(AfterPrimary)
            }
            else if (_qualification->isOverloadedLogicFunctions()) {
              excludeTypeAsResult();
              pushLastArgument(NULL, NULL, NULL /* , true, false */); 
              _operatorStack.back().setLeftSubExpressions(-1).setIdentifier(
                  _qualification);
              _operatorStack.back().setLocation(_startLocation);
              _startLocation = NULL;
              arguments.extendLocationWithToken(_loc);
              if (_doesStopTypeAmbiguity)
                DefineTReduce
              DefineGotoCase(AfterPrimary)
            }
          };
        };
        arguments.extendLocationWithToken(_loc);
        DefineAddError(std::string("unknown identifier '").append(identifier)
            .append("'"));
        DefineTReduce
      };
      DefineAddError(std::string("expecting identifier after "
            "parsing a qualification '::'"));
      DefineTReduce
    DefineParseCase(AfterQualifiedLogicAndCContextIdentifier)
      assert(_startLocation);
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
          else if (_qualification->isLogicType() && ensureTypeAsResult()) {
            arguments.extendLocationWithToken(_loc);
            logic_type_info ti = _qualification->asLogicType().type_info();
            logic_type typeResult =
              logic_type_Lnamed(
                qualified_name_dup(ti->type_name),ti->is_extern_c,NULL);
            LogicType* rule = new LogicType;
            rule->setType(typeResult, _startLocation);
            state.absorbRuleResult(rule);
            _startLocation = NULL;
            DefineShiftFrom(Type, 10 /* LogicType::readToken::TypeSuffix */,
                *rule, &LogicType::readToken);
          }
          else if (acceptSubExpressionTerm()) {
            if (_qualification->isLogicVariable()) {
              excludeTypeAsResult();
              pushLastArgument(NULL, NULL, NULL /* , true, false */); 
              _operatorStack.back().setLeftSubExpressions(-1).setIdentifier(
                  _qualification);
              _operatorStack.back().setLocation(_startLocation);
              _startLocation = NULL;
              arguments.extendLocationWithToken(_loc);
              if (_doesStopTypeAmbiguity)
                DefineTReduce
              DefineGotoCase(AfterPrimary)
            }
            else if (_qualification->isOverloadedLogicFunctions()) {
              excludeTypeAsResult();
//              pushLastArgument(NULL, NULL, NULL /* , true, false */);
//              _operatorStack.back().setLeftSubExpressions(-1).setIdentifier(
//                  _qualification);
//              _operatorStack.back().setLocation(_startLocation);
//              _startLocation = NULL;
              arguments.extendLocationWithToken(_loc);
              if (_doesStopTypeAmbiguity)
                DefineTReduce
              DefineGotoCase(AfterLogicIdentifier)
            }
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
              DefineGotoCase(AfterLogicAndCContextIdentifier)
          };
          if (kind >= clang::Decl::firstType && kind <= clang::Decl::lastType) {
            if (ensureTypeAsResult()) {
              if (hasFoundLogicQualification)
                DefineGotoCase(AfterLogicIdentifier)
              logic_type typeResult =
                  from_c_named_type(cidentifier,arguments.get_clang_utils());
              arguments.extendLocationWithToken(_loc);
              LogicType* rule = new LogicType;
              rule->setType(typeResult, _startLocation);
              state.absorbRuleResult(rule);
              _startLocation = NULL;
              DefineShiftAndParseFrom(Type, 10
                  /* LogicType::readToken::TypeSuffix */,
                  *rule, &LogicType::readToken);
            };
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
                DefineGotoCase(AfterLogicAndCContextIdentifier)
            case clang::Decl::NamespaceAlias:
              assert(llvm::dyn_cast<clang::NamespaceAliasDecl>(cidentifier));
              _declContext = static_cast<const clang::NamespaceAliasDecl*>(
                  cidentifier)->getNamespace();
              if (!hasFoundLogicQualification)
                DefineGotoCase(AfterCContextIdentifier)
              else
                DefineGotoCase(AfterLogicAndCContextIdentifier)
            case clang::Decl::Var:
            case clang::Decl::ParmVar:
              if (hasFoundLogicQualification)
                DefineGotoCase(AfterLogicIdentifier)
              assert(llvm::dyn_cast<clang::VarDecl>(cidentifier));
              excludeTypeAsResult();
              { const clang::VarDecl* varDecl =
                 static_cast<const clang::VarDecl*>(cidentifier);
                logic_var var = logic_var_cons(arguments.get_clang_utils()
                    ->makeQualifiedName(*varDecl), LVCGLOBAL);
                pushLastArgument(
                  arguments.get_clang_utils()->makeLogicType(
                    arguments.tokenSourceLocation(),
                    varDecl->getType().getTypePtr()),
                  term_cons(term_node_TLval(term_lval_cons(
                    term_lhost_TVar(var), term_offset_TNoOffset())),
                    _startLocation, NULL), NULL /* , true, false */);
              };
              _startLocation = NULL;
              if (_doesStopTypeAmbiguity)
                DefineReduce
              DefineGotoCase(AfterPrimary)
            case clang::Decl::EnumConstant:
              if (hasFoundLogicQualification)
                DefineGotoCase(AfterLogicIdentifier)
              assert(llvm::dyn_cast<clang::EnumConstantDecl>(cidentifier));
              excludeTypeAsResult();
              { const clang::EnumConstantDecl* constantDecl
                  = static_cast<const clang::EnumConstantDecl*>(cidentifier);
                logic_constant constant = logic_constant_LCEnum((int64_t)
                  constantDecl->getInitVal().getLimitedValue(UINT64_MAX),
                  arguments.get_clang_utils()
                    ->makeQualifiedName(*constantDecl));
                arguments.extendLocationWithToken(_startLocation);
                assert(llvm::dyn_cast<clang::EnumType>(
                  constantDecl->getType().getTypePtr()));
                pushLastArgument(logic_type_Lenum(
                  arguments.get_clang_utils()->makeQualifiedName(
                    *((const clang::EnumType*) constantDecl->getType()
                      .getTypePtr())->getDecl())),
                  term_cons(term_node_TConst(constant),
                    _startLocation, NULL), NULL /* , true, false */); 
              };
              _startLocation = NULL;
              arguments.extendLocationWithToken(_loc);
              if (_doesStopTypeAmbiguity)
                DefineTReduce
              DefineGotoCase(AfterPrimary)
            default:
              break;
          };
        };
        if (hasFoundLogicQualification)
          DefineGotoCase(AfterLogicIdentifier)

        free_location(_startLocation);
        _startLocation = NULL;
        arguments.extendLocationWithToken(_loc);
        DefineAddError(std::string("unknown identifier '").append(identifier)
            .append("'"));
        DefineTReduce
      };
      free_location(_startLocation);
      _startLocation = NULL;
      DefineAddError(std::string("expecting identifier after "
            "parsing a qualification '::'"));
      DefineTReduce
    DefineParseCase(AfterCContextIdentifier)
      assert(_startLocation);
      { AbstractToken token = arguments.queryToken();
        if (token.getType() == AbstractToken::TOperatorPunctuator) {
          OperatorPunctuatorToken::Type type = ((const OperatorPunctuatorToken&)
              token).getType();
          if (type == OperatorPunctuatorToken::TColonColon)
            DefineGotoCase(AfterQualifiedCContextIdentifier)
        };
        const clang::RecordDecl* recordDecl = llvm::dyn_cast<clang::RecordDecl>(
            _declContext);
        if (recordDecl) {
          logic_type typeResult =
            arguments.get_clang_utils()->makeLogicType(
              arguments.tokenSourceLocation(),
              recordDecl->getTypeForDecl());
          LogicType* rule = new LogicType;
          rule->setType(typeResult, _startLocation);
          state.absorbRuleResult(rule);
          _startLocation = NULL;
          DefineShiftAndParseFrom(Type, 10 /*LogicType::readToken::TypeSuffix*/,
              *rule, &LogicType::readToken);
        };
        std::string errorMessage = "unable to build a C/C++ term/predicate "
          "from qualification ";
        errorMessage.append(_qualification->getName());
        arguments.extendLocationWithToken(_loc);
        DefineAddError(errorMessage)
        DefineGotoCase(AfterPrimary)
      };
    DefineParseCase(AfterQualifiedCContextIdentifier)
      assert(_startLocation);
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
            if (ensureTypeAsResult()) {
              logic_type typeResult =
                from_c_named_type(cidentifier,arguments.get_clang_utils());
              arguments.extendLocationWithToken(_loc);
              LogicType* rule = new LogicType;
              rule->setType(typeResult, _startLocation);
              state.absorbRuleResult(rule);
              _startLocation = NULL;
              DefineShiftAndParseFrom(Type, 10
                  /* LogicType::readToken::TypeSuffix */,
                  *rule, &LogicType::readToken);
            };
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
            case clang::Decl::Var:
          case clang::Decl::ParmVar: {
            assert(llvm::dyn_cast<clang::VarDecl>(cidentifier));
            excludeTypeAsResult();
            const clang::VarDecl* varDecl =
             static_cast<const clang::VarDecl*>(cidentifier);
            logic_var var =
             logic_var_cons(
              arguments.get_clang_utils()->makeQualifiedName(*varDecl),
              LVCGLOBAL);
            pushLastArgument(
             arguments.get_clang_utils()->makeLogicType(
               arguments.tokenSourceLocation(),
               varDecl->getType().getTypePtr()),
             term_cons(
              term_node_TLval(
                term_lval_cons(
                 term_lhost_TVar(var), term_offset_TNoOffset())),
              _startLocation, NULL), NULL /* , true, false */);
          };
          _startLocation = NULL;
            if (_doesStopTypeAmbiguity)
             DefineReduce
             DefineGotoCase(AfterPrimary)
          case clang::Decl::EnumConstant:
              assert(llvm::dyn_cast<clang::EnumConstantDecl>(cidentifier));
              excludeTypeAsResult();
              { const clang::EnumConstantDecl* constantDecl
                  = static_cast<const clang::EnumConstantDecl*>(cidentifier);
                logic_constant constant = logic_constant_LCEnum((int64_t)
                  constantDecl->getInitVal().getLimitedValue(UINT64_MAX),
                  arguments.get_clang_utils()
                    ->makeQualifiedName(*constantDecl));
                arguments.extendLocationWithToken(_startLocation);
                assert(llvm::dyn_cast<clang::EnumType>(
                  constantDecl->getType().getTypePtr()));
                pushLastArgument(logic_type_Lenum(
                  arguments.get_clang_utils()->makeQualifiedName(
                    *((const clang::EnumType*) constantDecl->getType()
                      .getTypePtr())->getDecl())),
                  term_cons(term_node_TConst(constant),
                    _startLocation, NULL), NULL /* , true, false */); 
              };
              _startLocation = NULL;
              arguments.extendLocationWithToken(_loc);
              if (_doesStopTypeAmbiguity)
                DefineTReduce
              DefineGotoCase(AfterPrimary)
            default:
              break;
          };
        };
        free_location(_startLocation);
        _startLocation = NULL;
        arguments.extendLocationWithToken(_loc);
        DefineAddError(std::string("unknown identifier '").append(identifier)
            .append("'"));
        DefineGotoCase(AfterPrimary)
      };
      free_location(_startLocation);
      _startLocation = NULL;
      DefineAddError(std::string("expecting idendifier "
          "after parsing a qualification '::'"));
      DefineGotoCase(AfterPrimary)
    DefineParseCase(BeforeLogicIdentifierLabel)
      { AbstractToken token = arguments.queryToken();
        if (token.getType() == AbstractToken::TOperatorPunctuator) {
          OperatorPunctuatorToken::Type type = ((const OperatorPunctuatorToken&)
              token).getType();
          if (type == OperatorPunctuatorToken::TCloseBrace) {
            arguments.extendLocationWithToken(_loc);
            DefineGotoCase(BeforeStartCall)
          }
          if (type == OperatorPunctuatorToken::TComma)
            { DefineGotoCase(AfterLogicIdentifierLabel) }
        };
        DefineAddError(std::string("expecting ',' or '}' "
            "in label arguments"));
        DefineGotoCaseAndParse(AfterLogicIdentifierLabel)
      };
    DefineParseCase(AfterLogicIdentifierLabel)
      { AbstractToken token = arguments.queryToken();
        if ((token.getType() == AbstractToken::TOperatorPunctuator)
          && ((const OperatorPunctuatorToken&) token).getType()
            == OperatorPunctuatorToken::TCloseBrace) {
          arguments.extendLocationWithToken(_loc);
          DefineGotoCase(BeforeStartCall)
        };
        if (token.getType() == AbstractToken::TIdentifier) {
          const std::string& identifier = ((const IdentifierToken&) arguments
              .getContentToken()).content();
          logic_label foundLabel = arguments.findLogicLabel(identifier);
          if (!foundLabel)
            DefineAddError("expecting a label argument");
          ForwardReferenceList labelsArguments(_operatorStack.back()
              ._labelsArguments);
          labelsArguments.insertContainer(foundLabel);
          DefineGotoCase(BeforeLogicIdentifierLabel)
        }
        DefineAddError(std::string("expecting idendifier in label arguments"));
        if ((token.getType() == AbstractToken::TOperatorPunctuator)
            && ((const OperatorPunctuatorToken&) token).getType()
                == OperatorPunctuatorToken::TSemiColon) {
          /* logic_label */ list labelsArguments = _operatorStack.back()
              ._labelsArguments;
          _operatorStack.back()._labelsArguments = NULL;
          while (labelsArguments) {
            free_logic_label((logic_label) labelsArguments->element.container);
            /* logic_label */ list temp = labelsArguments;
            labelsArguments = labelsArguments->next;
            free(temp);
          };
          DefineGotoCaseAndParse(AfterPrimary)
        }
        DefineGotoCase(AfterLogicIdentifierLabel)
      };
    DefineParseCase(BeforeStartCall)
      { AbstractToken token = arguments.queryToken();
        if ((token.getType() == AbstractToken::TOperatorPunctuator)
            && ((const OperatorPunctuatorToken&) token).getType()
                == OperatorPunctuatorToken::TOpenParen)
          { DefineGotoCase(StartCall) }
        /* logic_label */ list labelsArguments = _operatorStack.back()
            ._labelsArguments;
        _operatorStack.back()._labelsArguments = NULL;
        while (labelsArguments) {
          free_logic_label((logic_label) labelsArguments->element.container);
          /* logic_label */ list temp = labelsArguments;
          labelsArguments = labelsArguments->next;
          free(temp);
        };
        _operatorStack.pop_back();
        DefineGotoCaseAndParse(AfterLogicIdentifier)
      };
    DefineParseCase(StartCall)
      { AbstractToken token = arguments.queryToken();
        if ((token.getType() == AbstractToken::TOperatorPunctuator)
          && ((const OperatorPunctuatorToken&) token).getType()
            == OperatorPunctuatorToken::TCloseParen) {
          _operatorStack.back().setLeftSubExpressions(0);
          arguments.extendLocationWithToken(_loc);
          _doesRequireValue=false;
          if (_doesStopTypeAmbiguity)
            DefineTReduce
          DefineGotoCase(AfterPrimary)
        };
        TermOrPredicate* subTerm = new TermOrPredicate;
        state.absorbRuleResult(subTerm);
        subTerm->_possibleTypeResults = (1U << LTRTerm);
        DefineShiftAndParse(CallArgument, *subTerm,
            &TermOrPredicate::readToken);
      };
    DefineParseCase(CallArgument)
    DefineParseCase(ArrayIndex)
        //assert(!_startLocation);
      { logic_type ltype = NULL;
        term termNode;
        { Parser::State::RuleAccess::TCastFromRule<TermOrPredicate>
            subterm(state.getRuleResult());
          termNode = subterm->extractTermOrSet(arguments, ltype);
          state.freeRuleResult();
        };
        if (!(!_operatorStack.empty() && ltype && termNode)) {
          DefineAddError("expecting a term before ']' or ')'");
          DefineReduceAndParse
        };
        _operatorStack.back().addArgument(ltype, termNode);

        AbstractToken token = arguments.queryToken();
        if (token.getType() == AbstractToken::TOperatorPunctuator) {
          if (((const OperatorPunctuatorToken&) token).getType()
              == OperatorPunctuatorToken::TCloseParen) {
            if (state.point() == DCallArgument) {
              _operatorStack.back().setLeftSubExpressions(0);
              arguments.extendLocationWithToken(_loc);
              _doesRequireValue=false;
              if (_doesStopTypeAmbiguity)
                DefineTReduce
              DefineGotoCase(AfterPrimary)
            };
          }
          else if (((const OperatorPunctuatorToken&) token).getType()
              == OperatorPunctuatorToken::TCloseBracket) {
            if (state.point() == DArrayIndex) {
              _operatorStack.back().setLeftSubExpressions(0);
              arguments.extendLocationWithToken(_loc);
              _doesRequireValue=false;
              if (_doesStopTypeAmbiguity)
                DefineTReduce                  
              DefineGotoCase(AfterPrimary)
            };
          }
          else if (((const OperatorPunctuatorToken&) token).getType()
              == OperatorPunctuatorToken::TComma) {
            TermOrPredicate* subTerm = new TermOrPredicate;
            state.absorbRuleResult(&subTerm->setTerm());
            DefineShift(CallArgument, *subTerm,
                &TermOrPredicate::readToken);
          };
        };
        std::ostringstream outToken;
        arguments.lexer().assumeContentToken();
        arguments.getContentToken().write(outToken,
            AbstractToken::PersistentFormat().setPretty());
        DefineAddError(std::string("unexpected token '")
            .append(outToken.str())
            .append("' when starting to parse a term"));
        DefineTReduce
      };

    DefineParseCase(PointField)
      assert(!_startLocation);
      if (arguments.queryToken().getType() == AbstractToken::TIdentifier) {
        const std::string& identifier = ((const IdentifierToken&)
            arguments.getContentToken()).content();
        assert(!_operatorStack.empty());
        _operatorStack.back().setLeftSubExpressions(0).setField(identifier);
        _doesRequireValue = false;
        arguments.extendLocationWithToken(_loc);
        if (_doesStopTypeAmbiguity)
          DefineTReduce
        DefineGotoCase(AfterPoint)
      };
      { std::ostringstream outToken;
        arguments.lexer().assumeContentToken();
        arguments.getContentToken().write(outToken,
            AbstractToken::PersistentFormat().setPretty());
        DefineAddError(std::string("unexpected token '")
            .append(outToken.str())
            .append("' when starting to parse a field after a term"));
        DefineTReduce
      };
    DefineParseCase(PointStar)
      assert(!_startLocation);
      { // int intResult = 0; double doubleResult = 0;
        logic_type ltype = NULL;
        term termNode = NULL;
        predicate_named predicateNode = NULL;
        // bool isRValue = false;
        { Parser::State::RuleAccess::TCastFromRule<TermOrPredicate>
            subterm(state.getRuleResult());
          // bool isConstant = false;
          subterm->extractTermOrPredicate(arguments, ltype, termNode,
              predicateNode);
          extend_location_with(_loc, subterm->_loc);
          state.freeRuleResult();
          if (!(termNode || predicateNode)) {
            if (arguments.doesStopAfterTooManyErrors())
              return RRFinished;
            DefineReduceAndParse
          };
        };
        // if (!isRValue) {
        //   // term_lval_cons ...
        //   // term_node = term_node_TLval(lval)
        // };
        pushLastArgument(ltype, termNode, predicateNode /* , isRValue, false,
            int* intArgument=NULL, double* doubleArgument=NULL*/);
        _operatorStack.back().setLeftSubExpressions(0);
        _doesRequireValue = false;
        if (_doesStopTypeAmbiguity)
          DefineReduceAndParse
        DefineGotoCaseAndParse(AfterPoint)
      };
    DefineParseCase(AfterPoint)
      { AbstractToken token = arguments.queryToken();
        if (token.getType() == AbstractToken::TOperatorPunctuator) {
          if (((const OperatorPunctuatorToken&) token).getType()
              == OperatorPunctuatorToken::TOpenParen) {
            if (!_operatorStack.back().changeTypeToCallAccess(arguments))
            { DefineAddError("the object type is not a struct type!");
              DefineReduceAndParse
            }
            DefineGotoCase(StartCall)
          };
        };
      }
      DefineGotoCaseAndParse(AfterPrimary)
    DefineParseCase(Binders)
      assert(!_startLocation);
      { AbstractToken token = arguments.queryToken();
        if (token.getType() == AbstractToken::TOperatorPunctuator) {
          if (((const OperatorPunctuatorToken&) token).getType()
              == OperatorPunctuatorToken::TSemiColon) {
            Parser::State::RuleAccess::TCastFromRule<Binders>
              binders(state.getRuleResult());
            /* logic_var_def */ list binderIter;
            _operatorStack.back().setBinders(binderIter
                = binders->extractResult());
            while (binderIter != NULL) {
              logic_var_def def = (logic_var_def) binderIter->element.container;
              arguments.addLocalBinding(def->lv_name->decl_name,
                  logic_var_def_dup(def));
              binderIter = binderIter->next;
            };
            state.freeRuleResult();
            DefineGotoCase(Begin)
          };
        };
        { std::ostringstream outToken;
          arguments.lexer().assumeContentToken();
          arguments.getContentToken().write(outToken,
              AbstractToken::PersistentFormat().setPretty());
          DefineAddError(std::string("unexpected token '")
              .append(outToken.str())
              .append("' after a binders construct"));
        };
      };
      DefineGotoCase(Binders)
    DefineParseCase(Let)
      assert(!_startLocation);
      if (arguments.queryToken().getType() == AbstractToken::TIdentifier) {
        const std::string& identifier = ((const IdentifierToken&)
            arguments.getContentToken()).content();
        assert(!_operatorStack.empty());
        _operatorStack.back().setLeftSubExpressions(1).setField(identifier);
        TermOrPredicate* subTerm = new TermOrPredicate;
        state.absorbRuleResult(subTerm);
        subTerm->_possibleTypeResults = (1U << LTRTerm);
        DefineShift(LetAssignment, *subTerm, &TermOrPredicate::readToken)
      };
      { std::ostringstream outToken;
        arguments.lexer().assumeContentToken();
        arguments.getContentToken().write(outToken,
            AbstractToken::PersistentFormat().setPretty());
        DefineAddError(std::string("unexpected token '")
            .append(outToken.str())
            .append("' for a let construct"));
        DefineGotoCase(Let)
      };
    DefineParseCase(LetAssignment)
      assert(!_startLocation);
      { AbstractToken token = arguments.queryToken();
        if (token.getType() == AbstractToken::TOperatorPunctuator) {
          if (((const OperatorPunctuatorToken&) token).getType()
              == OperatorPunctuatorToken::TSemiColon) {
            // int intResult = 0; double doubleResult = 0;
            logic_type ltype = NULL;
            term termNode = NULL;
            predicate_named predicateNode = NULL;
            // bool isRValue = false;
            { Parser::State::RuleAccess::TCastFromRule<TermOrPredicate>
                subterm(state.getRuleResult());
              // bool isConstant = false;
              subterm->extractTermOrPredicate(arguments, ltype, termNode,
                  predicateNode);
              state.freeRuleResult();
              if (!(termNode || predicateNode)) {
                if (arguments.doesStopAfterTooManyErrors())
                  return RRFinished;
                DefineReduceAndParse
              };
            };
            // if (!isRValue) {
            //   // term_lval_cons ...
            //   // term_node = term_node_TLval(lval)
            // };
            pushLastArgument(ltype, termNode, predicateNode /* , isRValue,
              false, int* intArgument=NULL, double* doubleArgument=NULL*/);
            _operatorStack.back().setLeftSubExpressions(1);
            DefineGotoCase(Begin)
          };
        };
      };
      { std::ostringstream outToken;
        arguments.lexer().assumeContentToken();
        arguments.getContentToken().write(outToken,
            AbstractToken::PersistentFormat().setPretty());
        DefineAddError(std::string("unexpected token '")
            .append(outToken.str())
            .append("' for a let construct after assignment"));
      };
      DefineGotoCase(LetAssignment)
    DefineParseCase(Type)
      assert(!_startLocation);
      { Parser::State::RuleAccess::TCastFromRule<LogicType>
          rule(state.getRuleResult());
        _typeResult = rule->extractType();
        location loc = rule->extractLocation();
        extend_location_with(_loc, loc);
        free_location(loc);
        arguments.extendLocationWithToken(_loc);
        state.freeRuleResult();
      };
      DefineReduceAndParse
    DefineParseCase(SizeOf)
      assert(_startLocation);
      { AbstractToken token = arguments.queryToken();
        if (token.getType() == AbstractToken::TOperatorPunctuator
            && (((const OperatorPunctuatorToken&) token).getType()
              == OperatorPunctuatorToken::TOpenParen)) {
          TermOrPredicate* subTerm = new TermOrPredicate;
          state.absorbRuleResult(subTerm);
          subTerm->_possibleTypeResults = ((1U << LTRTerm) | (1U << LTRType));
          DefineShift(EndSizeOf, *subTerm, &TermOrPredicate::readToken);
        }
      };
      DefineGotoCaseAndParse(EndSizeOf)
    DefineParseCase(EndSizeOf)
      assert(_startLocation);
      { AbstractToken token = arguments.queryToken();
        Parser::State::RuleAccess::TCastFromRule<TermOrPredicate>
          subterm(state.getRuleResult());
        if (subterm->isType()) {
          if (token.getType() == AbstractToken::TOperatorPunctuator) {
            if (((const OperatorPunctuatorToken&) token).getType()
                == OperatorPunctuatorToken::TCloseParen) {
              arguments.extendLocationWithToken(_startLocation);
              term node = term_cons(term_node_TSizeOf(
                    subterm->_typeResult), _startLocation, NULL);
              _startLocation = NULL;
              subterm->_typeResult = NULL;
              state.freeRuleResult();
              pushLastArgument(logic_type_Linteger(), node, NULL);
              arguments.extendLocationWithToken(_loc);
              if (_doesStopTypeAmbiguity)
                DefineTReduce
              DefineGotoCase(AfterPrimary)
            };
          };
          DefineAddError("expecting token ')' at the end of sizeof(type)");
          DefineGotoCase(EndSizeOf)
        };

        if (token.getType() == AbstractToken::TOperatorPunctuator) {
          if (((const OperatorPunctuatorToken&) token).getType()
              == OperatorPunctuatorToken::TCloseParen) {
            logic_type ltype = NULL;
            term termNode = subterm->extractTermOrSet(arguments, ltype);
            state.freeRuleResult();
            if (!termNode) {
              DefineAddError("expecting a term before ')'");
              DefineReduceAndParse
            };
            term node;
            arguments.extendLocationWithToken(_startLocation);
            if ((termNode->node->tag_term_node == TCONST)
              && (termNode->node->cons_term_node.TConst.value
                  ->tag_logic_constant == LSTR
                || termNode->node->cons_term_node.TConst.value
                    ->tag_logic_constant == LWSTR)) {
              assert(termNode->node->cons_term_node.TConst.value
                  ->tag_logic_constant == LSTR); // unimplemented
              node = term_cons(term_node_TSizeOfStr(
                  strdup(termNode->node->cons_term_node.TConst.value
                    ->cons_logic_constant.LStr.value)), _startLocation, NULL);
              free_logic_type(ltype);
            }
            else
              node = term_cons(term_node_TSizeOf(ltype), _startLocation, NULL);
            _startLocation = NULL;
            ltype = NULL;
            if (termNode)
              free_term(termNode);
            pushLastArgument(logic_type_Linteger(), node, NULL);
            arguments.extendLocationWithToken(_loc);
            if (_doesStopTypeAmbiguity)
              DefineTReduce
            DefineGotoCase(AfterPrimary)
          };
        };
      };
      DefineAddError("expecting token ')' at the end of sizeof(term)");
      DefineGotoCase(EndSizeOf)

    DefineParseCase(BaseAddrLabel)
    DefineParseCase(BlockLengthLabel)
    DefineParseCase(OffsetLabel)
    DefineParseCase(AllocationLabel)
    DefineParseCase(AllocableLabel)
    DefineParseCase(FreeableLabel)
    DefineParseCase(FreshLabel)
    DefineParseCase(InitializedLabel)
    DefineParseCase(DanglingLabel)
    DefineParseCase(ValidLabel)
    DefineParseCase(ValidReadLabel)
    DefineParseCase(ValidIndexLabel)
    DefineParseCase(ValidRangeLabel)
    DefineParseCase(Separated)
      assert(_startLocation);
      { AbstractToken token = arguments.queryToken();
        if (token.getType() == AbstractToken::TOperatorPunctuator) {
          OperatorPunctuatorToken::Type type = ((const OperatorPunctuatorToken&)
              token).getType();
          int point = state.point();
          if (type == OperatorPunctuatorToken::TOpenBrace
              && point != DSeparated) {
            state.absorbRuleResult(new TermOrPredicateMemoryExtension);
            DefineGotoCaseWithIncrement(DBaseAddrInLabel - DBaseAddrLabel,
                LInLabel);
          }
          else if (type == OperatorPunctuatorToken::TOpenParen) {
            TermOrPredicateMemoryExtension* subTerm
                = new TermOrPredicateMemoryExtension;
            state.absorbRuleResult(subTerm);
            if (point >= DBaseAddrLabel && point <= DFreshLabel) {
              DefineShiftWithIncrement(DBaseAddrTerm - DBaseAddrLabel,
                  LTermMemory, (TermOrPredicate&) *subTerm,
                  &TermOrPredicate::readToken);
            }
            else // point >= DInitializedLabel && point <= DSeparated
              DefineShiftWithIncrement(
                DValidLocation - DValidLabel,
                LLocationMemory, (TermOrPredicate&)*subTerm,
                &TermOrPredicate::readToken);
          }
        };
      };
      DefineAddError("expecting token '{' or '(' "
          "after a memory related keyword");
      DefineReduceAndParse
    DefineParseCase(ValidFunctionLabel)
        assert(_startLocation);
        { AbstractToken token = arguments.queryToken();
          if (token.getType() == AbstractToken::TOperatorPunctuator) {
            OperatorPunctuatorToken::Type type = ((const OperatorPunctuatorToken&)
                token).getType();
            int point = state.point();
            if (type == OperatorPunctuatorToken::TOpenBrace) {
              DefineAddError("\\valid_function does not take a label argument");
            }
            else if (type == OperatorPunctuatorToken::TOpenParen) {
              TermOrPredicateMemoryExtension* subTerm
                  = new TermOrPredicateMemoryExtension;
              state.absorbRuleResult(subTerm);
              if (point >= DBaseAddrLabel && point <= DFreshLabel) {
                DefineShiftWithIncrement(DBaseAddrTerm - DBaseAddrLabel,
                    LTermMemory, (TermOrPredicate&) *subTerm,
                    &TermOrPredicate::readToken);
              }
              else // point >= DInitializedLabel && point <= DSeparated
                DefineShiftWithIncrement(
                  DValidLocation - DValidLabel,
                  LLocationMemory, (TermOrPredicate&)*subTerm,
                  &TermOrPredicate::readToken);
            } else {
              DefineAddError("expecting token '{' or '(' "
                  "after a memory related keyword");
            }
          };
        };
        DefineReduceAndParse
    case DBaseAddrInLabel:
    case DBlockLengthInLabel:
    case DOffsetInLabel:
    case DAllocationInLabel:
    case DAllocableInLabel:
    case DFreeableInLabel:
    case DFreshInLabel:
    case DInitializedInLabel:
    case DDanglingInLabel:
    case DValidInLabel:
    case DValidReadInLabel:
    case DValidFunctionInLabel:
    case DValidIndexInLabel:
    case DValidRangeInLabel:
LInLabel:
      assert(_startLocation);
      if (arguments.queryToken().getType() == AbstractToken::TIdentifier) {
        const std::string& identifier = ((const IdentifierToken&)
            arguments.getContentToken()).content();
        Parser::State::RuleAccess::TCastFromRule<TermOrPredicateMemoryExtension>
            memory(state.getRuleResult());
        logic_label foundLabel = arguments.findLogicLabel(identifier);
        if (!foundLabel)
          DefineAddError("expecting a label in the memory construct");
        memory->addLabel(foundLabel);
        DefineGotoCaseWithIncrement(DBaseAddrEndLabel - DBaseAddrInLabel,
            LEndLabel);
      };
      DefineAddError("expecting identifier in labels of a memory construct");
      DefineGotoCaseWithIncrement(0, LInLabel);
    case DBaseAddrEndLabel:
    case DBlockLengthEndLabel:
    case DOffsetEndLabel:
    case DAllocationEndLabel:
    case DAllocableEndLabel:
    case DFreeableEndLabel:
    case DFreshEndLabel:
    case DInitializedEndLabel:
    case DDanglingEndLabel:
    case DValidEndLabel:
    case DValidReadEndLabel:
    case DValidFunctionEndLabel:
    case DValidIndexEndLabel:
    case DValidRangeEndLabel:
LEndLabel:
      assert(_startLocation);
      { AbstractToken token = arguments.queryToken();
        if (token.getType() == AbstractToken::TOperatorPunctuator) {
          OperatorPunctuatorToken::Type type = ((const OperatorPunctuatorToken&)
              token).getType();
          if (state.point() == DFreshEndLabel) {
            Parser::State::RuleAccess::TCastFromRule<
              TermOrPredicateMemoryExtension> memory(state.getRuleResult());
            if (!(memory->hasSecondLabel()
                ? (type == OperatorPunctuatorToken::TCloseBrace)
                : (type == OperatorPunctuatorToken::TComma))) {
              if (type == OperatorPunctuatorToken::TCloseBrace) {
                DefineAddError("expecting a second label "
                    "for the \\fresh construct");
                DefineGotoCaseWithIncrement(DBeforeFreshTerm - DFreshEndLabel,
                    LBeforeTermOrLocationMemory);
              }
              else {
                DefineAddError("only two labels are necessary "
                    "for the \\fresh construct");
                DefineGotoCaseWithIncrement(DFreshInLabel - DFreshEndLabel,
                    LInLabel);
              };
            };
          }
          else if (type == OperatorPunctuatorToken::TComma) {
            DefineAddError("only one label is necessary "
                "for the memory construct");
            DefineGotoCaseWithIncrement(DBaseAddrInLabel - DBaseAddrEndLabel,
                LInLabel);
          };
          if (type == OperatorPunctuatorToken::TCloseBrace)
            DefineGotoCaseWithIncrement(DBeforeBaseAddrTerm - DBaseAddrEndLabel,
                LBeforeTermOrLocationMemory)
          else if (type == OperatorPunctuatorToken::TComma)
            DefineGotoCaseWithIncrement(DBaseAddrInLabel - DBaseAddrEndLabel,
                LInLabel)
        };
      };
      DefineAddError("expecting identifier in labels of a memory construct");
      DefineGotoCaseWithIncrement(0, LEndLabel);
    case DBeforeBaseAddrTerm:
    case DBeforeBlockLengthTerm:
    case DBeforeOffsetTerm:
    case DBeforeAllocationTerm:
    case DBeforeAllocableTerm:
    case DBeforeFreeableTerm:
    case DBeforeFreshTerm:
    case DBeforeInitializedLocation:
    case DBeforeDanglingLocation:
    case DBeforeValidLocation:
    case DBeforeValidReadLocation:
    case DBeforeValidFunctionLocation:
    case DBeforeValidIndexLocation:
    case DBeforeValidRangeLocation:
LBeforeTermOrLocationMemory:
      assert(_startLocation);
      { AbstractToken token = arguments.queryToken();
        if (token.getType() == AbstractToken::TOperatorPunctuator) {
          if (((const OperatorPunctuatorToken&) token).getType()
              == OperatorPunctuatorToken::TOpenParen) {
            Parser::State::RuleAccess::TCastFromRule<
              TermOrPredicateMemoryExtension> memory(state.getRuleResult());
            if (state.point() <= DBeforeFreshTerm) {
              memory->setTerm();
              DefineShiftWithIncrement(DBaseAddrTerm - DBeforeBaseAddrTerm,
                  LTermMemory, (TermOrPredicate&) *memory,
                  &TermOrPredicate::readToken);
            }
            else {
              memory->setSet();
              DefineShiftWithIncrement(DInitializedLocation -
                  DBeforeInitializedLocation, LLocationMemory,
                  (TermOrPredicate&) *memory, &TermOrPredicate::readToken);
            };
          };
        };
      };
      DefineAddError("expecting '(' in a memory construct");
      state.freeRuleResult();
      free_location(_startLocation);
      _startLocation = NULL;
      DefineGotoCaseAndParse(AfterPrimary);
    case DBaseAddrTerm:
    case DBlockLengthTerm:
    case DOffsetTerm:
    case DAllocationTerm:
    case DAllocableTerm:
    case DFreeableTerm:
    case DFreshTerm:
LTermMemory:
      assert(_startLocation);
      { AbstractToken token = arguments.queryToken();
        if (token.getType() == AbstractToken::TOperatorPunctuator) {
          if (((const OperatorPunctuatorToken&) token).getType()
              == OperatorPunctuatorToken::TCloseParen) {
            arguments.extendLocationWithToken(_startLocation);
            Parser::State::RuleAccess::TCastFromRule<
              TermOrPredicateMemoryExtension> memory(state.getRuleResult());
            logic_type ltype = NULL;
            term node = memory->extractTermOrSet(arguments, ltype);
            if (!node) {
              DefineAddError("expecting a term before ')'");
              DefineReduceAndParse
            };
            if (state.point() == DFreshTerm) {
              if (!memory->hasSecondNode()) {
                if (node) free_term(node);
                if (ltype) free_logic_type(ltype);
                state.freeRuleResult();
                arguments.extendLocationWithToken(_loc);
                free_location(_startLocation);
                _startLocation = NULL;
                DefineAddError("expecting a second term "
                    "for the \\fresh construct");
                DefineGotoCase(AfterPrimary)
              };
            };
            assert(node && ltype);
            switch (state.point()) {
              case DBaseAddrTerm:
                if (isPointerType(ltype, Substitution(), arguments) ||
                    (isArrayType(ltype, Substitution(), arguments) &&
                     isCArray(node,ltype,arguments))) {
                  if (isCArray(node,ltype,arguments))
                    node = makeLogicStartOf(node, arguments);
                  pushLastArgument(logic_type_Lpointer(logic_type_Lint(ICHAR)),
                    term_cons(term_node_TBase_addr(memory->extractLabelOption(),
                        node), _startLocation, NULL), NULL);
                  _startLocation = NULL;
                }
                else {
                  if (node) free_term(node);
                  free_location(_startLocation);
                  _startLocation = NULL;
                  DefineAddError("expecting a pointer term "
                      "for the \\base_addr construct");
                };
                free_logic_type(ltype);
                state.freeRuleResult();
                arguments.extendLocationWithToken(_loc);
                if (_doesStopTypeAmbiguity)
                  DefineTReduce
                DefineGotoCase(AfterPrimary)
                break;
              case DBlockLengthTerm:
                if (isPointerType(ltype, Substitution(), arguments) ||
                    (isArrayType(ltype, Substitution(), arguments) &&
                     isCArray(node,ltype,arguments))) {
                  if (isCArray(node,ltype,arguments))
		      node = makeLogicStartOf(node, arguments);
                  pushLastArgument(logic_type_Linteger(), term_cons(
                    term_node_TBlock_length(memory->extractLabelOption(), node),
                    _startLocation, NULL), NULL);
                  _startLocation = NULL;
                }
                else {
                  if (node) free_term(node);
                  free_location(_startLocation);
                  _startLocation = NULL;
                  DefineAddError("expecting a pointer term "
                      "for the \\block_length construct");
                };
                free_logic_type(ltype);
                state.freeRuleResult();
                arguments.extendLocationWithToken(_loc);
                if (_doesStopTypeAmbiguity)
                  DefineTReduce
                DefineGotoCase(AfterPrimary)
                break;
              case DOffsetTerm:
                if (isPointerType(ltype, Substitution(), arguments) ||
                    (isArrayType(ltype, Substitution(), arguments) &&
                     isCArray(node,ltype,arguments))) {
                  if (isCArray(node,ltype,arguments))
		      node = makeLogicStartOf(node, arguments);
                  pushLastArgument(logic_type_Linteger(), term_cons(
                      term_node_TOffset(memory->extractLabelOption(), node),
                      _startLocation, NULL), NULL);
                  _startLocation = NULL;
                }
                else {
                  if (node) free_term(node);
                  free_location(_startLocation);
                  _startLocation = NULL;
                  DefineAddError("expecting a pointer term "
                      "for the \\offset construct");
                };
                free_logic_type(ltype);
                state.freeRuleResult();
                arguments.extendLocationWithToken(_loc);
                if (_doesStopTypeAmbiguity)
                  DefineTReduce
                DefineGotoCase(AfterPrimary)
                break;
              case DAllocationTerm:
                free_term(node);
                free_logic_type(ltype);
                assert(false); // unimplemented
              case DAllocableTerm:
                if (isPointerType(ltype, Substitution(), arguments) ||
                    (isArrayType(ltype, Substitution(), arguments) && 
                     isCArray(node,ltype,arguments))) {
                  if (isCArray(node,ltype,arguments))
		      node = makeLogicStartOf(node, arguments);
                  pushLastArgument(NULL, NULL,
                    predicate_named_cons(NULL, _startLocation,
                      predicate_Pallocable(memory->extractLabelOption(),
                          node)));
                  _startLocation = NULL;
                }
                else {
                  if (node) free_term(node);
                  free_location(_startLocation);
                  _startLocation = NULL;
                  DefineAddError("expecting a pointer term "
                      "for the \\allocable construct");
                };
                free_logic_type(ltype);
                state.freeRuleResult();
                arguments.extendLocationWithToken(_loc);
                if (_doesStopTypeAmbiguity)
                  DefineTReduce
                DefineGotoCase(AfterPrimary)
              case DFreeableTerm:
                if (isPointerType(ltype, Substitution(), arguments) ||
                    (isArrayType(ltype, Substitution(), arguments) &&
                     isCArray(node,ltype,arguments))) {
                  if (isCArray(node,ltype,arguments))
		      node = makeLogicStartOf(node, arguments);
                  pushLastArgument(NULL, NULL,
                    predicate_named_cons(NULL, _startLocation,
                      predicate_Pfreeable(memory->extractLabelOption(), node)));
                  _startLocation = NULL;
                }
                else {
                  if (node) free_term(node);
                  free_location(_startLocation);
                  _startLocation = NULL;
                  DefineAddError("expecting a pointer term "
                      "for the \\freeable construct");
                };
                free_logic_type(ltype);
                state.freeRuleResult();
                arguments.extendLocationWithToken(_loc);
                if (_doesStopTypeAmbiguity)
                  DefineTReduce
                DefineGotoCase(AfterPrimary)
              case DFreshTerm:
                if (!memory->hasLabel()) {
                  memory->addLabel(arguments.findLogicLabel("Old"));
                  memory->addLabel(arguments.findLogicLabel("Here"));
                }
                if (!memory->hasSecondLabel()) {
                  DefineAddError("\\fresh requires two labels")
                }
                if (logic_label_equal(memory->firstLabel(),
                      memory->secondLabel()))
                  DefineAddError("\\fresh requires two different labels");
                logic_type secondLtype = memory->secondLtype();
                if ((isPointerType(secondLtype, Substitution(), arguments) ||
                     (isArrayType(secondLtype, Substitution(), arguments) &&
                      isCArray(memory->secondNode(),ltype,arguments)))
                    && isIntegralType(ltype,arguments)) {
                  term& baseNode = memory->secondNode();
                  if (isCArray(memory->secondNode(),ltype,arguments))
		      baseNode = makeLogicStartOf(baseNode, arguments);
                  assert(memory->firstLabel() ? (bool) memory->secondLabel()
                      : ! (bool) memory->secondLabel());
                  pushLastArgument(NULL, NULL,
                    predicate_named_cons(NULL, _startLocation,
                      predicate_Pfresh(memory->extractFirstLabelOption(),
                        memory->extractSecondLabelOption(),
                        memory->extractSecondNode(), node)));
                  _startLocation= NULL;
                }
                else {
                  free_logic_type(secondLtype);
                  free_term(memory->secondNode());
                  if (node) free_term(node);
                  free_location(_startLocation);
                  _startLocation = NULL;
                  DefineAddError(
                    "expecting predicate of the form \\fresh(pointer,size)")
                };
                free_logic_type(ltype);
                state.freeRuleResult();
                arguments.extendLocationWithToken(_loc);
                if (_doesStopTypeAmbiguity)
                  DefineTReduce
                DefineGotoCase(AfterPrimary)
            }
          }
          else if (((const OperatorPunctuatorToken&) token).getType()
              == OperatorPunctuatorToken::TComma) {
            if (state.point() != DFreshTerm) {
              state.freeRuleResult();
              free_location(_startLocation);
              _startLocation = NULL;
              DefineAddError("')' expected, second term ignored "
                  "for the memory construct");
              DefineGotoCaseAndParse(AfterPrimary)
            };

            Parser::State::RuleAccess::TCastFromRule<
              TermOrPredicateMemoryExtension> memory(state.getRuleResult());
            logic_type ltype = NULL;
            term node = memory->extractTermOrSet(arguments, ltype);
            if (!(ltype && node)) {
              DefineAddError("expecting a term before ')'");
              DefineReduceAndParse
            };
            memory->setSecondNode(node);
            memory->setSecondLtype(ltype);
            DefineShiftWithIncrement(0, LTermMemory,
                (TermOrPredicate&) *memory, &TermOrPredicate::readToken);
          };
        };
      };
      DefineAddError("')' expected in a memory construct");
      state.freeRuleResult();
      DefineGotoCaseAndParse(AfterPrimary);
    case DInitializedLocation:
    case DDanglingLocation:
    case DValidLocation:
    case DValidReadLocation:
    case DValidFunctionLocation:
    case DValidIndexLocation:
    case DValidRangeLocation:
    case DSeparatedLocation:
LLocationMemory:
      assert(_startLocation);
      { AbstractToken token = arguments.queryToken();
        if (token.getType() == AbstractToken::TOperatorPunctuator) {
          if (((const OperatorPunctuatorToken&) token).getType()
              == OperatorPunctuatorToken::TCloseParen) {
            arguments.extendLocationWithToken(_startLocation);
            Parser::State::RuleAccess::TCastFromRule<
              TermOrPredicateMemoryExtension> memory(state.getRuleResult());
            logic_type ltype = NULL;
            term locationNode = memory->extractTermOrSet(arguments, ltype);
            if (!(locationNode && ltype)) {
              DefineAddError("expecting a term before ')'");
              DefineReduceAndParse
            };
            switch (state.point()) {
            case DInitializedLocation:
            case DDanglingLocation:  // TOOD: Probably needs its own case
                if (isCArray(locationNode,ltype,arguments))
		    locationNode = makeLogicStartOf(locationNode, arguments);
                pushLastArgument(NULL, NULL, predicate_named_cons(NULL,
                    _startLocation, predicate_Pinitialized(
                      memory->extractLabelOption(), locationNode)));
                _startLocation = NULL;
                free_logic_type(ltype);
                state.freeRuleResult();
                arguments.extendLocationWithToken(_loc);
                if (_doesStopTypeAmbiguity)
                  DefineTReduce
                DefineGotoCase(AfterPrimary)
              case DValidLocation:
		    if (isCArray(locationNode,ltype,arguments))
		  {
		    locationNode = makeLogicStartOf(locationNode, arguments);}
                pushLastArgument(NULL, NULL, predicate_named_cons(NULL,
                  _startLocation, predicate_Pvalid(memory->extractLabelOption(),
                      locationNode)));
                _startLocation = NULL;
                free_logic_type(ltype);
                state.freeRuleResult();
                arguments.extendLocationWithToken(_loc);
                if (_doesStopTypeAmbiguity)
                  DefineTReduce
                DefineGotoCase(AfterPrimary)
              case DValidReadLocation:
        if (isCArray(locationNode,ltype,arguments))
        locationNode = makeLogicStartOf(locationNode, arguments);
                pushLastArgument(NULL, NULL, predicate_named_cons(NULL,
                    _startLocation, predicate_Pvalid_read(
                        memory->extractLabelOption(), locationNode)));
                _startLocation = NULL;
                free_logic_type(ltype);
                state.freeRuleResult();
                arguments.extendLocationWithToken(_loc);
                if (_doesStopTypeAmbiguity)
                  DefineTReduce
                DefineGotoCase(AfterPrimary)
              case DValidFunctionLocation:
                pushLastArgument(NULL, NULL, predicate_named_cons(NULL,
                    _startLocation, predicate_Pvalid_function(locationNode)));
                _startLocation = NULL;
                free_logic_type(ltype);
                state.freeRuleResult();
                arguments.extendLocationWithToken(_loc);
                if (_doesStopTypeAmbiguity)
                  DefineTReduce
                DefineGotoCase(AfterPrimary)
              case DValidIndexLocation:
                if (memory->queryAdditionalNodesNumber() != 1) {
                  state.freeRuleResult();
                  free_location(_startLocation);
                  _startLocation = NULL;
                  DefineAddError("another location expected "
                      "before ')' in the memory construct");
                  DefineGotoCaseAndParse(AfterPrimary)
                };
                { term baseLocation = memory->extractSecondNode();
                  if (isCArray(baseLocation,ltype,arguments))
		      baseLocation = makeLogicStartOf(baseLocation, arguments);
                  term index = locationNode;
                  location plusLocation = copy_loc(baseLocation->loc);
                  extend_location_with(plusLocation, index->loc);
                  pushLastArgument(NULL, NULL,
                    predicate_named_cons(NULL, _startLocation,
                      predicate_Pvalid(memory->extractLabelOption(), term_cons(
                          term_node_TBinOp(BOPLUS, baseLocation, index),
                          plusLocation, NULL))));
                  _startLocation = NULL;
                };
                free_logic_type(ltype);
                state.freeRuleResult();
                arguments.extendLocationWithToken(_loc);
                if (_doesStopTypeAmbiguity)
                  DefineTReduce
                DefineGotoCase(AfterPrimary)
              case DValidRangeLocation:
                if (memory->queryAdditionalNodesNumber() != 2) {
                  state.freeRuleResult();
                  free_location(_startLocation);
                  _startLocation = NULL;
                  DefineAddError("another location expected "
                      "before ')' in the memory construct");
                  DefineGotoCaseAndParse(AfterPrimary)
                };
                { term baseLocation = memory->extractSecondNode();
                  if (isCArray(baseLocation,ltype,arguments))
		      baseLocation = makeLogicStartOf(baseLocation, arguments);
                  term min = memory->extractThirdNode();
                  term max = locationNode;
                  location rangeLocation = copy_loc(min->loc);
                  location plusLocation = copy_loc(baseLocation->loc);
                  extend_location_with(rangeLocation, max->loc);
                  extend_location_with(plusLocation, max->loc);
                  pushLastArgument(NULL, NULL,
                    predicate_named_cons(NULL, _startLocation,
                      predicate_Pvalid(memory->extractLabelOption(), term_cons(
                        term_node_TBinOp(BOPLUS, baseLocation,
                          term_cons(term_node_TRange(opt_some_container(min),
                            opt_some_container(max)), rangeLocation, NULL)),
                        plusLocation, NULL))));
                  _startLocation = NULL;
                };
                free_logic_type(ltype);
                state.freeRuleResult();
                arguments.extendLocationWithToken(_loc);
                if (_doesStopTypeAmbiguity)
                  DefineTReduce
                DefineGotoCase(AfterPrimary)
              case DSeparatedLocation:
                memory->addAddress(locationNode);
                /* term */ list locations = memory->extractAddresses();
                /* term */ list locationIterator = locations;
                while (locationIterator != NULL) {
                  term currentLocation = (term)
                    locationIterator->element.container;
                  if (isCArray(currentLocation,ltype,arguments))
                    locationIterator->element.container =
                      makeLogicStartOf(currentLocation, arguments);
                  locationIterator = locationIterator->next;
                };
                pushLastArgument(NULL, NULL, predicate_named_cons(NULL,
                    _startLocation, predicate_Pseparated(locations)));
                _startLocation = NULL;
                free_logic_type(ltype);
                state.freeRuleResult();
                arguments.extendLocationWithToken(_loc);
                if (_doesStopTypeAmbiguity)
                  DefineTReduce
                DefineGotoCase(AfterPrimary)
            }
          }
          else if (((const OperatorPunctuatorToken&) token).getType()
              == OperatorPunctuatorToken::TComma) {
            int point = state.point();
            if (point != DSeparatedLocation && point != DValidIndexLocation
                && point != DValidRangeLocation) {
              state.freeRuleResult();
              free_location(_startLocation);
              _startLocation = NULL;
              DefineAddError("')' expected, second term ignored "
                  "for the memory construct");
              DefineGotoCaseAndParse(AfterPrimary)
            };

            Parser::State::RuleAccess::TCastFromRule<
              TermOrPredicateMemoryExtension> memory(state.getRuleResult());
            logic_type ltype = NULL;
            term node = memory->extractTermOrSet(arguments, ltype);
            if (!(ltype && node)) {
              DefineAddError("expecting a term before ')'");
              DefineReduceAndParse
            };
            free_logic_type(ltype);
            if (point == DSeparatedLocation)
              memory->addAddress(node);
            else if (!memory->hasSecondNode())
              memory->setSecondNode(node);
            else {
              memory->setThirdNode(node);
              if (point != DValidRangeLocation) {
                state.freeRuleResult();
                free_location(_startLocation);
                _startLocation = NULL;
                DefineAddError("')' expected, second term ignored "
                    "for the memory construct");
                DefineGotoCaseAndParse(AfterPrimary)
              };
            };
            DefineShiftWithIncrement(0, LLocationMemory,
                (TermOrPredicate&) *memory, &TermOrPredicate::readToken);
          };
        };
      };
      free_location(_startLocation);
      _startLocation = NULL;
      DefineAddError("')' expected in a memory construct");
      state.freeRuleResult();
      DefineGotoCaseAndParse(AfterPrimary);
    DefineParseCase(AtBegin)
      assert(_startLocation);
      { AbstractToken token = arguments.queryToken();
        if (token.getType() == AbstractToken::TOperatorPunctuator) {
          if (((const OperatorPunctuatorToken&) token).getType()
              == OperatorPunctuatorToken::TOpenParen) {
            TermOrPredicateMemoryExtension* subTerm
              = new TermOrPredicateMemoryExtension;
            state.absorbRuleResult(subTerm);
            DefineShift(AtMiddle, *subTerm, &TermOrPredicate::readToken);
          };
        };
      };
      free_location(_startLocation);
      _startLocation = NULL;
      DefineAddError("'(' expected after the \\at keyword");
      DefineGotoCaseAndParse(Begin)
    DefineParseCase(OldBegin)
      assert(_startLocation);
      { AbstractToken token = arguments.queryToken();
        if (token.getType() == AbstractToken::TOperatorPunctuator) {
          if (((const OperatorPunctuatorToken&) token).getType()
              == OperatorPunctuatorToken::TOpenParen) {
            TermOrPredicate* subTerm = new TermOrPredicate;
            state.absorbRuleResult(subTerm);
            DefineShift(OldEnd, *subTerm, &TermOrPredicate::readToken);
          };
        };
      };
      free_location(_startLocation);
      _startLocation = NULL;
      DefineAddError("'(' expected after the \\old keyword");
      DefineGotoCaseAndParse(Begin)
    DefineParseCase(AtMiddle)
      assert(_startLocation);
      { AbstractToken token = arguments.queryToken();
        if (token.getType() == AbstractToken::TOperatorPunctuator) {
          if (((const OperatorPunctuatorToken&) token).getType()
              == OperatorPunctuatorToken::TComma)
            DefineGotoCase(AtLabel)
        };
      };
      DefineAddError("',' expected in the \\at construct to parse the label");
      DefineGotoCaseAndParse(AtEnd)
    DefineParseCase(OldEnd)
      assert(_startLocation);
      { AbstractToken token = arguments.queryToken();
        if (token.getType() == AbstractToken::TOperatorPunctuator) {
          if (((const OperatorPunctuatorToken&) token).getType()
              == OperatorPunctuatorToken::TCloseParen) {
            arguments.extendLocationWithToken(_startLocation);
            Parser::State::RuleAccess::TCastFromRule<TermOrPredicate>
                rule(state.getRuleResult());
            logic_label label = arguments.findLogicLabel("Old");
            if (!label)
              DefineAddError("\\old undefined in this context");
            logic_type ltype = NULL;
            predicate_named pred = NULL;
            term node = NULL;
            rule->extractTermOrPredicate(arguments, ltype, node, pred);
            if (!(node || pred)) {
              DefineAddError("expecting a term before ')'");
              DefineReduceAndParse
            };
            if (node && pred)
              pushLastArgument(ltype, term_cons(term_node_TAt(node, label),
                copy_loc(_startLocation), NULL), predicate_named_cons(NULL,
                _startLocation, predicate_Pat(logic_label_dup(label), pred)));
            else if (node)
              pushLastArgument(ltype, term_cons(term_node_TAt(node, label),
                  copy_loc(_startLocation), NULL), NULL);
            else if (pred)
              pushLastArgument(NULL, NULL, predicate_named_cons(NULL,
                  _startLocation, predicate_Pat(label, pred)));
            _startLocation = NULL;
            state.freeRuleResult();
            arguments.extendLocationWithToken(_loc);
            if (_doesStopTypeAmbiguity)
              DefineTReduce
            DefineGotoCase(AfterPrimary)
          };
        };
      };
      DefineAddError("')' expected at the end of the \\old construct");
      DefineGotoCase(OldEnd)
    DefineParseCase(AtLabel)
      assert(_startLocation);
      if (arguments.queryToken().getType() == AbstractToken::TIdentifier) {
        const std::string& identifier = ((const IdentifierToken&) arguments
            .getContentToken()).content();
        Parser::State::RuleAccess::TCastFromRule<TermOrPredicateMemoryExtension>
            rule(state.getRuleResult());
        logic_label foundLabel = arguments.findLogicLabel(identifier);
        if (!foundLabel)
          DefineAddError("expecting a label in the \\at construct");
        rule->addLabel(foundLabel);
        DefineGotoCase(AtEnd)
      };
      DefineAddError("expecting a label in the \\at construct");
      DefineGotoCase(AtLabel)
    DefineParseCase(AtEnd)
      assert(_startLocation);
      { AbstractToken token = arguments.queryToken();
        if (token.getType() == AbstractToken::TOperatorPunctuator) {
          if (((const OperatorPunctuatorToken&) token).getType()
              == OperatorPunctuatorToken::TCloseParen) {
            arguments.extendLocationWithToken(_startLocation);
            Parser::State::RuleAccess::TCastFromRule<
              TermOrPredicateMemoryExtension> rule(state.getRuleResult());
            term node = NULL;
            logic_type ltype = NULL;
            predicate_named pred = NULL;
            rule->extractTermOrPredicate(arguments, ltype, node, pred);
            if (!(node || pred)) {
              if (arguments.doesStopAfterTooManyErrors())
                return RRFinished;
              DefineReduceAndParse
            };
            if (node && pred) {
              logic_label label = rule->extractFirstLabel();
              pushLastArgument(ltype, term_cons(term_node_TAt(node, label),
                  _startLocation, NULL),
                predicate_named_cons(NULL, copy_loc(_startLocation),
                  predicate_Pat(logic_label_dup(label), pred)));
            }
            else if (node)
              pushLastArgument(ltype, term_cons(term_node_TAt(node,
                  rule->extractFirstLabel()), _startLocation, NULL), NULL);
            else if (pred)
              pushLastArgument(NULL, NULL, predicate_named_cons(NULL,
                  _startLocation, predicate_Pat(rule->extractFirstLabel(),
                  pred)));
            _startLocation = NULL;
            state.freeRuleResult();
            arguments.extendLocationWithToken(_loc);
            if (_doesStopTypeAmbiguity)
              DefineTReduce
            DefineGotoCase(AfterPrimary)
          };
        };
      };
      DefineAddError("')' expected at the end of the \\at construct");
      DefineGotoCase(AtEnd)
    DefineParseCase(SetBeforeInter)
    DefineParseCase(SetBeforeUnion)
      assert(_startLocation);
      { AbstractToken token = arguments.queryToken();
        if (token.getType() == AbstractToken::TOperatorPunctuator) {
          if (((const OperatorPunctuatorToken&) token).getType()
              == OperatorPunctuatorToken::TOpenParen) {
            TermOrPredicate* subTerm = new TermOrPredicateList;
            state.absorbRuleResult(subTerm);
            subTerm->_possibleTypeResults = (1U << LTRSet);
            DefineShiftWithIncrement(DSetInter - DSetBeforeInter, LSetUI,
                *subTerm, &TermOrPredicate::readToken);
          };
        };
      };
      free_location(_startLocation);
      _startLocation = NULL;
      DefineAddError("'(' expected after \\union or \\inter");
      arguments.extendLocationWithToken(_loc);
      DefineGotoCase(AfterPrimary)
    case DSetInter:
    case DSetUnion:
LSetUI:
      assert(_startLocation);
      { AbstractToken token = arguments.queryToken();
        if (token.getType() == AbstractToken::TOperatorPunctuator) {
          OperatorPunctuatorToken::Type type = ((const OperatorPunctuatorToken&)
              token).getType();
          if (type == OperatorPunctuatorToken::TCloseParen) {
            arguments.extendLocationWithToken(_startLocation);
            Parser::State::RuleAccess::TCastFromRule<TermOrPredicateList>
                rule(state.getRuleResult());
            logic_type ltype = NULL;
            term node = rule->extractTermOrSet(arguments, ltype);
            if (!node) {
              DefineAddError("expecting a term or a set before ')'");
              DefineReduceAndParse
            };
            rule->addComponent(node, ltype, arguments);
            ltype = NULL;
            /* term */ list components = rule->extractComponents(ltype);
            if (state.point() == DSetInter) 
              pushLastArgument(ltype,
                term_cons(term_node_TInter(components), _startLocation, NULL),
                NULL);
            else
              pushLastArgument(ltype,
                term_cons(term_node_TUnion(components), _startLocation, NULL),
                NULL);
            _startLocation = NULL;
            state.freeRuleResult();
            arguments.extendLocationWithToken(_loc);
            if (_doesStopTypeAmbiguity)
              DefineTReduce
            DefineGotoCase(AfterPrimary)
          }
          else if (type == OperatorPunctuatorToken::TComma) {
            Parser::State::RuleAccess::TCastFromRule<TermOrPredicateList>
                rule(state.getRuleResult());
            logic_type ltype = NULL;
            term node = rule->extractTermOrSet(arguments, ltype);
            if (!node) {
              DefineAddError("expecting a term or a set before ','");
              DefineReduceAndParse
            };
            rule->addComponent(node, ltype, arguments);
            DefineShiftWithIncrement(0, LSetUI, (TermOrPredicate&) *rule,
                &TermOrPredicate::readToken)
          };
        };
      };
      DefineAddError("')' expected or ',' in the \\union, \\inter construct");
      DefineGotoCaseWithIncrement(0, LSetUI)
    DefineParseCase(SetBeforeSubset)
      assert(_startLocation);
      { AbstractToken token = arguments.queryToken();
        if (token.getType() == AbstractToken::TOperatorPunctuator) {
          if (((const OperatorPunctuatorToken&) token).getType()
              == OperatorPunctuatorToken::TOpenParen) {
            TermOrPredicate* subTerm = new TermOrPredicateMemoryExtension;
            state.absorbRuleResult(subTerm);
            subTerm->_possibleTypeResults = (1U << LTRSet);
            DefineShift(SetSubsetFirst, *subTerm, &TermOrPredicate::readToken);
          };
        };
      };
      DefineAddError("'(' expected after the \\subset keyword");
      DefineGotoCaseAndParse(AfterPrimary)
    DefineParseCase(SetSubsetFirst)
      assert(_startLocation);
      { AbstractToken token = arguments.queryToken();
        if (token.getType() == AbstractToken::TOperatorPunctuator) {
          if (((const OperatorPunctuatorToken&) token).getType()
              == OperatorPunctuatorToken::TComma) {
            Parser::State::RuleAccess::TCastFromRule<
              TermOrPredicateMemoryExtension> rule(state.getRuleResult());
            logic_type ltype = NULL;
            term node = rule->extractTermOrSet(arguments, ltype);
            if (!node) {
              DefineAddError("expecting a term or a set before ','");
              DefineReduceAndParse
            };
            rule->setSecondNode(node);
            DefineShift(SetSubsetSecond, (TermOrPredicate&) *rule,
                &TermOrPredicate::readToken)
          };
        };
      };
      DefineAddError("',' expected in the \\subset construct");
      DefineGotoCaseAndParse(SetSubsetSecond)
    DefineParseCase(SetSubsetSecond)
      assert(_startLocation);
      { AbstractToken token = arguments.queryToken();
        if (token.getType() == AbstractToken::TOperatorPunctuator) {
          if (((const OperatorPunctuatorToken&) token).getType()
              == OperatorPunctuatorToken::TCloseParen) {
            arguments.extendLocationWithToken(_startLocation);
            Parser::State::RuleAccess::TCastFromRule<
              TermOrPredicateMemoryExtension> rule(state.getRuleResult());
            logic_type ltype = NULL;
            term node = rule->extractTermOrSet(arguments, ltype);
            if (!node) {
              DefineAddError("expecting a term of a set before ')'");
              DefineReduceAndParse
            };
            free_logic_type(ltype);
            qualified_name name = qualified_name_cons(NULL,"\\subset");
            list args =
              cons_container(
                rule->extractSecondNode(), cons_container(node,NULL));
            predicate subset =predicate_PApp(name,NULL,args,true);
            pushLastArgument(
              NULL, NULL,
              predicate_named_cons(NULL, arguments.newTokenLocation(), subset));
            _startLocation = NULL;
            state.freeRuleResult();
            arguments.extendLocationWithToken(_loc);
            if (_doesStopTypeAmbiguity)
              DefineTReduce
            DefineGotoCase(AfterPrimary)
          };
        };
        DefineAddError("',' expected in the \\subset construct");
        if (token.getType() == AbstractToken::TOperatorPunctuator) {
          if (((const OperatorPunctuatorToken&) token).getType()
              == OperatorPunctuatorToken::TCloseParen) {
            free_location(_startLocation);
            _startLocation = NULL;
            state.freeRuleResult();
            DefineGotoCase(AfterPrimary)
          }
        };
      };
      DefineGotoCase(SetSubsetSecond)
  };
  return result;
}

Parser::ReadResult
TermOrPredicate::Binders::readToken(Parser::State& state,
    Parser::Arguments& arguments) {
  enum Delimiters
    { DBegin, DAfterType, DNextBinder, DTypeModifier, 
      DAfterTypeIdentifier, DTypeSuffixArray };
  ReadResult result = RRNeedChars;
  switch (state.point()) {
    DefineParseCase(Begin)
      { LogicType* rule = new LogicType;
        state.absorbRuleResult(rule);
        rule->setStopOnSuffix();
        DefineShiftAndParse(AfterType, *rule, &LogicType::readToken);
      };
    DefineParseCase(AfterType)
      { Parser::State::RuleAccess::TCastFromRule<LogicType>
          rule(state.getRuleResult());
        _currentDeclType = rule->extractType();
        state.freeRuleResult();
      };
      DefineGotoCaseAndParse(TypeModifier)
    // We'll recurse to check for multiple '*', but we only have to extract
    // the specifier once. AfterType thus falls through 
    // the main part of the rule which starts here.
    DefineParseCase(NextBinder)
    DefineParseCase(TypeModifier)
      { AbstractToken token = arguments.queryToken();
        if (token.getType() == AbstractToken::TIdentifier) {
          const std::string& identifier = ((const IdentifierToken&)
              arguments.getContentToken()).content();
          if (!_currentVarType)
            _currentVarType = logic_type_dup(_currentDeclType);
          _result.insertContainer(
            logic_var_def_cons(
              qualified_name_cons(
                arguments.createPrequalification(), strdup(identifier.c_str())),
              _currentVarType, LVQUANT));
          if (!_parentVarTypes.empty()
              && _parentVarTypes.back() == &_currentVarType)
            _parentVarTypes.back() =
              &((logic_var_def)
                _result.getFront()->element.container)->lv_type;
          _postInsertionType =
            &((logic_var_def)
              _result.getFront()->element.container)->lv_type;
          _currentVarType = NULL;
          DefineGotoCase(AfterTypeIdentifier)
        }
        else if (token.getType() == AbstractToken::TOperatorPunctuator) {
          OperatorPunctuatorToken::Type type = ((const OperatorPunctuatorToken&)
              token).getType();
          if (type == OperatorPunctuatorToken::TStar) {
            if (!_currentVarType)
              _currentVarType = logic_type_dup(_currentDeclType);
            logic_type pointerType = logic_type_Lpointer(_currentVarType);
            if (!_parentVarTypes.empty()
                && _parentVarTypes.back() == &_currentVarType)
              _parentVarTypes.back()
                = &pointerType->cons_logic_type.Lpointer.subtype;
            _currentVarType = pointerType;
            DefineGotoCase(TypeModifier)
          }
          else if (type == OperatorPunctuatorToken::TAmpersand) {
            if (!_currentVarType)
              _currentVarType = logic_type_dup(_currentDeclType);
            logic_type referenceType = logic_type_Lreference(_currentVarType);
            if (!_parentVarTypes.empty()
                && _parentVarTypes.back() == &_currentVarType)
              _parentVarTypes.back()
                = &referenceType->cons_logic_type.Lreference.subtype;
            _currentVarType = referenceType;
            DefineGotoCase(TypeModifier)
          }
          else if (type == OperatorPunctuatorToken::TOpenParen) {
            if (!_currentVarType)
              _currentVarType = logic_type_dup(_currentDeclType);
            _parentVarTypes.push_back(&_currentVarType);
            DefineGotoCase(TypeModifier)
          };
        }
        else if (token.getType() == AbstractToken::TKeyword) {
          KeywordToken::Type type = ((const KeywordToken&) token).getType();
          if (type == KeywordToken::TConst || type == KeywordToken::TVolatile)
            DefineGotoCase(TypeModifier)
        };
      };
      if (state.point() == DNextBinder) {
        LogicType* type = new LogicType;
        type->setStopOnSuffix();
        state.absorbRuleResult(type);
        DefineShiftAndParse(AfterType,*type,&LogicType::readToken)
      } else {
        DefineAddError(
          std::string("expecting idendifier " 
                      "after parsing a logic type in binder")); }
      DefineReduce
    DefineParseCase(AfterTypeIdentifier)
      { AbstractToken token = arguments.queryToken();
        if (token.getType() == AbstractToken::TOperatorPunctuator) {
          OperatorPunctuatorToken::Type type = ((const OperatorPunctuatorToken&)
              token).getType();
          if (type == OperatorPunctuatorToken::TCloseParen) {
            _postInsertionType = _parentVarTypes.back();
            _parentVarTypes.pop_back();
            DefineGotoCase(AfterTypeIdentifier)
          };
          if (type == OperatorPunctuatorToken::TOpenBracket) {
            TermOrPredicate* subTerm = new TermOrPredicate;
            state.absorbRuleResult(&subTerm->setTerm());
            DefineShift(TypeSuffixArray, *subTerm, &TermOrPredicate::readToken)
          };
          if (type == OperatorPunctuatorToken::TComma) {
            _parentVarTypes.clear();
            _postInsertionType = NULL;
            DefineGotoCase(NextBinder)
          };
        };
      };
      if (!_parentVarTypes.empty())
        DefineAddError(std::string("expecting ')' while parsing "
              "a logic type in binder"));
      DefineReduceAndParse
    DefineParseCase(TypeSuffixArray)
      { AbstractToken token = arguments.queryToken();
        if (token.getType() == AbstractToken::TOperatorPunctuator
            && (((const OperatorPunctuatorToken&) token).getType()
              == OperatorPunctuatorToken::TCloseBracket)) {
          // int intResult = 0; double doubleResult = 0;
          logic_type ltype = NULL;
          term termNode;
          const char* dimension = strdup("0");
          // bool isRValue = false;
          { Parser::State::RuleAccess::TCastFromRule<TermOrPredicate>
              subterm(state.getRuleResult());
            // bool isConstant = false; // [TODO] activate it!
            termNode = subterm->extractTerm(arguments, ltype);
            state.freeRuleResult();
            if (!termNode) {
              DefineAddError("expecting a term before ']'");
              DefineReduceAndParse
            };
          };
          // if (!isRValue) {
          //   // term_lval_cons ...
          //   // term_node = term_node_TLval(lval)
          // };
          assert(ltype && termNode);
          assert(false); // unimplemented
          *_postInsertionType = logic_type_Larray(*_postInsertionType,
              opt_some_container(logic_constant_LCInt(dimension)));
          DefineGotoCase(AfterTypeIdentifier)
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
  };
  return result;
}

Parser::ReadResult
TermOrPredicate::SetComprehension::readToken(Parser::State& state,
    Parser::Arguments& arguments) {
  enum Delimiters
    { DBegin, DBinders, DCondition, DBeforeBrace };

  ReadResult result = RRNeedChars;
  switch (state.point()) {
    DefineParseCase(Begin)
      { Binders* binders = new Binders;
        state.absorbRuleResult(binders);
        DefineShiftAndParse(Binders, *binders, &Binders::readToken);
      }
    DefineParseCase(Binders)
      { Parser::State::RuleAccess::TCastFromRule<Binders>
          binders(state.getRuleResult());
        /* logic_var_def */ list binderIter;
        _binders = binderIter = binders->extractResult();
        while (binderIter != NULL) {
          // to parse the node before ;-)
          logic_var_def def = (logic_var_def) binderIter->element.container;
          arguments.addLocalBinding(def->lv_name->decl_name,
              logic_var_def_dup(def));
          binderIter = binderIter->next;
        };
        state.freeRuleResult();
        AbstractToken token = arguments.queryToken();
        if (token.getType() == AbstractToken::TOperatorPunctuator) {
          OperatorPunctuatorToken::Type type = ((const OperatorPunctuatorToken&)
              token).getType();
          if (type == OperatorPunctuatorToken::TCloseBrace) {
            /* logic_var_def */ list binderIter = _binders;
            while (binderIter != NULL) {
              logic_var_def def = (logic_var_def) binderIter->element.container;
              arguments.removeLocalBinding(def->lv_name->decl_name);
              binderIter = binderIter->next;
            };
            DefineReduceAndParse
          }
          else if (type == OperatorPunctuatorToken::TSemiColon) {
            TermOrPredicate* condition = new TermOrPredicate;
            state.absorbRuleResult(condition);
            DefineShiftAndParse(Condition, *condition,
                &TermOrPredicate::readToken);
          };
        };
      };
      DefineAddError("expecting ';' or '}' in the set comprehension construct");
      DefineGotoCase(BeforeBrace)
    DefineParseCase(Condition)
      { Parser::State::RuleAccess::TCastFromRule<TermOrPredicate>
          subterm(state.getRuleResult());
        _suchThatCondition = subterm->extractPredicate(arguments);
        state.freeRuleResult();
        if (!_suchThatCondition) {
          DefineAddError("expecting a predicate");
          DefineReduceAndParse
        };
        AbstractToken token = arguments.queryToken();
        if (token.getType() == AbstractToken::TOperatorPunctuator) {
          OperatorPunctuatorToken::Type type = ((const OperatorPunctuatorToken&)
              token).getType();
          if (type == OperatorPunctuatorToken::TCloseBrace) {
            /* logic_var_def */ list binderIter = _binders;
            while (binderIter != NULL) {
              logic_var_def def = (logic_var_def) binderIter->element.container;
              arguments.removeLocalBinding(def->lv_name->decl_name);
              binderIter = binderIter->next;
            };
            DefineReduceAndParse
          }
        };
      };
      DefineAddError("'}' expected at the end "
          "of the set comprehension construct");
      DefineGotoCase(BeforeBrace)
    DefineParseCase(BeforeBrace)
      { AbstractToken token = arguments.queryToken();
        if (token.getType() == AbstractToken::TOperatorPunctuator) {
          OperatorPunctuatorToken::Type type = ((const OperatorPunctuatorToken&)
              token).getType();
          if (type == OperatorPunctuatorToken::TCloseBrace) {
            /* logic_var_def */ list binderIter = _binders;
            while (binderIter != NULL) {
              logic_var_def def = (logic_var_def) binderIter->element.container;
              arguments.removeLocalBinding(def->lv_name->decl_name);
              binderIter = binderIter->next;
            };
            DefineReduceAndParse
          };
        };
      };
      DefineGotoCase(BeforeBrace)
  };
  return result;
}

Parser::ReadResult
TermOrPredicate::Range::readToken(Parser::State& state,
    Parser::Arguments& arguments) {
  enum Delimiters
    { DBegin, DMax };

  ReadResult result = RRNeedChars;
  switch (state.point()) {
    DefineParseCase(Begin)
      { AbstractToken token = arguments.queryToken();
        if (token.getType() == AbstractToken::TOperatorPunctuator) {
          OperatorPunctuatorToken::Type
            type = ((const OperatorPunctuatorToken&) token).getType();
          if (type == OperatorPunctuatorToken::TCloseParen
              || type == OperatorPunctuatorToken::TCloseBracket
              || type == OperatorPunctuatorToken::TCloseBrace)
            DefineReduceAndParse
        };
      }
      { TermOrPredicate* max = new TermOrPredicate;
        state.absorbRuleResult(max);
        DefineShiftAndParse(Max, *max, &TermOrPredicate::readToken);
      }
    DefineParseCase(Max)
      { Parser::State::RuleAccess::TCastFromRule<TermOrPredicate>
          max(state.getRuleResult());
        _maxNode = max->extractTerm(arguments, _maxType);
        state.freeRuleResult();
        if (!_maxNode) {
          DefineAddError("expecting a term after '..'");
          DefineReduceAndParse
        };
      };
      DefineReduceAndParse
  };
  return result;
}

Parser::ReadResult
TermOrPredicate::WithConstruct::readToken(Parser::State& state,
    Parser::Arguments& arguments) {
  enum Delimiters
    { DUpdate, DWithOrWithout, DAfterBraceTerm, DUpdateArrayIndex,
      DUpdatePointField, DWithAssignment, DBeforeTermAssignment,
      DTermAssignment, DEnd, DSubTerm
    };
  
  ReadResult result = RRNeedChars;
  switch (state.point()) {
    DefineParseCase(Update)
      if (arguments.queryToken().getType()
          == AbstractToken::TOperatorPunctuator) {
        AbstractToken token = arguments.queryToken();
        OperatorPunctuatorToken::Type type = ((const OperatorPunctuatorToken&)
            token).getType();
        if (type == OperatorPunctuatorToken::TOpenBracket) {
          TermOrPredicate* subTerm = new TermOrPredicate;
          state.absorbRuleResult(&subTerm->setTerm());
          DefineShift(UpdateArrayIndex, *subTerm, &TermOrPredicate::readToken)
        }
        else if (type == OperatorPunctuatorToken::TPunct)
          DefineGotoCase(UpdatePointField)
      };
      DefineAddError("expecting '.field' or '[index]' "
          "after a \\with construct");
      DefineReduce
    DefineParseCase(WithOrWithout)
      { AbstractToken token = arguments.queryToken();
        if (token.getType() == AbstractToken::TKeyword) {
          if (((const KeywordToken&) token).getType() == KeywordToken::TWith)
            DefineGotoCase(Update)
        }
      };
      { TermOrPredicate* subTerm = new TermOrPredicate;
        state.absorbRuleResult(subTerm);
        subTerm->_possibleTypeResults = (1U << TermOrPredicate::LTRTerm);
        DefineShiftAndParse(AfterBraceTerm, *subTerm,
            &TermOrPredicate::readToken);
      };
    DefineParseCase(AfterBraceTerm)
      { AbstractToken token = arguments.queryToken();
        if (token.getType() == AbstractToken::TKeyword) {
          if (((const KeywordToken&) token).getType() == KeywordToken::TWith) {
            logic_type ltype = NULL;
            term termNode;
            { Parser::State::RuleAccess::TCastFromRule<TermOrPredicate>
                subterm(state.getRuleResult());
              termNode = subterm->extractTerm(arguments, ltype);
              state.freeRuleResult();
              if (!termNode) {
                DefineAddError("expecting a term before '\\with'");
                DefineReduceAndParse
              };
            };
            WithConstruct* subConstruct = new WithConstruct(ltype, termNode);
            state.absorbRuleResult(subConstruct);
            DefineShift(SubTerm, *subConstruct, &WithConstruct::readToken);
          };
        };
      };
      DefineAddError("expecting '}' or '|' in the with construct");
      DefineGotoCase(AfterBraceTerm);
    DefineParseCase(UpdateArrayIndex)
      if (arguments.queryToken().getType()
          == AbstractToken::TOperatorPunctuator) {
        AbstractToken token = arguments.queryToken();
        if (((const OperatorPunctuatorToken&) token).getType()
            == OperatorPunctuatorToken::TCloseBracket) {
          logic_type ltype = NULL;
          term termNode = NULL;
          { Parser::State::RuleAccess::TCastFromRule<TermOrPredicate>
              subterm(state.getRuleResult());
            termNode = subterm->extractTerm(arguments, ltype);
            state.freeRuleResult();
            if (!termNode) {
              DefineAddError("expecting a term before ']'");
              DefineReduceAndParse
            };
          };
          assert(termNode && ltype);
          free_logic_type(ltype);
          ltype = _updates.empty() ? _ltype : _updates.back().second;
          logic_type lsubtype = NULL;
          term_offset offset = NULL;
          if (!TermOrPredicate::isArrayType(ltype,
                TermOrPredicate::Substitution(), arguments))
            DefineAddError("update 'term with []=' with array "\
                "construct when term is not an array")
          else {
            lsubtype = TermOrPredicate::typeOfArrayElement(ltype,
                TermOrPredicate::Substitution(), arguments);
            offset = term_offset_TIndex(termNode, term_offset_TNoOffset());
          };
          _updates.push_back(std::make_pair(offset, lsubtype));
          DefineGotoCase(WithAssignment)
        };
      };
      DefineAddError("']' expected at the end of a '\\with [index]' construct");
      DefineGotoCase(UpdateArrayIndex)
    DefineParseCase(UpdatePointField)
      if (arguments.queryToken().getType() == AbstractToken::TIdentifier) {
        const std::string& identifier = ((const IdentifierToken&)
            arguments.getContentToken()).content();
        logic_type ltype = _updates.empty() ? _ltype : _updates.back().second;
        const clang::RecordType* recordType = NULL;
        tkind templateParameters = NULL;
        if (ltype->tag_logic_type == LSTRUCT || ltype->tag_logic_type == LUNION)
        { qualified_name name;
          if (ltype->tag_logic_type == LSTRUCT) {
            name = ltype->cons_logic_type.Lstruct.name;
            templateParameters = ltype->cons_logic_type.Lstruct.template_kind;
          }
          else {
            name = ltype->cons_logic_type.Lunion.name;
            templateParameters = ltype->cons_logic_type.Lunion.template_kind;
          }
          recordType = arguments.getRecordType(name);
        }
        else if (ltype->tag_logic_type == LCNAMED)
          recordType = arguments.getRecordType(
              ltype->cons_logic_type.LCnamed.name);
        logic_type lsubtype = NULL;
        term_offset offset = NULL;
        if (!recordType) {
          DefineAddError("update 'term with .field=' with field "\
              "construct when term is not a struct")
        }
        else {
          const clang::RecordDecl* decl=recordType->getDecl()->getDefinition();
          if (templateParameters
                && templateParameters->tag_tkind == TTEMPLATEINSTANCE)
          { clang::Decl::Kind kind = decl->getKind();
            if (kind >= clang::Decl::firstCXXRecord
                  && kind <= clang::Decl::lastCXXRecord) {
              assert(llvm::dyn_cast<clang::CXXRecordDecl>(decl));
              clang::ClassTemplateDecl* templateDecl
                = static_cast<const clang::CXXRecordDecl*>(decl)
                  ->getDescribedClassTemplate();
              if (templateDecl) {
                clang::ClassTemplateDecl::spec_iterator iterEnd
                  = templateDecl->spec_end();
                decl = NULL;
                for (clang::ClassTemplateDecl::spec_iterator iter = templateDecl
                    ->spec_begin(); !decl && iter != iterEnd; ++iter) {
                  tkind matchTemplateParameters =
                    tkind_TTemplateInstance(
                      arguments.get_clang_utils()->getTemplateExtension(
                        arguments.tokenSourceLocation(),
                        iter->getTemplateArgs()));
                  if (tkind_equal(templateParameters, matchTemplateParameters))
                    decl = *iter;
                  free_tkind(matchTemplateParameters);
                };
              }
              else
                decl = NULL;
            }
            else
              decl = NULL;
          };
          clang::RecordDecl::field_iterator iterEnd = decl->field_end();

          for (clang::RecordDecl::field_iterator iter = decl->field_begin();
              !lsubtype && iter != iterEnd; ++iter) {
            if (iter->getName().str() == identifier) {
              lsubtype =
                arguments.get_clang_utils()->makeLogicType(
                  arguments.tokenSourceLocation(),
                  iter->getType().getTypePtr());
              offset = term_offset_TField(strdup(identifier.c_str()),
                  term_offset_TNoOffset());
            }
          };
          if (lsubtype) {
            _updates.push_back(std::make_pair(offset, lsubtype));
            DefineGotoCase(WithAssignment)
          };
        };
        _updates.push_back(std::make_pair(offset, lsubtype));
        DefineGotoCase(WithAssignment)
      };
      DefineAddError("expecting known field in 'term with .field=' construct")
      _updates.push_back(std::pair<term_offset, logic_type>(NULL, NULL));
      DefineGotoCase(WithAssignment)
    DefineParseCase(WithAssignment)
      { AbstractToken token = arguments.queryToken();
        if (token.getType() == AbstractToken::TOperatorPunctuator) {
          OperatorPunctuatorToken::Type type = ((const OperatorPunctuatorToken&)
              token).getType();
          if (type == OperatorPunctuatorToken::TAssign)
            DefineGotoCase(BeforeTermAssignment)
          if (type == OperatorPunctuatorToken::TCloseBrace) {
            DefineAddError("'=' expected during the parsing "
                "of a '\\with' construct");
            if (_updates.back().first) free_term_offset(_updates.back().first);
            if (_updates.back().second) free_logic_type(_updates.back().second);
            _updates.pop_back();
            if (_updates.empty())
              DefineReduce
            else
              DefineGotoCase(End)
          };
        };
      };
      DefineAddError("'=' expected during the parsing of a '\\with' construct");
      DefineGotoCaseAndParse(WithAssignment)
    DefineParseCase(BeforeTermAssignment)
      { AbstractToken token = arguments.queryToken();
        if (token.getType() == AbstractToken::TOperatorPunctuator) {
          if (((const OperatorPunctuatorToken&) token).getType()
              == OperatorPunctuatorToken::TOpenBrace)
            DefineGotoCase(WithOrWithout)
        };
      }
      { TermOrPredicate* subTerm = new TermOrPredicate;
        state.absorbRuleResult(&subTerm->setTerm());
        DefineShiftAndParse(TermAssignment, *subTerm,
            &TermOrPredicate::readToken)
      };
    DefineParseCase(TermAssignment)
      { // int intResult = 0; double doubleResult = 0;
        // bool isRValue = false;
        // bool isConstant = false;
        logic_type ltype = NULL;
        Parser::State::RuleAccess::TCastFromRule<TermOrPredicate>
          subterm(state.getRuleResult());
        term updateNode = subterm->extractTerm(arguments, ltype);
        state.freeRuleResult();
        if (!(updateNode && ltype)) {
          DefineAddError("expecting a term before '='");
          DefineReduceAndParse
        };

        std::pair<term_offset, logic_type>& back = _updates.back();
        term_offset offset = back.first;
        back.first = NULL;
        std::list<std::pair<term_offset, logic_type> >::const_reverse_iterator
          iterEnd = _updates.rend();
        for (std::list<std::pair<term_offset, logic_type> >
            ::const_reverse_iterator iter = _updates.rbegin();
              iter != iterEnd; ++iter) {
          tag_term_offset tag = iter->first->tag_term_offset;
          if (tag == TFIELD)
            offset = term_offset_TField(strdup(iter->first->cons_term_offset
                  .TField.field), offset);
          else if (tag == TINDEX)
            offset = term_offset_TIndex(term_dup(iter->first->cons_term_offset
                  .TIndex.subexpr), offset);
          else
            assert(false);
        };
        updateNode = TermOrPredicate::makeCast(back.second, updateNode, ltype,
            TermOrPredicate::Substitution(), TermOrPredicate::Substitution(),
            arguments);
        free_logic_type(back.second);
        back.second = NULL;
        location loc = copy_loc(_node->loc);
        extend_location_with(loc, updateNode->loc);
        _node = term_cons(term_node_TUpdate(_node, offset, updateNode),
            loc, NULL);
      };
      DefineGotoCaseAndParse(End)
    DefineParseCase(End)
      { AbstractToken token = arguments.queryToken();
        if (token.getType() == AbstractToken::TOperatorPunctuator) {
          OperatorPunctuatorToken::Type type = ((const OperatorPunctuatorToken&)
              token).getType();
          std::pair<term_offset, logic_type> back = _updates.back();
          _updates.pop_back();
          if (back.first)
            free_term_offset(back.first);
          if (back.second)
            free_logic_type(back.second);

          if (type == OperatorPunctuatorToken::TCloseBrace) {
            if (_updates.empty())
              DefineReduceAndParse
            else
              DefineGotoCase(End)
          };

          if (type != OperatorPunctuatorToken::TComma)
            DefineAddError("expecting ',' or '}' "
                "after a '{ term \\with ... = term }' construct");
          DefineGotoCase(Update)
        };
      };
      DefineAddError("expecting ',' or '}' "
          "after a '{ term \\with ... = term }' construct");
      DefineGotoCase(End)
    DefineParseCase(SubTerm)
      { AbstractToken token = arguments.queryToken();
        if (token.getType() == AbstractToken::TOperatorPunctuator
            && ((const OperatorPunctuatorToken&) token).getType()
                == OperatorPunctuatorToken::TCloseBrace) {
          Parser::State::RuleAccess::TCastFromRule<WithConstruct>
            updateWith(state.getRuleResult());
          logic_type ltype = NULL;
          term termNode = updateWith->extractResult(ltype, arguments);
          state.freeRuleResult();
          std::pair<term_offset, logic_type>& back = _updates.back();
          term_offset offset = back.first;
          back.first = NULL;
          termNode = TermOrPredicate::makeCast(back.second, termNode, ltype,
              TermOrPredicate::Substitution(), TermOrPredicate::Substitution(),
              arguments);
          free_logic_type(back.second);
          back.second = NULL;
          location loc = copy_loc(_node->loc);
          extend_location_with(loc, termNode->loc);
          _node = term_cons(term_node_TUpdate(_node, offset, termNode),
              loc, NULL);
          DefineGotoCaseAndParse(End)
        };
      };
      DefineAddError("'}' expected at the end of an update "
          "'{ term \\with update }' construct.")
      DefineGotoCase(SubTerm)
  };
  return result;
}

#if defined(__clang__) || defined(__GNUC__)
#pragma GCC diagnostic pop
#endif

} // end of namespace Acsl

