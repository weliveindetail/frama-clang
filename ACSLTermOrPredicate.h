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
//   Definition of the ACSL terms and predicates.
//

#ifndef ACSL_TermOrPredicateH
#define ACSL_TermOrPredicateH

#include "ACSLParser.h"
// #include "DescentParse.h"

extern "C" {
#include "intermediate_format.h"
} // end of extern "C"

#include "ACSLLogicType.h"

namespace Acsl {

/*! @class TermOrPredicate
 *  @brief Component that parses a term, a predicate, a type, a set
 *    or a range with a state machine.
 *
 *  The distinction between term and predicate is not possible since a
 *    predicate can encounter terms. Hence \c p defined by <tt>a <= b</tt>
 *    requires \c a to be a term whereas \c p define by <tt>a || b</tt> requires
 *    the subexpression \c a to be a predicate. \n
 *  The distinction between term and type is not possible since a term can
 *    be casted with a C cast. Hence \c t defined by <tt>(a) b</tt> requires
 *    \c a to be a type whereas \c t defined by <tt>(a) + b</tt> requires
 *    \c a to be a term. \n
 *  The distinction between a term and set and range is not possible since ACSL
 *    authorize the implicit conversion between a value and a singleton. \n \n
 *
 *  The state is defined by the Parser::State::point() method and has
 *    additional information within the fields _operatorStack, _qualification,
 *    _labelOrIdentifier, _declContext, _doesRequireValue. \n \n
 *  Depending on _possibleTypeResults, the local parsing method readToken
 *    builds a term for extractTerm, extractTermOrSet or a set for extractSet,
 *    extractTermOrSet or a predicate for extractPredicate. For a type, the
 *    caller has to verify if the result is a type with the isType() method
 *    before calling extractType().
 */
class TermOrPredicate
    : public ::Parser::Base::RuleResult, public ::Parser::Base {
  // + set (including range) + type
private:
  typedef ::Parser::Base::RuleResult inherited;
protected:
  typedef ::Parser::Base::RuleResult RuleResult;
private:
  term _node; //!< Can hold the parsed term for the extractTerm() method.
  predicate_named _predicate;
    //!< Can hold the parsed predicate for the extractPredicate() method.
  location _loc; //!< location range of the term, predicate or type.
  void absorbLoc(location l) { if (_loc) free_location(_loc); _loc = l; }
  logic_type _typeResult;
    //!< Hold the parsed logic_type for the extractType method.

  // logic_type _type; // NULL for predicates = Boolean
  // /* string */ list _names;

  /*! @class Operator
   *  @brief class used as element of the _operatorStack field to explicitly
   *    have a stack parsing the expressions.
   *
   *  When the parser encounters an Operator with a high Precedence, it pushes
   *    it. When it encounters an Operator with a low Precedence, it pops and
   *    reduces the previous stacked Operators until the last Operator has a
   *    lower Precedence. \n
   *  The Operator class handles unary prefix operators, binary operators,
   *    and ternary operators, function calls. The field _leftSubExpressions
   *    is an indication of how many subterms are lacking.
   */
  class Operator {
  private:
    /* operator precedence:
      ->[1] naming ':'
      ->[2] binding 'forall' 'exists' 'let'
      ->[3] conditional expression ? :
      ->[...] assignment expression =, +=, ...
      ->[4] '<==>'
      ->[5] '==>'
      ->[6] '||'
      ->[7] '^^'
      ->[8] '&&'
      ->[9] '<-->'
      ->[10] '-->'
      ->[11] '|'
      ->[12] '^'
      ->[13] '&'
      ->[14] '==' | '!='
      ->[15] '<' | '>' | "<=" | '>='
      ->[16] '<<' | '>>'
      ->[17] '+' | '-'
      ->[18] '*' | '/' | '%'
      ->[19] casts
      ->[20] unary '&' | '*' | '+' | '-' | '~' | '!'
      ->[21] prefix '++' | '--'
      ->[22] postfix '++' | '--' | '->' | '.' | '[]' | '()' | 'with'
      ->[23] constant | identifier | '('term_node')'
    */

    enum Precedence
      { PUndefined, PNaming, PBinding, PConditional, PLogicalEquiv,
        PLogicalImply, PLogicalOr, PLogicalXOr, PLogicalAnd, PBitEquiv,
        PBitImply, PBitOr, PBitExclusiveOr, PBitAnd, PEquality, PComparison,
        PShift, PAddition, PMultiplication, PCast, PUnary, PPrefix, PPostFix
      };
    enum Type
      { TUndefined, TPlus, TMinus, TTimes, TDivide, TModulo, TLeftShift,
        TRightShift, TEqual, TDifferent, TLessOrEqual, TGreaterOrEqual, TLess,
        TGreater, TLogicalAnd, TLogicalOr, TLogicalImply, TLogicalEquiv,
        TLogicalXOr, TBitAnd, TBitOr, TBitImply, TBitEquiv, TBitXOr,
        TUnaryPlus,
        TUnaryMinus, TNot, TComplement, TDereference, TAddressOf, TCast,
        TSubType, TCoerce, TNaming, TStructAccess, TArrowStructAccess,
        TIndirectMethodAccess, TArrowIndirectMethodAccess, TArrayAccess, TCall,
        TStructCall, TArrowStructCall, TForall, TExists, TLet, TConditional
      };

    Precedence _precedence; 
    //!< enable to sort the operator by their Precedence.

    Type _type; //!< Extract type of the operator.
    bool isOverloadable() const
      { return (_type >= TPlus && _type <= TDereference)
          || (_type >= TSubType && _type <= TCoerce)
          || (_type == TArrowStructAccess)
          || (_type == TArrayAccess);
      }
    DLexer::OperatorPunctuatorToken queryOperatorToken() const;

    // typ _ctypeCast; // if C-expr are integrated
    logic_type _typeCast; //!< Type of the cast for _type == TCast
    int _leftSubExpressions; //!< Number of lacking subterms.
    bool _isRightAssociative;
      //!< Indicates if the operator is right associative.
    logic_type _ltypeFirstArgument;
      //!< Type of _tfirstArgument => for implicit cast
    // expression _cfirstArgument;
    term _tfirstArgument; //!< First term for non-unary prefix operators
    predicate_named _pfirstArgument;
      //!< First predicate for non-unary prefix operators
    logic_type _ltypeSecondArgument;
      //!< Type of _tsecondArgument => for implicit cast
    term _tsecondArgument; //!< Second term for ternary operators
    predicate_named _psecondArgument; //! Second predicate for ternary operators
    logic_type _ltypeThirdArgument;
      //!< Type of _tthirdArgument => for implicit cast
    term _tthirdArgument;
      //!< Third term for ternary operators like with [array index]
    predicate_named _pthirdArgument;
      //!< Third predicate for ternary operators like with [array index]
    location _startLocation; //!< Location of the operator if needed

    // bool _isVariable; // optional constant evaluation => for array size
    // bool _isFirstLValue;  // optional => automatic translation into RValue
    // bool _isSecondLValue; // optional => automatic translation into RValue
    GlobalContext::NestedContext* _identifier;
      //!< Qualification for function call as instance
    std::list<std::pair<logic_type, term> > _arguments;
      //!< Arguments of a function/method call
    /* logic_label */ list _labelsArguments;
      //!< labels for a logic_function call
    struct Relation {
      Type _type;
      logic_type _ltype;
      term _node;

      Relation(Type type, logic_type ltype, term node)
        : _type(type), _ltype(ltype), _node(node) {}
    };
    std::list<Relation> _endRelationList;
      //!< End of a relation for predicates like <tt>a <= b <= c</tt>
    std::string _fieldName; //!< Name of a field, a function call.
    /* logic_var_def */ list _binders; //!< binders for exists, forall operators

    friend class TermOrPredicate;

  public:
    Operator()
      : _precedence(PUndefined), _type(TUndefined), _typeCast(NULL),
        _leftSubExpressions(0), _isRightAssociative(false),
        _ltypeFirstArgument(NULL), _tfirstArgument(NULL), _pfirstArgument(NULL),
        _ltypeSecondArgument(NULL), _tsecondArgument(NULL),
        _psecondArgument(NULL), _ltypeThirdArgument(NULL),
        _tthirdArgument(NULL), _pthirdArgument(NULL), _startLocation(NULL),
        _identifier(NULL), _labelsArguments(NULL), _binders(NULL)
        // , _isVariable(false), _isFirstLValue(false), _isSecondLValue(false)
      {}
    // C++-11 makes possible the copy/destruction
    //   of _firstArgument and _secondArgument in the STL.
    Operator(const Operator& source)
      : _precedence(source._precedence), _type(source._type),
        _typeCast(source._typeCast),
        _leftSubExpressions(source._leftSubExpressions),
        _isRightAssociative(source._isRightAssociative),
        _ltypeFirstArgument(source._ltypeFirstArgument),
        _tfirstArgument(source._tfirstArgument),
        _pfirstArgument(source._pfirstArgument),
        _ltypeSecondArgument(source._ltypeSecondArgument),
        _tsecondArgument(source._tsecondArgument),
        _psecondArgument(source._psecondArgument),
        _ltypeThirdArgument(source._ltypeThirdArgument),
        _tthirdArgument(source._tthirdArgument),
        _pthirdArgument(source._pthirdArgument),
        _startLocation(source._startLocation),
        /*_isVariable(source._isVariable),
          _isFirstLValue(source._isFirstLValue),
          _isSecondLValue(source._isSecondLValue), */
        _identifier(source._identifier),
        _arguments(source._arguments),
        _labelsArguments(source._labelsArguments),
        _endRelationList(source._endRelationList),
        _fieldName(source._fieldName), _binders(source._binders)
      {}
    ~Operator() {}

    void extractLastArgument(logic_type& ltargument, term& targument,
        predicate_named& pargument /* , bool& isRValue, int* intResult,
        double* doubleResult*/);
    void extractSecondArgument(logic_type& ltargument, term& targument,
        predicate_named& pargument /* , bool& isRValue, int* intResult,
        double* doubleResult*/);
    void extractFirstArgument(logic_type& ltargument, term& targument,
        predicate_named& pargument /* , bool& isRValue, int* intResult,
        double* doubleResult*/);
    void retrieveFirstArgument(logic_type& ltargument, term& targument,
        predicate_named& pargument);
    void retrieveSecondArgument(logic_type& ltargument, term& targument,
        predicate_named& pargument);
    // bool isFirstRValue() const { return !_isFirstLValue; }
    // bool isFirstLValue() const { return _isFirstLValue; }
    // bool isSecondRValue() const { return !_isSecondLValue; }
    // bool isSecondLValue() const { return _isSecondLValue; }
    Precedence getPrecedence() const { return _precedence; }

    int queryArgumentsNumber() const;
    void addArgument(logic_type ltype, term node)
      { _arguments.push_back(std::make_pair(ltype, node)); }
    void setField(const std::string& fieldName) { _fieldName = fieldName; }
    Operator& setType(Type type, bool isPrefix=false);
    Type getType() const { return _type; }
    bool isBinaryOperator() const
      { return _type >= TPlus && _type <= TBitXOr; }
    bool isRelation() const { return _type >= TEqual && _type <= TGreater; }
    std::string queryOperatorName() const;
    Operator& absorbTypeCast(logic_type typeCast)
      { assert(!_typeCast);
        _typeCast = typeCast;
        _type = TCast;
        return *this;
      }
    logic_type extractTypeCast()
      { logic_type result = _typeCast; _typeCast = NULL; return result; }
    bool changeTypeToCallAccess(Parser::Arguments& context);
    
    Operator& setLeftSubExpressions(int leftSubExpressions)
      { _leftSubExpressions = leftSubExpressions; return *this; }
    bool isFinished() const {
      if (isRelation() && !_endRelationList.empty()) {
        return _endRelationList.back()._node;
      }
      return _leftSubExpressions == 0; 
    }
    bool BinaryOperatorHasSecondArgument() {
      if (isRelation() && !_endRelationList.empty()) {
        return _endRelationList.back()._node;
      }
      return _tsecondArgument || _psecondArgument;
    }
    void advance() { assert(_leftSubExpressions > 0); _leftSubExpressions--; }
    bool isLeftAssociative() { return !_isRightAssociative; }
    bool isRightAssociative() { return _isRightAssociative; }
    // bool isConstant() const { return !_isVariable; }
    // bool isVariable() const { return _isVariable; }
    bool isCast() const { return _typeCast != NULL; }
    bool isValid() const { return _precedence != PUndefined; }
    // void setVariable() { _isVariable = true; }
    int getLeftSubExpressions() const { return _leftSubExpressions; }
    void setLocation(location loc)
      { assert(!_startLocation);
        _startLocation = loc; 
      }
    void changeLocation(location loc)
      { if (_startLocation && loc != _startLocation)
          free_location(_startLocation);
        _startLocation = loc; 
      }
    Operator& setFirstArgument(logic_type ltype, term expression,
        predicate_named pred /* , bool isRValue, bool isConstant,
        int* intArgument=NULL, double* doubleArgument = NULL*/);
    Operator& setSecondArgument(logic_type ltype, term expression,
        predicate_named pred /* , bool isRValue, bool isConstant,
        int* intArgument=NULL, double* doubleArgument = NULL*/);
    Operator& setThirdArgument(logic_type ltype, term expression,
        predicate_named pred /* , bool isRValue, bool isConstant,
        int* intArgument=NULL, double* doubleArgument = NULL*/);
    Operator& setIdentifier(GlobalContext::NestedContext* identifier)
      { _identifier = identifier; return *this; }
    Operator& setBinders(/* logic_var_def */ list binders)
      { _binders = binders; return *this; }
  };
  std::list<Operator> _operatorStack;
    //!< first part of the term expression, sorted by increasing Precedence.
  GlobalContext::NestedContext* _qualification;
    //!< Qualification of the expected identifier.
  std::string _labelOrIdentifier;
    //!< Stored identifier to determine if it is a label or a variable.
  location _startLocation;
    //!< Start location of our term/predicate if needed
  const clang::DeclContext* _declContext;
    //!< clang scope context
  bool _doesRequireValue;
    //!< Does the parser need a term/predicate to complete the parsing.
  bool _doesStopTypeAmbiguity;
    //!< Does the parser stop after it desambiguates a type from a term.

protected:
  enum TypeResult { LTRTerm, LTRPredicate, LTRType, LTRSet }; 
  unsigned short _possibleTypeResults;
    //!< Possible expected types of results.
  
  unsigned getSubExpressionPossibleTypes() const
    { unsigned result = _possibleTypeResults;
      if ((result & ~(1U << LTRType)) == 0)
        return result;
      result |= ((1U << LTRTerm) | (1U << LTRPredicate));
      // pred ? term : term // pred can be a subtype of term
      // pred ? set : set   // pred can be a subtype of set
      // term <= term       // term can be a subtype of pred
      // term .. term       // term can be a direct subtype of set
      return result;
    }
  bool acceptSubExpressionTerm()
    { return _possibleTypeResults & ~(1U << LTRType); }
  bool acceptSubExpressionPredicate()
    { return _possibleTypeResults & ~(1U << LTRType); }
  bool acceptSubExpressionSet()
    { return _possibleTypeResults & ~(1U << LTRType); }
  bool acceptSubExpressionType()
    { return _possibleTypeResults & (1U << LTRType); }
  bool excludeTypeAsResult()
    { bool result = _possibleTypeResults & ~(1U << LTRType);
      if (result)
        _possibleTypeResults &= ~(1U << LTRType);
      return result;
    }
  bool ensureTypeAsResult()
    { bool result = _possibleTypeResults & (1U << LTRType);
      if (result)
        _possibleTypeResults = (1U << LTRType);
      return result;
    }

public:
  Operator& pushOperator(Operator::Type typeOperator, int leftSubExpressions,
      Parser::Arguments& context, bool& hasFailed);

  static term tinteger(location loc, unsigned long v) {
    std::ostringstream buf;
    buf << v;
    return
      term_cons(
        term_node_TConst(logic_constant_LCInt(strdup(buf.str().c_str()))),
        copy_loc(loc), NULL);
  }

  static term tzero(location loc) { return tinteger(loc,0); }
  static term tone (location loc) { return tinteger(loc,1); }

  static bool isCArray(const term& argument,const logic_type ltype,
    Parser::Arguments& context);
  static bool isLogicZero(const term& argument);
  static bool isLogicStrictNull(const term& argument);
  static bool isLogicNull(const term& argument)
    { return isLogicZero(argument) || isLogicStrictNull(argument); }
  static logic_type computeType(term_node node);
  static bool needLogicCast(logic_type oldType, logic_type newType);
  static term makeLogicStartOf(term node, Parser::Arguments& context);
  static bool isCType(logic_type ltype);
  static bool isCPointerType(logic_type ltype, Parser::Arguments& context);
  static bool isCReferenceType(logic_type ltype, Parser::Arguments& context);
  static bool isCArrayType(logic_type ltype, Parser::Arguments& context);
  static qualified_name makeCCompoundType(logic_type ltype,
      Parser::Arguments& context, tkind* templateKind);
  static bool isIntegralType(logic_type ctype, Parser::Arguments& context);
  static bool isSignedInteger(logic_type ctype, Parser::Arguments& context);
  static bool isPlainBooleanType(logic_type ctype, Parser::Arguments& context);
  /// convert boolean or integral term to predicate
  static predicate_named convertTermToPredicate(
    logic_type,term,Parser::Arguments&);
  static bool isArithmeticType(logic_type ctype, Parser::Arguments& context);
  static bool isFloatingType(logic_type ctype, Parser::Arguments& context);
  static logic_type logicArithmeticPromotion(logic_type source,
      Parser::Arguments& context);
  static qualified_name getClassType(logic_type ltype,
      tkind* templateParameters=NULL);
  static term typeBoolTerm(logic_type& ltype, term source,
      Parser::Arguments& context);
  static void addOffset(term_offset& source, term_offset shift);
  static term makeMemoryShift(logic_type ltype, term source, term_offset shift,
      location loc, logic_type& resultType, Parser::Arguments& context);
  static term termLValAddressOf(logic_type ltype, term source, location loc,
      logic_type& lresultType, Parser::Arguments& context);
  static bool retrieveTypeOfField(logic_type structType,
       const std::string& fieldName, term_offset& offset, logic_type& ltype,
       Parser::Arguments& context);
  static term makeDot(term source, location loc, term_offset offset,
      Parser::Arguments& context);
  static term makeMemory(term address, term_offset offset);
  static term makeShift(term memoryAccess, logic_type laccessType,
      term shift, location loc, Parser::Arguments& context);
  static logic_type logicArithmeticConversion(logic_type t1, logic_type t2,
      Parser::Arguments& context);
  static logic_type integralPromotion(logic_type ltype,
      Parser::Arguments& context);
  static logic_type carithmeticConversion(logic_type first, logic_type second,
      Parser::Arguments& context);
  static logic_type conditionalConversion(logic_type first, logic_type second,
      Parser::Arguments& context);
  static bool hasImplicitConversion(logic_type ltypeResult, term node,
      logic_type ltype, Parser::Arguments& context);
  static bool isLogicVoidPointerType(logic_type ltype,
      Parser::Arguments& context);

  class SubstitutionLevel;
  class Substitution;
  static bool isSameType(logic_type lfirst, logic_type lsecond,
      Substitution substitutionFirst, Substitution substitutionSecond,
      Parser::Arguments& context);
  /*! Checks whether lsecond is compatible with lfirst, modulo instantiation
    of some type variables if needed.
    returns instantiated first type if both are compatible, NULL otherwise
  */
  static logic_type isCompatibleType(logic_type lfirst, logic_type lsecond,
      Substitution substitutionFirst, Substitution substitutionSecond,
      Parser::Arguments& context);
  static bool isIntegralType(logic_type type, Substitution substitution,
      Parser::Arguments& context);
  static bool isPlainPointerType(logic_type type, Substitution substitution,
      Parser::Arguments& context);
  static bool isPlainArrayType(logic_type type, Substitution substitution,
      Parser::Arguments& context);
  static qualified_name makePlainCompoundType(logic_type type,
      Substitution substitution, Parser::Arguments& context,
      tkind* templateKind);
  static bool isPointerType(logic_type ltype, Substitution substitution,
      Parser::Arguments& context);
  static bool isArrayType(logic_type ltype, Substitution substitution,
      Parser::Arguments& context);
  static qualified_name makeCompoundType(logic_type type,
      Substitution substitution, Parser::Arguments& context,
      tkind* templateKind);
  static logic_type typeOfPointed(logic_type type, Substitution substitution,
      Parser::Arguments& context);
  static logic_type typeOfArrayElement(logic_type ltype,
      Substitution substitution, Parser::Arguments& context);
  static bool isPointerCharType(logic_type type, Substitution substitution,
      Parser::Arguments& context);
  static term logicCoerce(logic_type& ltype, term source);
  static logic_type isSetType(logic_type ltype);
  /*! tries to coerce the given node of type ltype into ltypeResult.
    if isOverloaded is true, no error is raised if the conversion fails.
    returns NULL in case the conversion fails. Note that an _implicit_
    conversion always go from a smaller type into a bigger one. Casts from
    e.g. long to int or double to float have to be inserted explicitly by
    the user.
  */
  static term implicitConversion(
    logic_type& ltypeResult,
    /*!< the expected targetted type. It may be simplified.
         implicitConversion takes its ownership and gives it back at the end.
         As a consequence ltypeResult is different from NULL at the end.
         If ltypeResult shall not change (ex if present in a signature),
         the caller should use fresh logic_types. If ltypeResult is allowed
         to change to find a common target type between two arguments, the
         caller should directly use ltypeResult.
     */
    term node,
    /*!< the term that should be converted to ltypeResult. implicitConversion
         takes its ownership. The resulting term is likely to include node
         as a subterm of the conversion.
     */
    logic_type ltype,
    /*!< the actual type of node. implicitConversion takes its ownership. */
    bool isOverloaded, /*!< if true, indicates that we are trying to select
                         an instance of an overloaded operator, so that we
                         shouldn't output an error message if the conversion
                         is not possible, since another instance might match.*/
    Substitution substitutionFirst, /*!< instantiations of type variables
                                      occurring in ltypeResult. */
    Substitution substitutionSecond, /*!< instantiations of type variables
                                       occurring in ltype. */
    Parser::Arguments& context, /*!< information about compilation context. */
    bool emitMsg = true
  );

  static term implicitConversion(logic_type& ltypeResult, term node,
      logic_type ltype, bool isOverloaded, Parser::Arguments& context);
  static term makeCast(logic_type& ltype, term source, logic_type oldtype,
      Substitution substitutionThis, Substitution substitutionSource,
      Parser::Arguments& context);

protected:
  Operator& queryLastOperator() { return _operatorStack.back(); }
  static void setLastArgument(Operator& operation, logic_type ltype,
      term targument, predicate_named pargument /* , bool isRValue,
      bool isConstant, int* intArgument=NULL, double* doubleArgument=NULL*/);
  void pushLastArgument(logic_type ltype, term targument,
      predicate_named pargument /* , bool isRValue, bool isConstant,
      int* intArgument=NULL, double* doubleArgument=NULL*/);
  Operator& pushPrefixUnaryOperator(Operator::Type typeOperator, location loc)
    { _operatorStack.push_back(Operator());
      Operator& result = _operatorStack.back();
      result.setType(typeOperator, true).setLeftSubExpressions(1);
      result.setLocation(loc);
      return result;
    }
  Operator& pushPrefixBinaryOperator(Operator::Type typeOperator, location loc)
    { _operatorStack.push_back(Operator());
      Operator& result = _operatorStack.back();
      result.setType(typeOperator, true).setLeftSubExpressions(2);
      result.setLocation(loc);
      return result;
    }
  Operator& pushBinaryOperator(Operator::Type typeOperator,
      Parser::Arguments& context, bool& hasFailed)
    { return pushOperator(typeOperator, 1, context, hasFailed); }
  Operator& pushConditionalOperator(Parser::Arguments& context, bool& hasFailed)
    { return pushOperator(Operator::TConditional, 2, context, hasFailed); }
  Operator& pushPostfixUnaryOperator(Operator::Type typeOperator,
      Parser::Arguments& context, bool& hasFailed)
    { return pushOperator(typeOperator, 0, context, hasFailed); }
  Operator& pushCastOperator(logic_type typeCast, location loc)
    { _operatorStack.push_back(Operator());
      Operator& result = _operatorStack.back();
      result.setType(Operator::TCast).absorbTypeCast(typeCast)
          .setLeftSubExpressions(1);
      result.setLocation(loc);
      return result;
    }

  class GuardLogicType;
  class GuardType;
  class GuardTerm;
  class TermOrPredicateMemoryExtension;
  class TermOrPredicateList;
  static term applyTermCast(
      logic_type& ccastType,
      /*!< the cast type. applyTermCast takes its ownership and put NULL
           in it to avoid some "memory bugs" at the caller site.
       */
      term targument,
      /*!< the term that should be converted to ltypeResult. applyTermCast
           takes its ownership. The resulting term is likely to include node
           as a subterm of the conversion.
       */
      logic_type ltype,
      /*!< the actual type of targument. applyTermCast takes its ownership. */
      Parser::Arguments& context);

  static void applyOverloadOperatorIfAny(Operator& operation,
      Parser::Arguments& context);
  
  typedef GlobalContext::OverloadedLogicFunctions::Functions Functions;

  /*!
    selects the most precise signature among a list of overloaded functions.
    returns NULL in case of ambiguity.
   */
  static logic_info disambiguate(
    const std::string& name, const Functions&, Parser::Arguments&);
  // returns the list of arguments for the given call operation
  // adding the this pointer if needed.
  static list
    create_argument_list(Operator& operation, logic_info f, 
                         Parser::Arguments& context);
  static bool apply(Operator& operation, logic_type& ltypeResult,
      term& expressionResult, predicate_named& predicateResult,
      /* bool& isRValue, bool& isConstant, int *intResult, double* doubleResult,
      */ Parser::Arguments& context, unsigned& possibleTypes);

  bool clearStack(logic_type& ltypeResult, term& expressionResult,
      predicate_named& predicateResult /* , bool& isRValue, bool& isConstant,
      int* intResult, double* doubleResult*/, Parser::Arguments& context);

  class Binders;
  class WithConstruct;
  class Range;
  class SetComprehension;
  friend class Binders;
  friend class WithConstruct;
  friend class Range;
  friend class SetComprehension;

public:
  TermOrPredicate()
    : _node(NULL), _predicate(NULL), _loc(NULL), _typeResult(NULL),
      /* _type(NULL), _names(NULL), */ _qualification(NULL),
      _startLocation(NULL), _declContext(NULL), _doesRequireValue(true),
      _doesStopTypeAmbiguity(false),
      _possibleTypeResults((1U << LTRTerm) | (1U << LTRPredicate)) {}
  TermOrPredicate(const TermOrPredicate& source)
    : RuleResult(source), _node(NULL), _predicate(NULL), _loc(NULL),
      _typeResult(NULL), /* _type(NULL), _names(NULL), */ _qualification(NULL),
      _startLocation(NULL), _declContext(NULL), _doesRequireValue(true),
      _doesStopTypeAmbiguity(false),
      _possibleTypeResults(source._possibleTypeResults) {}
  ~TermOrPredicate()
    { if (_loc) { free_location(_loc); _loc = NULL; };
      if (_startLocation)
        { free_location(_startLocation); _startLocation = NULL; }
      if (_node) { free_term(_node); _node = NULL; };
      if (_predicate) { free_predicate_named(_predicate); _predicate = NULL; };
      if (_typeResult) { free_logic_type(_typeResult); _typeResult = NULL; };
    }

  void setStopOnTypeDesambiguition() { _doesStopTypeAmbiguity = true; }
    // foresee to merge the _operatorStack = for SetComprehension.
  TermOrPredicate& setPredicate()
    { _possibleTypeResults &= (1U << LTRPredicate); return *this; }
  TermOrPredicate& setTerm()
    { _possibleTypeResults &= (1U << LTRTerm); return *this; }
  TermOrPredicate& setSet()
    { _possibleTypeResults &= (1U << LTRSet); return *this; }
  TermOrPredicate& setType()
    { _possibleTypeResults &= (1U << LTRType);
      return *this;
    }
  virtual RuleResult* clone() const { return new TermOrPredicate(*this); }
  /// the only ambiguous states where all results may be possible are Begin
  /// and AfterLogicIdentifier.
  /// To conform with LALR(1) rules, the state AfterLogicIdentifier should
  /// correspond to a special class QualifiedIdentifier.
  ReadResult readToken(Parser::State& state, Parser::Arguments& argument);
  void clear()
    { assert(_operatorStack.empty());
      if (_loc) {
        _loc->linenum1 = _loc->linenum2;
        _loc->charnum1 = _loc->charnum2;
      };
      /* _type = NULL; */ _doesRequireValue = true;
      _doesStopTypeAmbiguity = false;
      if (_node) { free_term(_node); _node = NULL; };
      if (_predicate) { free_predicate_named(_predicate); _predicate = NULL; };
      if (_typeResult) { free_logic_type(_typeResult); _typeResult = NULL; };
    }

  bool isTerm(Parser::Arguments& arguments);
  bool isSureTerm(Parser::Arguments& arguments);
  bool isSet(Parser::Arguments& arguments);
  bool isSureSet(Parser::Arguments& arguments);
  bool isPredicate(Parser::Arguments& arguments);
  bool isSurePredicate(Parser::Arguments& arguments);
  bool isType() const;
  term extractTerm(Parser::Arguments& arguments);
  term extractTerm(Parser::Arguments& arguments, logic_type& ltype);
  term extractTermOrSet(Parser::Arguments& arguments, logic_type& ltype);
  term extractSet(Parser::Arguments& arguments, logic_type& ltype);
  void extractTermOrPredicate(Parser::Arguments& arguments,
      logic_type& ltype, term& node, predicate_named& pred);
  predicate_named extractPredicate(Parser::Arguments& arguments);
  logic_type extractType();
  location getLocation() const { return _loc; }
  static term term_true(location loc)
    { return term_cons(term_node_TTrue(),copy_loc(loc),NULL); }
  static term term_false(location loc)
    { return term_cons(term_node_TFalse(),copy_loc(loc),NULL); }
};

inline void
TermOrPredicate::Operator::extractLastArgument(logic_type& ltargument,
    term& targument, predicate_named& pargument
    /* , bool& isRValue, int* intResult, double* doubleResult*/)
{ ++_leftSubExpressions;
  if (isRelation() && !_endRelationList.empty()) {
    ltargument = _endRelationList.back()._ltype;
    _endRelationList.back()._ltype = NULL;
    targument = _endRelationList.back()._node;
    _endRelationList.back()._node = NULL;
    assert(targument);
    pargument = NULL;
  }
  else if (_tthirdArgument != NULL || _pthirdArgument != NULL) {
    // if (intResult)
    //   *intResult = _thirdArgument->intArgument();
    // if (doubleResult)
    //   *doubleResult = _thirdArgument->doubleArgument();
    ltargument = _ltypeThirdArgument;
    _ltypeThirdArgument = NULL;
    targument = _tthirdArgument;
    _tthirdArgument = NULL;
    pargument = _pthirdArgument;
    _pthirdArgument = NULL;
    // isRValue = !_isThirdLValue;
  }
  else if (_tsecondArgument != NULL || _psecondArgument != NULL) {
    // if (intResult)
    //   *intResult = _secondArgument->intArgument();
    // if (doubleResult)
    //   *doubleResult = _secondArgument->doubleArgument();
    ltargument = _ltypeSecondArgument;
    _ltypeSecondArgument = NULL;
    targument = _tsecondArgument;
    _tsecondArgument = NULL;
    pargument = _psecondArgument;
    _psecondArgument = NULL;
    // isRValue = !_isSecondLValue;
  }
  else {
    // if (intResult)
    //   *intResult = _firstArgument->intArgument();
    // if (doubleResult)
    //   *doubleResult = _firstArgument->doubleArgument();
    ltargument = _ltypeFirstArgument;
    _ltypeFirstArgument = NULL;
    targument = _tfirstArgument;
    _tfirstArgument = NULL;
    pargument = _pfirstArgument;
    _pfirstArgument = NULL;
    // isRValue = !_isFirstLValue;
  };
}

inline void
TermOrPredicate::Operator::extractSecondArgument(logic_type& ltargument,
    term& targument, predicate_named& pargument
    /* , bool& isRValue, int* intResult, double* doubleResult*/)
{ ++_leftSubExpressions;
  assert(_tthirdArgument == NULL && _pthirdArgument == NULL);
  assert(_tsecondArgument != NULL || _psecondArgument != NULL);
  // if (intResult)
  //   *intResult = _secondArgument->intArgument();
  // if (doubleResult)
  //   *doubleResult = _secondArgument->doubleArgument();
  ltargument = _ltypeSecondArgument;
  _ltypeSecondArgument = NULL;
  targument = _tsecondArgument;
  _tsecondArgument = NULL;
  pargument = _psecondArgument;
  _psecondArgument = NULL;
  // isRValue = !_isSecondLValue;
}

inline void
TermOrPredicate::Operator::extractFirstArgument(logic_type& ltargument,
    term& targument, predicate_named& pargument
    /* , bool& isRValue, int* intResult, double* doubleResult*/)
{ ++_leftSubExpressions;
  assert(_tthirdArgument == NULL && _pthirdArgument == NULL);
  assert(_tsecondArgument == NULL && _psecondArgument == NULL);
  assert(_tfirstArgument != NULL || _pfirstArgument != NULL);
  // if (intResult)
  //   *intResult = _firstArgument->intArgument();
  // if (doubleResult)
  //   *doubleResult = _firstArgument->doubleArgument();
  ltargument = _ltypeFirstArgument;
  _ltypeFirstArgument = NULL;
  targument = _tfirstArgument;
  _tfirstArgument = NULL;
  pargument = _pfirstArgument;
  _pfirstArgument = NULL;
  // isRValue = !_isFirstLValue;
}

inline void
TermOrPredicate::Operator::retrieveFirstArgument(logic_type& ltargument,
    term& targument, predicate_named& pargument) {
  assert(_tfirstArgument != NULL || _pfirstArgument != NULL);
  ltargument = _ltypeFirstArgument;
  targument = _tfirstArgument;
  pargument = _pfirstArgument;
}

inline void
TermOrPredicate::Operator::retrieveSecondArgument(logic_type& ltargument,
    term& targument, predicate_named& pargument) {
  assert(_tsecondArgument != NULL || _psecondArgument != NULL);
  ltargument = _ltypeSecondArgument;
  targument = _tsecondArgument;
  pargument = _psecondArgument;
}

inline int
TermOrPredicate::Operator::queryArgumentsNumber() const
{ int result = 0;
  if (_type >= TPlus && _type <= TBitXOr)
    result = 2;
  else if (_type == TCall)
    result = 1 + _arguments.size();
  // TArrayAccess has 2 arguments, but it is handled as if it has only one
  // (the second one being found in the _arguments list)
  else if (_type == TArrayAccess)
    result = 1;
  else if (_type >= TUnaryPlus && _type < TCall)
    result = 1;
  else if (_type == TConditional)
    result = 3;
  else if (_type == TForall || _type == TExists)
    result = 1;
  return result;
}

inline TermOrPredicate::Operator&
TermOrPredicate::Operator::setFirstArgument(logic_type ltype, term expression,
    predicate_named pred /* , bool isRValue, bool isConstant,
    int* intArgument=NULL, double* doubleArgument = NULL*/)
{ // if (intArgument)
  //   _firstArgument->intArgument() = *intArgument;
  // if (doubleArgument)
  //   _firstArgument->doubleArgument() = *doubleArgument;
  _ltypeFirstArgument = ltype;
  _tfirstArgument = expression;
  _pfirstArgument = pred;
  // _isFirstLValue = !isRValue;
  // if (!isConstant)
  //   _isVariable = true;
  return *this;
}

inline TermOrPredicate::Operator&
TermOrPredicate::Operator::setSecondArgument(logic_type ltype, term expression,
    predicate_named pred /* , bool isRValue, bool isConstant,
    int* intArgument=NULL, double* doubleArgument = NULL*/)
{ // if (intArgument)
  //   _secondArgument.intArgument() = *intArgument;
  // if (doubleArgument)
  //   _secondArgument.doubleArgument() = *doubleArgument;
  _ltypeSecondArgument = ltype;
  _tsecondArgument = expression;
  _psecondArgument = pred;
  // _isSecondLValue = !isRValue;
  // if (!isConstant)
  //   _isVariable = true;
  return *this;
}

inline TermOrPredicate::Operator&
TermOrPredicate::Operator::setThirdArgument(logic_type ltype, term expression,
    predicate_named pred /* , bool isRValue, bool isConstant,
    int* intArgument=NULL, double* doubleArgument = NULL*/)
{ // if (intArgument)
  //   _thirdArgument.intArgument() = *intArgument;
  // if (doubleArgument)
  //   _thirdArgument.doubleArgument() = *doubleArgument;
  _ltypeThirdArgument = ltype;
  _tthirdArgument = expression;
  _pthirdArgument = pred;
  // _isThirdLValue = !isRValue;
  // if (!isConstant)
  //   _isVariable = true;
  return *this;
}

inline void
TermOrPredicate::setLastArgument(Operator& operation, logic_type ltype,
    term targument, predicate_named pargument /* , bool isRValue,
    bool isConstant, int* intArgument=NULL, double* doubleArgument=NULL*/)
{ if (operation._tfirstArgument == NULL && operation._pfirstArgument == NULL) {
    operation._ltypeFirstArgument = ltype;
    operation._tfirstArgument = targument;
    operation._pfirstArgument = pargument;
    // operation._isFirstLValue = !isRValue;
    // if (!isConstant)
    //   operation._isVariable = true;
    // if (intArgument)
    //   operation._firstArgument->intArgument() = *intArgument;
    // if (doubleArgument)
    //   operation._firstArgument->doubleArgument() = *doubleArgument;
  }
  else if (operation._tsecondArgument == NULL
      && operation._psecondArgument == NULL) {
    assert(operation._tsecondArgument == NULL
        && operation._psecondArgument == NULL);
    operation._ltypeSecondArgument = ltype;
    operation._tsecondArgument = targument;
    operation._psecondArgument = pargument;
    // operation._isSecondLValue = !isRValue;
    // if (!isConstant)
    //   operation._isVariable = true;
    // if (intArgument)
    //   operation._secondArgument->intArgument() = *intArgument;
    // if (doubleArgument)
    //   operation._secondArgument->doubleArgument() = *doubleArgument;
  }
  else {
    if (operation.isRelation() && !operation._endRelationList.empty()
        && operation._endRelationList.back()._node == NULL) {
      // we know that this argument won't be used as predicate.
      if (pargument) free_predicate_named(pargument);
      operation._endRelationList.back()._ltype = ltype;
      operation._endRelationList.back()._node = targument;
    }
    else {
      assert(operation._tthirdArgument == NULL
          && operation._pthirdArgument == NULL);
      operation._ltypeThirdArgument = ltype;
      operation._tthirdArgument = targument;
      operation._pthirdArgument = pargument;
      // operation._isThirdLValue = !isRValue;
      // if (!isConstant)
      //   operation._isVariable = true;
      // if (intArgument)
      //   operation._thirdArgument->intArgument() = *intArgument;
      // if (doubleArgument)
      //   operation._thirdArgument->doubleArgument() = *doubleArgument;
    };
  };
  if (operation.isValid()) { operation.advance (); }
}

inline void
TermOrPredicate::pushLastArgument(logic_type ltype, term targument,
    predicate_named pargument /* , bool isRValue, bool isConstant,
    int* intArgument=NULL, double* doubleArgument=NULL*/)
{ assert(_doesRequireValue);
  if (_operatorStack.empty())
    _operatorStack.push_back(Operator());
  Operator& operation = _operatorStack.back();
  setLastArgument(operation, ltype, targument, pargument
      /* , isRValue, isConstant, intArgument, doubleArgument*/);
  _doesRequireValue = false;
}

inline bool
TermOrPredicate::isTerm(Parser::Arguments& arguments)
{ assert(_possibleTypeResults & (1U << LTRTerm));
  bool isOk = true;
  if (_typeResult == NULL && _node == NULL && _predicate == NULL) {
    isOk = clearStack(_typeResult, _node, _predicate, arguments);
    if (!isOk)
      _operatorStack.clear();
  };
  return isOk && _node && !isSetType(_typeResult);
}

inline bool
TermOrPredicate::isSureTerm(Parser::Arguments& arguments)
{ assert(_possibleTypeResults & (1U << LTRTerm));
  bool isOk = true;
  if (_typeResult == NULL && _node == NULL && _predicate == NULL) {
    isOk = clearStack(_typeResult, _node, _predicate, arguments);
    if (!isOk)
      _operatorStack.clear();
  };
  return isOk && _node && !isSetType(_typeResult) && !_predicate;
}

inline bool
TermOrPredicate::isSet(Parser::Arguments& arguments)
{ assert(_possibleTypeResults & (1U << LTRSet));
  bool isOk = true;
  if (_typeResult == NULL && _node == NULL && _predicate == NULL) {
    isOk = clearStack(_typeResult, _node, _predicate, arguments);
    if (!isOk)
      _operatorStack.clear();
  };
  return isOk && _node && isSetType(_typeResult);
}

inline bool
TermOrPredicate::isSureSet(Parser::Arguments& arguments)
{ assert(_possibleTypeResults & (1U << LTRSet));
  bool isOk = true;
  if (_typeResult == NULL && _node == NULL && _predicate == NULL) {
    isOk = clearStack(_typeResult, _node, _predicate, arguments);
    if (!isOk)
      _operatorStack.clear();
  };
  return isOk && _node && isSetType(_typeResult) && !_predicate;
}

inline bool
TermOrPredicate::isPredicate(Parser::Arguments& arguments)
{ assert(_possibleTypeResults & (1U << LTRPredicate));
  bool isOk = true;
  if (_typeResult == NULL && _node == NULL && _predicate == NULL) {
    isOk = clearStack(_typeResult, _node, _predicate, arguments);
    if (!isOk)
      _operatorStack.clear();
  };
  return isOk && _predicate;
}

inline bool
TermOrPredicate::isSurePredicate(Parser::Arguments& arguments)
{ assert(_possibleTypeResults & (1U << LTRPredicate));
  bool isOk = true;
  if (_typeResult == NULL && _node == NULL && _predicate == NULL) {
    isOk = clearStack(_typeResult, _node, _predicate, arguments);
    if (!isOk)
      _operatorStack.clear();
  };
  return isOk && !_node && _predicate;
}

inline bool
TermOrPredicate::isType() const
{ if (_possibleTypeResults & (1U << LTRType)) return _typeResult;
  return false;
}

inline term
TermOrPredicate::extractTerm(Parser::Arguments& arguments)
{ assert(_possibleTypeResults & (1U << LTRTerm));
  if (_typeResult == NULL && _node == NULL && _predicate == NULL)
    if (!clearStack(_typeResult, _node, _predicate, arguments))
      return NULL;
  if (!(_node && _typeResult && !isSetType(_typeResult)))
    return NULL;
  term result = _node;
  _node = NULL;
  clear();
  return result;
}

inline term
TermOrPredicate::extractTerm(Parser::Arguments& arguments, logic_type& ltype)
{ assert(acceptSubExpressionTerm());
  if (_typeResult == NULL && _node == NULL && _predicate == NULL)
    if (!clearStack(_typeResult, _node, _predicate, arguments))
      return NULL;
  if (!(_node && _typeResult && !isSetType(_typeResult)))
    return NULL;
  term result = _node;
  _node = NULL;
  ltype = _typeResult;
  _typeResult = NULL;
  clear();
  return result;
}

inline void
TermOrPredicate::extractTermOrPredicate(Parser::Arguments& arguments,
    logic_type& ltype, term& node, predicate_named& pred)
{ if (_typeResult == NULL && _node == NULL && _predicate == NULL)
    if (!clearStack(_typeResult, _node, _predicate, arguments))
      return;
  node = _node;
  _node = NULL;
  ltype = _typeResult;
  _typeResult = NULL;
  pred = _predicate;
  _predicate = NULL;
  clear();
}

inline term
TermOrPredicate::extractTermOrSet(Parser::Arguments& arguments,
    logic_type& ltype)
{ assert(_possibleTypeResults & ((1U << LTRTerm) | (1U << LTRSet)));
  if (_typeResult == NULL && _node == NULL && _predicate == NULL)
    if (!clearStack(_typeResult, _node, _predicate, arguments))
      return NULL;
  if (!(_node && _typeResult))
    return NULL;
  term result = _node;
  _node = NULL;
  ltype = _typeResult;
  _typeResult = NULL;
  clear();
  return result;
}

inline term
TermOrPredicate::extractSet(Parser::Arguments& arguments, logic_type& ltype)
{ assert(_possibleTypeResults & (1U << LTRSet));
  if (_typeResult == NULL && _node == NULL && _predicate == NULL)
    if (!clearStack(_typeResult, _node, _predicate, arguments))
      return NULL;
  if (!(_node && _typeResult && isSetType(_typeResult)))
    return NULL;
  term result = _node;
  _node = NULL;
  ltype = _typeResult;
  _typeResult = NULL;
  clear();
  return result;
}

inline predicate_named
TermOrPredicate::extractPredicate(Parser::Arguments& arguments)
{ assert(_possibleTypeResults & (1U << LTRPredicate));
  if (_typeResult == NULL && _node == NULL && _predicate == NULL)
    if (!clearStack(_typeResult, _node, _predicate, arguments))
      return NULL;
  if (!_predicate)
    return NULL;
  predicate_named result = _predicate;
  _predicate = NULL;
  clear();
  return result;
}

inline logic_type
TermOrPredicate::extractType()
{ assert(_possibleTypeResults & (1U << LTRType));
  if (!_typeResult || _node)
    return NULL;
  logic_type result = _typeResult;
  _typeResult = NULL;
  clear();
  return result;
}

} // end of namespace Acsl

#endif // ACSL_TermOrPredicateH

