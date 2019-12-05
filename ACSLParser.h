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
//   Definition of the ACSL++ parser.
//

#ifndef ACSL_ParserH

#define ACSL_ParserH

#include "ACSLLexer.h"
#include "Clang_utils.h"
#include "clang/AST/DeclCXX.h"
#include <initializer_list>

/** @file */

namespace clang {

class ASTContext;
class DeclContext;
class Sema;
class Scope;
class MacroArgs;
class Token;
class MacroInfo;

} // end of namespace clang

class RTTITable;

namespace Acsl {

/*! @class ErrorMessage
 *  @brief Represents an error message in the parser.
 *
 *  The parser Parser can stop parsing at the first error message or it can
 *    try to recover a <em>natural state</em> after an error is reported. In
 *    the last case many ErrorMessage are stored in the Parser::_errorMessages
 *    field.
 */
class ErrorMessage {
private:
  std::string _message; //!< Content of the error message.
  std::string _filePos; //!< File name in which the error occurs.
  unsigned _linePos;    //!< Line at which the error occurs.
  unsigned _columnPos;  //!< Column at which the error occurs.

public:
  ErrorMessage(const std::string& message, const std::string& filePos,
      unsigned linePos, unsigned columnPos)
    : _message(message), _filePos(filePos), _linePos(linePos),
      _columnPos(columnPos) {}
  const std::string& getMessage() const { return _message; }
  const std::string& filepos() const { return _filePos; }
  unsigned linepos() const { return _linePos; }
  unsigned columnpos() const { return _columnPos; }
};

/*! @class Parser
 *  @brief Builds a logical CIL AST from Token read by the intern Lexer
 *    _arguments._lexer.
 *
 *  The parser Parser can stop parsing at the first error message or it can
 *    try to recover a <em>natural state</em> after an error is reported. In
 *    the last case many ErrorMessage are stored in the
 *    Parser::Arguments::_errorMessages field. \n
 *  The main method is the parse method. Assumed that an initial state is
 *    provided to the constructor Parser::Parser, the parse method makes it
 *    evolve. Each time a transition is taken, a reference to a node of the CIL
 *    AST stored within the state enables to build another piece of the AST.
 */
class Parser : public ::Parser::Base {
public:
  /*! @class Arguments
   *  @brief Provides accessibility to some high-level constructs during
   *    the parsing. The selected services helps to construct local nodes in
   *    the CIL AST.
   */
  class Arguments {
  private:
    //! @name Parsing information data members
    ///@{
    Lexer _lexer; //!< lexer used to provide Token to the grammar.
    location _tokenLocation;
          //!< location of the current token _lexer.queryToken().
    clang::SourceLocation _clangLocation;
          //!< clang location of the beginning of the buffer being lexed/parsed.
    ///@}


    //    const std::string* _buffer; //!< ACSL comment being parsed
//    size_t _position; //!< Parsing position in the ACSL comment.

    //! @name Local data members to manage the parsing
    ///@{
    int _localStackHeight;
      //!< Size of the recursive calls to readToken methods.
    std::list<ErrorMessage>* _errorMessages;
      //!< Refence to the Parser::_errorMessages field.
    int _countErrors;
      //!< Number of errors to stop the parser when it is greater than 20.
    bool _doesStopOnError;
      //!< Flag to stop the parser on the first encountered error.
    ///@}

    //! @name Global parsing context coming from clang
    ///@{
    const clang::DeclContext* _clangContext; //!< clang declarative context
    const clang::ASTContext* _clangAST; //!< clang root node on the AST
    clang::Sema* _clangSema;
      //!< Reference to clang Sema to perform the name lookup
    clang::Scope* _clangScope;
      //!< clang Scope that should follow _clangContext for name lookup issues.
    ///@}

    //! @name Local context information
    ///@{
    const Clang_utils* _clang_utils; //!< utilities shared with FramaCIRGen.cpp
    const RTTITable& _rttiTable;
      //!< inheritance links between classes to manage the casts.
    GlobalContext::NestedContext* _currentLogicScope;
      //!< namespace and class scope enabling to store the logic constructs
      //!<   at the right places.
    std::map<std::string, std::list<logic_var_def> > _localBinding;
      //!< local \\let construct stored for finding the connected logic_var_def.
    std::map<std::string, logic_type> _logicFormals;
      //!< table for function formal parameters, including the implicit this.
    std::set<std::string> _logicLabels; //!< Available logic labels.

    enum { Unspecified, GlobalAnnot, FunSpec, CodeAnnot } _annotContext;
    //!< the kind of annotation we are currently parsing
    bool _result_context; //!< Can we have \\result in a term.
    bool _isVerbose; //!< Does the parsing show its internal states/transitions.
    ///@}
    friend class Parser;

    template <class TypeTraits> typename TypeTraits::ResultType isTypedefType
      (TypeTraits& traits, qualified_name name) const;
    class IsIntegralTypeTraits;
    class IsSignedTypeTraits;
    class IsArithmeticTypeTraits;
    class IsFloatingTypeTraits;
    class IsPointerTypeTraits;
    class IsReferenceTypeTraits;
    class IsArrayTypeTraits;
    class IsCompoundTypeTraits;
    class LogicArithmeticPromotionTraits;
    class MakePointedTypeTraits;
    class MakeReferencedTypeTraits;
    class MakeElementArrayTypeTraits;
    class MakeLogicTypeTraits;
    class RetrieveTypeOfFieldTraits;
    class GetRecordTypeTraits;

    bool addOverloadedLogicFunctionOrOperator(const std::string& name,
        logic_info info, bool isMethod=false,
        DLexer::OperatorPunctuatorToken::Type* codeOperator=NULL);

  public:
    Arguments(const clang::DeclContext* clangContext,
        const clang::ASTContext* clangAST, clang::Sema* clangSema,
        clang::Scope* clangScope,
        Clang_utils* clang_utils, const RTTITable& rttiTable
        )
      :
        _lexer(clangSema),
        _tokenLocation(NULL),
        _clangLocation(),
        _localStackHeight(0),
        _errorMessages(NULL),
        _countErrors(0),
        _doesStopOnError(clang_utils->stopOnAnnotError()),
        _clangContext(clangContext),
        _clangAST(clangAST),
        _clangSema(clangSema),
        _clangScope(clangScope),
        _clang_utils(clang_utils),
        _rttiTable(rttiTable),
        _currentLogicScope(clang_utils->queryDeclLogicScope(clangContext)),
        _localBinding(),
        _logicFormals(),
        _logicLabels(),
        _annotContext(Unspecified),
        _result_context(false),
        _isVerbose(clang_utils->isVerbose())
      { }

    ~Arguments()
      { std::map<std::string, std::list<logic_var_def> >::iterator
          iterEnd = _localBinding.end();
        for (std::map<std::string, std::list<logic_var_def> >::iterator
            iter = _localBinding.begin(); iter != iterEnd; ++iter) {
          std::list<logic_var_def>::iterator subiterEnd = iter->second.end();
          for (std::list<logic_var_def>::iterator
              subiter = iter->second.begin(); subiter != subiterEnd; ++subiter)
            free_logic_var_def(*subiter);
          iter->second.clear();
        };
      }


    // Getter and setter methods

    void resetAnnotContext() { _annotContext = Unspecified; }
    void setGlobalAnnotContext() { _annotContext = GlobalAnnot; }
    void setFunSpecContext() { _annotContext = FunSpec; }
    void setCodeAnnotContext() { _annotContext = CodeAnnot; }
    bool isGlobalAnnotContext() const { return _annotContext == GlobalAnnot; }
    bool isFunSpecContext() const { return _annotContext == FunSpec; }
    bool isCodeAnnotContext () const { return _annotContext == CodeAnnot; }
    void setDoesStopOnError() { _doesStopOnError = true; }
    const clang::DeclContext* getDeclContext() { return _clangContext; }
    bool isExternCContext() { return _clang_utils->isExternCContext(_clangContext); }
    const GlobalContext::NestedContext* getLogicContext() { return _currentLogicScope; }
    const Clang_utils* get_clang_utils() { return _clang_utils; }
    Lexer& lexer() { return _lexer; }
    Lexer::AbstractToken queryToken() { return _lexer.queryToken(); }
    const Lexer::AbstractToken& getContentToken() const { return _lexer.getContentToken(); }

    // Parser methods

    void shift() { ++_localStackHeight; }
    void reduce() { --_localStackHeight; }
    int getNewVarNumber() { return ++_clang_utils->logicVariableNumber(); }

    //! Adds an error message to _errorMessages with the given message
    //! and the position of the most recent lexer token
    bool addErrorMessage(const std::string& message) {
      return addErrorMessage(message, _lexer.seeTokenLocation());
    }

    //! Adds an error message to _errorMessages with the given message and location
    //!
    bool addErrorMessage(const std::string& message, location tokenLocation);

    bool doesStopAfterTooManyErrors() const
      { return (_doesStopOnError || !_errorMessages || _countErrors >= 20); } // FIXME - allow user to set this number?

    //! Moves accumulated error messages from lexer to parser
    //!
    void addErrorMessagesFromLexer();

    /**
     * @brief a shortcut function to call the lexer inside the parser.
     *
     *  With this function, call/return to the Parser::parse function are
     *  translated into goto, call, return inside the readToken function
     *  of components.
     *  To debug the parsing, it may be convenient to return false. That
     *  enables to count the tokens issued from the lexer and so to find
     *  the exact rule that is likely to produce inadequate results.
     */
    void eatToken(ReadResult& result);

    bool setToNextToken(ReadResult& result)
      {
        bool booleanResult = false;
        if (isValidRange()) {
          if (_lexer.doesNeedClear())
            _lexer.clearToken();
          do {
            _lexer.eatToken(result);
          } while (result == RRContinueLexing);
          booleanResult = (result == RRHasToken);
        }
        else
           result = RRNeedChars;
        if (!booleanResult)
          clearRange();
        return booleanResult;
      }

    /*! Makes a copy of the current token location */
    location newTokenLocation() const { return copy_loc(_tokenLocation); }

    /*! copies the end position of the current token location into the end position in the argument */
    void extendLocationWithToken(location loc) const {
      extend_location_with(loc,_tokenLocation); }

    /*! Converts the current token location to an equivalent clang SourceLocation */
    clang::SourceLocation tokenSourceLocation() const
      { return _clang_utils->getSourceLocation(_tokenLocation); }

    bool isValidRange() const
      { return _isVerbose ? false
            : (_localStackHeight >= 0 && _localStackHeight <= 7);
      }
    void clearRange() { _localStackHeight = 0; }
    bool hasErrors() const
      { return _errorMessages && !_errorMessages->empty(); }
    std::list<ErrorMessage>& errors() const
      { assert(_errorMessages); return *_errorMessages; }

    /// outputs existing error messages before failing with assert(false)
    bool fail () const {
      std::list<ErrorMessage>& msgs = errors();
      std::list<ErrorMessage>::const_iterator iterEnd = msgs.end();
      for (std::list<ErrorMessage>::const_iterator iter = msgs.begin();
           iter != iterEnd; ++iter)
        std::cerr << iter->filepos() << ':' << iter->linepos() << ':'
                  << iter->columnpos() << ": " 
                  << iter->getMessage() << std::endl;
      msgs.clear();
      return false;
    }

    const clang::NamedDecl* isCodeName(const std::string& name,
        const clang::TemplateArgument** templateArgument=NULL,
        bool* hasOverload=NULL) const;
    const clang::NamedDecl* findQualifiedName(const std::string& name,
        const clang::DeclContext* context, bool* hasOverload=NULL) const;
    bool isIntegralTypedefType(qualified_name name) const;
    bool isSignedTypedefType(qualified_name name) const;
    bool isArithmeticTypedefType(qualified_name name) const;
    bool isFloatingTypedefType(qualified_name name) const;
    bool isPointerTypedefType(qualified_name name) const;
    bool isReferenceTypedefType(qualified_name name) const;
    bool isArrayTypedefType(qualified_name name) const;
    bool is_char_signed() const;
    bool is_wchar_signed() const;
    qualified_name makeCompoundTypedefType(qualified_name name,
        tkind* templateKind) const;
    logic_type makeTypeOfPointed(qualified_name name) const;
    logic_type makeTypeOfReferenced(qualified_name name) const;
    logic_type makeTypeOfArrayElement(qualified_name name) const;
    const clang::RecordType* getRecordType(qualified_name name) const;
    bool addOverloadedLogicFunctions(const std::string& name, logic_info info,
        bool isMethod=false)
      { return addOverloadedLogicFunctionOrOperator(name, info, isMethod); }
    bool addOverloadedLogicOperators(const std::string& name,
        DLexer::OperatorPunctuatorToken::Type typeOperator, logic_info info,
        bool isMethod=false)
      { return addOverloadedLogicFunctionOrOperator(name, info, isMethod,
          &typeOperator);
      }
    bool addLogicType(const std::string& name, logic_type_info ltypeInfo);

    GlobalContext::LogicType* findGlobalLogicType(qualified_name name) const;
    GlobalContext::LogicVariable* findGlobalLogicVariable(qualified_name name)
      const;
    GlobalContext::NestedContext* findGlobalLogicName(qualified_name name) const
      { return _clang_utils->globalAcslContext().findAbsolute(name); }
    GlobalContext::NestedContext* findLogicName(const std::string& name) const
      { return _clang_utils->globalAcslContext().find(name, _currentLogicScope);
      }
    GlobalContext::NestedContext* findLogicName(qualified_name context,
        const std::string& name, tkind* templateParameterContext=NULL) const;
    /* qualification */ list createPrequalification() const;
    GlobalContext::NestedContext* findLogicQualifiedName(
        const std::string& name, GlobalContext::NestedContext* scope) const
      { const GlobalContext::NestedContext::SonsSet* sons = scope
            ? scope->ssons() : &_clang_utils->globalAcslContext().logicTable();
        GlobalContext::NestedContext* result = NULL;
        if (sons) {
          GlobalContext::NestedContext locate(name);
          GlobalContext::NestedContext::SonsSet::const_iterator
            found = sons->find(&locate);
          result = (found != sons->end()) ? *found : NULL;
        };
        return result;
      }

    logic_type boolean_type() const {
      qualification logic_ns = qualification_QNamespace("Utf8_logic");
      qualified_name boolean =
        qualified_name_cons(cons_container(logic_ns,NULL),"boolean");
      GlobalContext::LogicType* def =  findGlobalLogicType(boolean);
      assert(def);
      logic_type_info info = def->type_info();
      return logic_type_Lnamed(qualified_name_dup(info->type_name),false,NULL);
    }
    
    bool is_builtin_boolean(logic_type t) const {
      static logic_type default_boolean_type = boolean_type();
      return logic_type_equal(default_boolean_type,t);
    }

    bool isLogicSetType(logic_type typ) const {
      return
        typ->tag_logic_type == LNAMED &&
        strcmp(typ->cons_logic_type.Lnamed.name->decl_name,"set") == 0;
    }
    
    logic_type type_of_element(logic_type typ) const {
      assert (isLogicSetType(typ));
      return 
        (logic_type)
        typ->cons_logic_type.Lnamed.template_arguments->element.container;
    }

    logic_type logicArithmeticPromotion(qualified_name name) const;
    logic_type makeLogicType(qualified_name name) const;
    qualified_name makeLogicQualifiedName(const std::string& name) const;

    /** Outside of a class, returns NULL. Inside a class,
        it returns the type corresponding to the this pointer when in a
        code annotation or function contract, and to the \this object when
        in a global annotation.
     */
    logic_type queryThisType() const;
    
    /** Outside of a class, returns NULL. Inside a class, returns the object
        *this (when in a code annotation or function constract) or \this
        (when in a global annotation)
    */
    term_lval thisLval() const;

    bool retrieveTypeOfField(qualified_name name, tkind templateParameters,
        const std::string& fieldName, term_offset& offset, logic_type& ltype,
        std::string& errorMessage);
    
    logic_var_def hasLocalBinding(const std::string& name) const
      { std::map<std::string, std::list<logic_var_def> >::const_iterator
            found = _localBinding.find(name);
        return (found != _localBinding.end()) ? found->second.back() : NULL;
      }
    void addLocalBinding(const std::string& name, logic_var_def definition)
      { std::map<std::string, std::list<logic_var_def> >::iterator
            found = _localBinding.find(name);
        if (found == _localBinding.end())
          found = _localBinding.insert(std::make_pair(name,
                std::list<logic_var_def>())).first;
        found->second.push_back(definition);
      }

    void removeLocalBinding(const std::string& name)
      { std::map<std::string, std::list<logic_var_def> >::iterator
            found = _localBinding.find(name);
        if (found != _localBinding.end()) {
          free_logic_var_def(found->second.back());
          found->second.pop_back();
          if (found->second.empty())
            _localBinding.erase(found);
        };
      }

    logic_type hasLogicFormal(const std::string& name) const
      { std::map<std::string, logic_type>::const_iterator found = 
          _logicFormals.find(name);
        return (found != _logicFormals.end())?found->second:NULL;
      }
    void addLogicFormal(const std::string& name, logic_type type)
      { _logicFormals.insert(std::make_pair(name,type)); }
    void removeLogicFormal(const std::string& name)
      { _logicFormals.erase(name); }

    void addLogicLabel(const std::string& name) { _logicLabels.insert(name); }
    void removeLogicLabel(const std::string& name)
      { std::set<std::string>::iterator found = _logicLabels.find(name);
        if (found != _logicLabels.end())
          _logicLabels.erase(found);
      }
    logic_label findLogicLabel(const std::string& name) const;
    void set_result_context(bool flag) { _result_context = flag; }
    logic_type createResultType() const;
    bool isVerbose() const { return _isVerbose; }
    void setVerbose() { _isVerbose = true; }
  };

  typedef ::Parser::TStateStack<Arguments> State;

private:
   /*! @brief Current state of the parser.
    *
    *  This field is a stack of state machines. The current state machine can
    *  go to another local state. It can shift, that is it pushes a new state
    *  machine onto the stack _state. It can reduce, that is it pops the last
    *  state machine from the stack _state
    */
  State _state;
    /*! @brief Global services to help the CIL AST construction methods.
     *
     *  These services are to be called by _state.parse = readToken methods
     *    of the components.
     */

  void addBuiltinBinding(const std::string& ident, logic_type ret_type, std::initializer_list<logic_type> args);
//  void addBuiltinBinding(const std::string& ident, logic_type ret_type, logic_type arg0);
//  void addBuiltinBinding(const std::string& ident, logic_type ret_type, logic_type arg0, logic_type arg1);
  void addBuiltinBindings(void);

  Arguments _arguments;
  std::list<ErrorMessage> _errorMessages; //!< List of the error messages.

public:
  template <class TypeObject>
  Parser(const clang::DeclContext* clangContext,
      const clang::ASTContext* clangAST, clang::Sema* clangSema,
      clang::Scope* clangScope,
      Clang_utils* clang_utils, TypeObject& object, const RTTITable& rttiTable)
    : _arguments(clangContext, clangAST, clangSema, clangScope,
        clang_utils, rttiTable)
    { _state.shift(object, &TypeObject::readToken); addBuiltinBindings(); _arguments._errorMessages = &_errorMessages; }

  State& state() { return _state; }
  const State& state() const { return _state; }
  const std::list<ErrorMessage>& errorMessages() const
    { return _errorMessages; }
  bool hasError() const { return !_errorMessages.empty(); }
  void parse(const std::string& buffer, const clang::SourceLocation& sourceLocation);

  Lexer& lexer() { return _arguments.lexer(); }
};

} // end of namespace Acsl

#define DefineParseCase(Delim)                                                 \
case D##Delim:                                                                 \
L##Delim:

#define DefineInitParseCase(Delim)                                             \
case D##Delim:                                                                 \

#define DefineGotoCase(Delim)                                                  \
{ state.point() = D##Delim;                                                    \
  if (arguments.isVerbose()) {                                                 \
    std::cout << "** token \"";                                                \
    arguments.lexer().assumeContentToken();                                    \
    arguments.getContentToken().write(std::cout,                               \
      AbstractToken::PersistentFormat().setPretty());                          \
    std::cout << "\" parsed, goto state (" #Delim ")" << std::endl;            \
  };                                                                           \
  if (arguments.setToNextToken(result)) goto L##Delim;                         \
  return result;                                                               \
}

#define DefineGotoCaseWithIncrement(Increment, LabelTarget)                    \
{ state.point() += Increment;                                                  \
  if (arguments.isVerbose()) {                                                 \
    std::cout << "** token \"";                                                \
    arguments.lexer().assumeContentToken();                                    \
    arguments.getContentToken().write(std::cout,                               \
      AbstractToken::PersistentFormat().setPretty());                          \
    std::cout << "\" parsed, goto state" << state.point() << std::endl;        \
  };                                                                           \
  if (arguments.setToNextToken(result)) goto LabelTarget;                      \
  return result;                                                               \
}

#define DefineGotoCaseAndParse(Delim)                                          \
{ state.point() = D##Delim;                                                    \
  if (arguments.isVerbose())                                                   \
    std::cout << "** goto state (" #Delim ")" << std::endl;                    \
  goto L##Delim;                                                               \
}

#define DefineGotoCaseAndParseWithIncrement(Increment, LabelTarget)            \
{ state.point() += Increment;                                                  \
  if (arguments.isVerbose())                                                   \
    std::cout << "** goto state ("                                             \
              << state.point() << ")" << std::endl;                            \
  goto LabelTarget;                                                            \
}

#define DefineShift(Delim, Object, MethodPointer)                              \
{ arguments.shift();                                                           \
  state.point() = D##Delim;                                                    \
  state.shift(Object, MethodPointer);                                          \
  if (arguments.isVerbose()) {                                                 \
    std::cout << "** token \"";                                                \
    arguments.lexer().assumeContentToken();                                    \
    arguments.getContentToken().write(std::cout,                               \
        AbstractToken::PersistentFormat().setPretty());                        \
    std::cout << "\" parsed, call " << #MethodPointer                          \
      << ", next is (" #Delim ")" << std::endl;                                \
  };                                                                           \
  if (arguments.setToNextToken(result)) {                                      \
    result = (Object).readToken(state, arguments);                             \
    if (result == RRContinueParsing) {                                         \
      result = RRNeedChars;                                                    \
      state.point() = D##Delim;                                                \
      goto L##Delim;                                                           \
    };                                                                         \
  };                                                                           \
  return result;                                                               \
}

#define DefineShiftFrom(Delim, Point, Object, MethodPointer)                   \
{ arguments.shift();                                                           \
  state.point() = D##Delim;                                                    \
  state.shift(Object, MethodPointer);                                          \
  state.point() = Point;                                                       \
  if (arguments.isVerbose()) {                                                 \
    std::cout << "** token \"";                                                \
    arguments.lexer().assumeContentToken();                                    \
    arguments.getContentToken().write(std::cout,                               \
        AbstractToken::PersistentFormat().setPretty());                        \
    std::cout << "\" parsed, call " << #MethodPointer << ':'                   \
      << Point << ", next is (" #Delim ")" << std::endl;                       \
  };                                                                           \
  if (arguments.setToNextToken(result)) {                                      \
    result = (Object).readToken(state, arguments);                             \
    if (result == RRContinueParsing) {                                         \
      result = RRNeedChars;                                                    \
      state.point() = D##Delim;                                                \
      goto L##Delim;                                                           \
    };                                                                         \
  };                                                                           \
  return result;                                                               \
}

#define DefineShiftWithIncrement(Increment, LabelTarget, Object, MethodPointer)\
{ arguments.shift();                                                           \
  state.point() += Increment;                                                  \
  state.shift(Object, MethodPointer);                                          \
  if (arguments.isVerbose()) {                                                 \
    std::cout << "** token \"";                                                \
    arguments.lexer().assumeContentToken();                                    \
    arguments.getContentToken().write(std::cout,                               \
        AbstractToken::PersistentFormat().setPretty());                        \
    std::cout << "\" parsed, call " << #MethodPointer                          \
      << ", next is " << state.point() << std::endl;                           \
  };                                                                           \
  if (arguments.setToNextToken(result)) {                                      \
    result = (Object).readToken(state, arguments);                             \
    if (result == RRContinueParsing) {                                         \
      result = RRNeedChars;                                                    \
      goto LabelTarget;                                                        \
    };                                                                         \
  };                                                                           \
  return result;                                                               \
}

#define DefineShiftAndParse(Delim, Object, MethodPointer)                      \
{ arguments.shift();                                                           \
  state.point() = D##Delim;                                                    \
  state.shift(Object, MethodPointer);                                          \
  if (arguments.isVerbose())                                                   \
    std::cout << "** call " << #MethodPointer                                  \
      << ", next is (" #Delim ")" << std::endl;                                \
  if (arguments.isValidRange())                                                \
    result = (Object).readToken(state, arguments);                             \
  else {                                                                       \
    arguments.clearRange();                                                    \
    result = state.parse(arguments);                                           \
  };                                                                           \
  if (result == RRContinueParsing) {                                           \
    result = RRNeedChars;                                                      \
    state.point() = D##Delim;                                                  \
    goto L##Delim;                                                             \
  };                                                                           \
  return result;                                                               \
}

#define DefineShiftAndParseFrom(Delim, Point, Object, MethodPointer)           \
{ arguments.shift();                                                           \
  state.point() = D##Delim;                                                    \
  state.shift(Object, MethodPointer);                                          \
  state.point() = Point;                                                       \
  if (arguments.isVerbose())                                                   \
    std::cout << "** call " << #MethodPointer << ':' << Point                  \
      << ", next is (" #Delim ")" << std::endl;                                \
  if (arguments.isValidRange())                                                \
    result = (Object).readToken(state, arguments);                             \
  else {                                                                       \
    arguments.clearRange();                                                    \
    result = state.parse(arguments);                                           \
  };                                                                           \
  if (result == RRContinueParsing) {                                           \
    result = RRNeedChars;                                                      \
    state.point() = D##Delim;                                                  \
    goto L##Delim;                                                             \
  };                                                                           \
  return result;                                                               \
}

#define DefineReduce                                                           \
{ arguments.reduce();                                                          \
  state.reduce();                                                              \
  if (arguments.isVerbose()) {                                                 \
    std::cout << "** token \"";                                                \
    arguments.lexer().assumeContentToken();                                    \
    arguments.getContentToken().write(std::cout,                               \
        AbstractToken::PersistentFormat().setPretty());                        \
    std::cout << "\" parsed, reduction" << std::endl;                          \
  };                                                                           \
  if (arguments.setToNextToken(result) && result == RRNeedChars)               \
    result = RRContinueParsing;                                                \
  return result;                                                               \
}

#define DefineTReduce                                                          \
{ arguments.extendLocationWithToken(_loc);                                     \
  arguments.reduce();                                                          \
  state.reduce();                                                              \
  if (arguments.isVerbose()) {                                                 \
    std::cout << "** token \"";                                                \
    arguments.lexer().assumeContentToken();                                    \
    arguments.getContentToken().write(std::cout,                               \
        AbstractToken::PersistentFormat().setPretty());                        \
    std::cout << "\" parsed, reduction" << std::endl;                          \
  };                                                                           \
  if (arguments.setToNextToken(result) && result == RRNeedChars)               \
    result = RRContinueParsing;                                                \
  return result;                                                               \
}

#define DefineReduceAndParse                                                   \
{ arguments.reduce();                                                          \
  state.reduce();                                                              \
  if (arguments.isVerbose())                                                   \
    std::cout << "** reduction" << std::endl;                                  \
  if (arguments.isValidRange() && result == RRNeedChars)                       \
    result = RRContinueParsing;                                                \
  else {                                                                       \
    arguments.clearRange();                                                    \
    result = state.parse(arguments);                                           \
  };                                                                           \
  return result;                                                               \
}

#define DefineAddError(Message)                                                \
{ if (!arguments.addErrorMessage(Message))                                     \
    return RRFinished;                                                         \
}

#define DefineAddErrorAndParse(Message)                                        \
{ if (!arguments.addErrorMessage(Message))                                     \
    return RRFinished;                                                         \
  arguments.clearRange();                                                      \
  return RRNeedChars;                                                          \
}

#endif // ACSL_ParserH

