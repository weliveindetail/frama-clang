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
//   Definition of ACSL++ tokens.
//

#ifndef ACSL_TokenH

#include "DescentParse.h"
#include <unordered_map>
#include <sstream>

/** @file */

namespace Acsl { namespace DLexer {

/*! @def DefineStandardTokenMethods(a,b)
 *  @brief Automatically add methods for all classes derived from the class
 *  AbstractToken.
 */
#define DefineStandardTokenMethods(Type)                                       \
  virtual AbstractToken* _clone() const                                        \
    { return new Type(*this); }                                                \
  Type* clone() const                                                          \
    { return (Type*) _clone(); }

class Token;
/*! @class AbstractToken
 *  @brief The class AbstractToken represents a token in the ACSL language.
 *
 *  There exists two kinds of token. The tokens that are completly identified by
 *    an \b enum value compose the first kind. The other tokens compose the
 *    second kind. We name it \b elaborate tokens \n
 *  The first kind \b enum tokens are stored in the lexer Lexer::_token as an
 *    unsigned value. The second kind tokens are stored with an auto_ptr on the
 *    concrete Token derived from AbstractToken. The class Token has been
 *    created to supply a unique interface. \n \n
 *  As instance of an \b enum token, the token <tt>'('</tt> is an
 *    OperatorPunctuatorToken of type OperatorPunctuatorToken::TOpenParen. Its
 *    stored unsigned value is
 *  \code{.cpp}
 *  AbstractToken(OperatorPunctuatorToken().setType(TOpenParen)).params()
 *  \endcode Here is a way to retrieve the token with:
 *  \code{.cpp}
 *  AbstractToken token(... \/\* unsigned \*\/);
 *  if (token.getType() == AbstractToken::TOperatorPunctuator)
 *    ... = ((const OperatorPunctuatorToken&) token).queryType();
 *  \endcode \n
 *  An IdentifierToken is an instance of the second kind \b elaborate token.
 *    Its stored value is an <tt>auto_ptr\<AbstractToken\></tt> owning our
 *    IdentifierToken.
 *  @sa{Token, Lexer::_token, Lexer}
 */
class AbstractToken : protected FormatParameters {
public:
  /*! @enum Type
   *  @brief Main classes derived from AbstractToken.
   */
  enum Type
    { TUndefined, TIdentifier, TKeyword, TLiteral, TOperatorPunctuator,
      TComment, TEnd
    };

  /*! @class PersistentFormat
   *  @brief Available formats for printing/storing/reading tokens.
   *
   *  \code{.cpp}\endcode
   *  For the moment, tokens are only printed in the error messages of Lexer
   *    and Parser. They produces a string from the write method (that calls
   *    _write) called with an \c ostringstream.
   *  @sa{_write, write, Lexer, Parser}
   */
  class PersistentFormat {
  private:
    bool _isPretty; //!< should produce a readable output or just a raw output
                    //!<   only for persistence.

  public:
    PersistentFormat() : _isPretty(false) {}

    bool isPretty() const { return _isPretty; }
    PersistentFormat& setPretty() { _isPretty = true; return *this; }
    PersistentFormat& notPretty() { _isPretty = false; return *this; }
  };

private:
  AbstractToken(unsigned parameters) { params() = parameters; }
  friend class Token;

protected:
  DefineParameters(4, FormatParameters)
  DefineSubParameters(Type, 3, INHERITED)
  DefineSubParameters(Full, 1, Type)

protected:
  AbstractToken() {}

  void setIdentifier() { assert(!hasTypeField()); mergeTypeField(TIdentifier); }
  void setKeyword() { assert(!hasTypeField()); mergeTypeField(TKeyword); }
  void setLiteral() { assert(!hasTypeField()); mergeTypeField(TLiteral); }
  void setOperatorPunctuator()
    { assert(!hasTypeField()); mergeTypeField(TOperatorPunctuator); }
  void setComment() { assert(!hasTypeField()); mergeTypeField(TComment); }
  void setFull() { mergeFullField(1); }
  
  virtual void _write(std::ostream& out, PersistentFormat& format) const;
  virtual AbstractToken* _clone() const { return new AbstractToken(*this); }

public:
  AbstractToken(Type type) {}
  AbstractToken(const AbstractToken& source) : FormatParameters(source) {}
  AbstractToken& operator=(const AbstractToken& source)
    { FormatParameters::operator=(source);
      return *this;
    }
  virtual ~AbstractToken() {}
  virtual AbstractToken* clone() const { return _clone(); }

  void write(std::ostream& out, PersistentFormat& format) const
    { if (hasFullField())
        AbstractToken::_write(out, format);
      else
        _write(out, format);
    }

  //!< Returns a text representation of the token type and content
  std::string str() const;

  //!< Returns a text representation of the token content
  virtual std::string text() const;

  std::string type_text() const;

  virtual bool isValid() const
    { return hasTypeField() && (queryTypeField() < TEnd); }
  Type getType() const { return (Type) queryTypeField(); }
  bool isFull() const { return hasFullField(); }

  static std::string utf8_convert(unsigned int v);
    //!< converts a unicode character into its utf8 representation


};

/*! @class CommentToken
 *  @brief The class CommentToken represents a comment in the ACSL language.
 *
 *  CommentToken is a second kind AbstractToken.
 *  @sa{Token, IdentifierToken, KeywordToken, LiteralToken,
 *    OperatorPunctuatorToken, Lexer::readToken}
 */
class CommentToken : public AbstractToken {
private:
  typedef AbstractToken inherited;
  std::string _content;

protected:
  virtual void _write(std::ostream& out, PersistentFormat& format) const;

public:
  CommentToken() { inherited::setComment(); }
  CommentToken(const CommentToken& source)
    : inherited(source), _content(source._content) {}
  DefineStandardTokenMethods(CommentToken)

  const std::string& content() const { return _content; }
  std::string& content() { return _content; }
  bool isSlashSlashComment() const
    { return _content[0] == '/' &&  _content[1] == '/'; }
  virtual bool isValid() const
    { return inherited::isValid() && inherited::getType() == TComment; }
};

/*! @class IdentifierToken
 *  @brief The class IdentifierToken represents an identifier in the ACSL
 *    language.
 *
 *  IdentifierToken is a second kind AbstractToken.
 *  @sa{Token, CommentToken, KeywordToken, LiteralToken,
 *    OperatorPunctuatorToken, Lexer::readToken}
 */
class IdentifierToken : public AbstractToken {
private:
  typedef AbstractToken inherited;
  std::string _content;

protected:
  virtual void _write(std::ostream& out, PersistentFormat& format) const;

public:
  IdentifierToken() { inherited::setIdentifier(); }
  IdentifierToken(const std::string& id): _content(id) { inherited::setIdentifier(); }
  IdentifierToken(const IdentifierToken& source)
    : inherited(source), _content(source._content) {}
  DefineStandardTokenMethods(IdentifierToken)

  std::string& content() { return _content; }  // FIXME - this is assignable - is it good form?
  const std::string& content() const { return _content; }
  virtual bool isValid() const
    { return inherited::isValid() && inherited::getType() == TIdentifier; }
  virtual std::string text() const
    { return _content;
    }

};

/*! @class KeywordToken
 *  @brief The class KeywordToken represents a keyword in the ACSL language.
 *
 *  KeywordToken is a first kind AbstractToken.
 *  @sa{Token, CommentToken, IdentifierToken, LiteralToken,
 *    OperatorPunctuatorToken, Lexer::readToken}
 */
class KeywordToken : public AbstractToken {
  public:
  enum Type
    { TUndefined, TAuto, TBool, TCase, TChar, TChar16, TChar32, 
        TClass, TConst, TConstCast, TDouble, TDynamicCast, TElse, TEnum,
        TFalse, TFloat, TFor, TIf, TInt, TLong, TOperator, TReinterpretCast,
        TShort, TSigned, TSizeof, TStatic, TStaticCast, TStruct,
        TTrue, TTypeId, TTypename, TUnion, TUnsigned,
        TVirtual, TVoid, TVolatile, TWcharT, TWhile, TEndOfCode,
      TForall=TEndOfCode, TExists, TInteger, TReal, TBoolean, TLTrue, TLFalse,
        TLet, TLogic, TPredicate, TLemma, TAxiomatic, TAxiom, TEnsures,
        TAssumes, TRequires, TTerminates, TDecreases, TAssert, TAssigns, TReads,
        TWrites, TNothing, TBehavior, TComplete, TDisjoint, TBehaviors, TAt,
        TOld, TResult, TType, TMatch, TLambda, TSum, TProduct, TLength,
        TBlockLength, TOffset, TTIso, TOrigin, TObject, TNull, TBaseAddr,
        TAllocation, TAllocable, TFreeable, TFresh, TSeparated, TFrees,
        TAllocates, TAllocationStatus, TLStatic, TLRegister, TLAutomatic,
        TLDynamic, TLUnallocated, TInitialized, TSpecified, TWith, TNumOf,
        TLUnion, TLInter, TSubset, TEmpty, TValid, TValidRead, TValidFunction, TValidIndex,
        TValidRange, TInductive, TLoop, TVariant, TInvariant, TSet, TBreaks,
        TExits, TContinues, TReturns, TExitStatus, TFrom, TGlobal, TWeak,
        TStrong, TGhost, TDangling, TThis,
      // Below are built-in identifiers, not keywords per se.
      //      TUp, TDown, TNearestAway, TNearestEven, TRoundFloat, TRoundDouble,
      //TIsFinite, TIsNaN, TMin, TMax, TAbs, TSqrt, TPow, TCeil, TFloor, TExp,
      //  TLog, TLog10, TCos, TSin, TTan, TCosh, TSinh, TTanh, TAcos, TAsin,
      //  TAtan, TAtan2, THypot, TExact, TRoundError,
        TEnd
    };

  typedef std::unordered_map<std::string, Type> Map;
  typedef std::pair<std::string, KeywordToken::Type> Connection;

  static Connection mapUnicode[];
  static Map _unicodeKeywords;
  static Connection mapUnprotected[];
  static Map _unprotectedKeywords;
    //!< the keyword without '\' as first character.
  static Connection mapProtected[];
  static Map _protectedKeywords; //!< the keyword with '\' as first character.

private:
  typedef AbstractToken inherited;

protected:
  DefineParameters(8, AbstractToken)
  virtual void _write(std::ostream& out, PersistentFormat& format) const;

public:
  KeywordToken() { setKeyword(); setFull(); }
  KeywordToken(Type t) { setKeyword(); setFull(); setType(t); }
  KeywordToken(const KeywordToken& source) : inherited(source) {}
  DefineStandardTokenMethods(KeywordToken)

  Type getType() const    { return (Type) queryOwnField(); }
  KeywordToken& setType(Type type)
    { assert(!hasOwnField()); mergeOwnField(type); return *this; }
  virtual bool isValid() const
    { return inherited::isValid() && (inherited::getType() == TKeyword)
          && hasOwnField() && (queryOwnField() < TEnd);
    }

  virtual std::string text() const;

};

/*! @class LiteralToken
 *  @brief The class LiteralToken represents a constant in the ACSL language.
 *
 *  LiteralToken is a second kind AbstractToken. \n
 *  Such a constant can be an integer value like <tt>1</tt>, a character
 *    value like <tt>'a'</tt>, a floating point value like <tt>3.14</tt> or
 *    a string value like <tt>"abcde"</tt>.
 *  @sa{Token, CommentToken, IdentifierToken, KeywordToken,
 *    OperatorPunctuatorToken, Lexer::readToken}
 */
class LiteralToken : public AbstractToken {
public:
  enum Type { TUndefined, TInteger, TCharacter, TFloating, TString, TEnd };

private:
  typedef AbstractToken inherited;

protected:
  DefineParameters(3, AbstractToken)

  void setInteger()   { assert(!hasOwnField()); mergeOwnField(TInteger); }
  void setCharacter() { assert(!hasOwnField()); mergeOwnField(TCharacter); }
  void setFloating()  { assert(!hasOwnField()); mergeOwnField(TFloating); }
  void setString()    { assert(!hasOwnField()); mergeOwnField(TString); }

  LiteralToken() { inherited::setLiteral(); }
  LiteralToken(const LiteralToken& source) : inherited(source) {}
  virtual void _write(std::ostream& out, PersistentFormat& format) const;
  
public:
  Type getType() const { assert(hasOwnField()); return (Type) queryOwnField(); }
  DefineStandardTokenMethods(LiteralToken)

  bool isInteger() const { return queryOwnField() == TInteger; }
  bool isCharacter() const { return queryOwnField() == TCharacter; }
  bool isFloating() const { return queryOwnField() == TFloating; }
  bool isString() const { return queryOwnField() == TString; }

  virtual bool isValid() const
    { return inherited::isValid() && (AbstractToken::getType() == TLiteral)
        && hasOwnField() && (queryOwnField() < TEnd);
    }
};

class IntegerLiteralToken : public LiteralToken {
public:
  typedef LiteralToken inherited;
  enum Type { TDecimal, TBit, TOctal, THexaDecimal };
  enum Extension {
    ENoExtension, EUnsigned = 1, ELong = 2, EUnsignedLong=3,
    ELongLong = 4, EUnsignedLongLong = 5
  };

private:
  // don't try to interpret the value as an integer: since ACSL integers
  // are unbounded, we would need an big int library for that.
  std::string _value;

protected:
  DefineParameters(5, inherited)
  DefineSubParameters(Type, 2, INHERITED)
  DefineSubParameters(Extension, 3, Type)

  virtual void _write(std::ostream& out, PersistentFormat& format) const;

public:
  IntegerLiteralToken() : _value() { inherited::setInteger(); }
  IntegerLiteralToken(const IntegerLiteralToken& source)
    : inherited(source), _value(source._value) {}
  DefineStandardTokenMethods(IntegerLiteralToken)

  bool isDecimal() const { return !hasTypeField(); }
  bool isBit() const { return queryTypeField() == TBit; }
  bool isOctal() const { return queryTypeField() == TOctal; }
  bool isHexadecimal() const { return queryTypeField() == THexaDecimal; }
  
  bool isInt() const { return !(queryExtensionField() >> 1); }
  bool isUnsigned() const { return queryExtensionField() & EUnsigned; }
  bool isLong() const { return queryExtensionField() & ELong; }
  bool isLongLong() const { return queryExtensionField() & ELong; }
  bool isUnsignedLong() const
    { return (queryExtensionField() & EUnsignedLong) == EUnsignedLong; }
  bool isUnsignedLongLong() const
    { return (queryExtensionField() & EUnsignedLongLong) == EUnsignedLongLong;}
  bool hasExtension() const { return hasExtensionField(); }

  void setType(Type type) { assert(!hasTypeField()); mergeTypeField(type); }
  void mergeExtension(Extension extension) { mergeExtensionField(extension); }

  const std::string& getValue() const { return _value; }
  std::string& value() { return _value; }

  virtual bool isValid() const
    { return inherited::isValid() && LiteralToken::isInteger(); }
};

class CharacterLiteralToken : public LiteralToken {
private:
  typedef LiteralToken inherited;
  union { char ch; wchar_t wch; } _value;

public:
  enum Type { TUndefined, TChar, TWideChar };
  
protected: 
  DefineParameters(2, inherited);

  virtual void _write(std::ostream& out, PersistentFormat& format) const;

public:
  CharacterLiteralToken() { _value.wch = L'\0'; inherited::setCharacter(); }
  CharacterLiteralToken(char ch)
    { inherited::setCharacter(); mergeOwnField(TChar); _value.ch = ch; }
  CharacterLiteralToken(wchar_t wch)
    { inherited::setCharacter(); mergeOwnField(TWideChar); _value.wch = wch; }
  DefineStandardTokenMethods(CharacterLiteralToken)

  bool isChar() const { return queryOwnField() == TChar; }
  bool isWideChar() const { return queryOwnField() == TWideChar; }

  void setType(Type type) { assert(!hasOwnField()); mergeOwnField(type); }

  char getChar() const { assert(queryOwnField() == TChar); return _value.ch; }
  const wchar_t& getWideChar() const
    { assert(queryOwnField() == TWideChar); return _value.wch; }

  char& char_value() { assert(queryOwnField() == TChar); return _value.ch; }
  wchar_t& wchar_value() { 
    assert(queryOwnField() == TWideChar); return _value.wch; }
  void set_value(char c) {
    assert(queryOwnField() != TUndefined);
    if (queryOwnField() == TChar) _value.ch = c; else _value.wch = c;
  }

  virtual bool isValid() const
    { return inherited::isValid()
          && inherited::isCharacter() && hasOwnField();
    }
};

class FloatingLiteralToken : public LiteralToken {
public:
  enum FloatingSuffix { FSNone, FSDouble, FSFloat, FSLongDouble };
  enum Type { TDecimal, TBit, THexaDecimal };

private:
  typedef LiteralToken inherited;
  // do not interpret the value as a floating-point number, as it is
  // normally a mathematical real.
  std::string _real;

protected:
  DefineParameters(4, LiteralToken)
  DefineSubParameters(Type, 2, INHERITED)
  DefineSubParameters(Suffix, 2, Type)

  virtual void _write(std::ostream& out, PersistentFormat& format) const;

public:
  FloatingLiteralToken() : _real() { inherited::setFloating(); }
  FloatingLiteralToken(const FloatingLiteralToken& source)
    :  inherited(source), _real(source._real) {}
  DefineStandardTokenMethods(FloatingLiteralToken)
  
  bool isReal() const { return !hasSuffixField(); }
  bool isDouble() const { return querySuffixField() == FSDouble; }
  bool isFloat() const { return querySuffixField() == FSFloat; }
  bool isLongDouble() const { return querySuffixField() == FSLongDouble; }

  virtual bool isValid() const
      { return inherited::isValid() == inherited::isFloating(); }
  void setType(Type type) { assert(!hasTypeField()); mergeTypeField(type); }
  void mergeSuffix(FloatingSuffix suffix) { mergeSuffixField(suffix); }

  const std::string& getValueAsString() const { return _real; }
  std::string& value() { return _real; }
};

class StringLiteralToken : public LiteralToken {
private:
  typedef LiteralToken inherited;
  std::string _content;

protected:
  virtual void _write(std::ostream& out, PersistentFormat& format) const;

public:
  StringLiteralToken(const std::string& content)
      : _content(content) { inherited::setString(); }
  StringLiteralToken(const StringLiteralToken& source)
      : inherited(source), _content(source._content) {}
  DefineStandardTokenMethods(StringLiteralToken)

  std::string& content() { return _content; }
  const std::string& content() const { return _content; }
  virtual bool isValid() const
    { return inherited::isValid() && inherited::getType() == TString; }
};

/*! @class OperatorPunctuatorToken
 *  @brief The class OperatorPunctuatorToken represents a punctuation symbol
 *    in the ACSL language.
 *
 *  OperatorPunctuatorToken is a first kind AbstractToken.
 *  @sa{Token, CommentToken, IdentifierToken, KeywordToken,
 *    LiteralToken, Lexer::readToken}
 */
class OperatorPunctuatorToken : public AbstractToken {
public:
  enum Type
    { TUndefined, TOpenBrace, TCloseBrace, TOpenBracket, TCloseBracket,
        TOpenParen, TCloseParen, TSemiColon, TColon, TEllipsis, TQuery,
        TColonColon, TPunct, TPunctStar, TComma, TArrowStar, TArrow,
      TPlus, TMinus, TStar, TDivide, TProcent, TBitXor, TAmpersand, TBitOr, 
        TTilda, TNot, TAssign, TLess, TGreater, TPlusAssign, TMinusAssign,
        TMultAssign, TDivideAssign, TModuloAssign, TBitXorAssign, TBitAndAssign,
        TBitOrAssign, TLeftShift, TRightShift, TLeftShiftAssign,
        TRightShiftAssign, TEqual, TDifferent, TLessOrEqual, TGreaterOrEqual,
        TLogicalAnd, TLogicalOr, TPlusPlus, TMinusMinus, TEndOfCode,
      TImplies=TEndOfCode, TEquiv, TLogicalXor, TBitImplies, TBitEquiv,
        TLTColon, TColonGT, TRange, THash, TTEnd
    };
  
private:
  typedef AbstractToken inherited;
  
protected:
  DefineParameters(6, AbstractToken)

  virtual void _write(std::ostream& out, PersistentFormat& format) const;

public:
  OperatorPunctuatorToken() { setOperatorPunctuator(); setFull(); }
  OperatorPunctuatorToken(const OperatorPunctuatorToken& source)
    : inherited(source) {}
  DefineStandardTokenMethods(OperatorPunctuatorToken)

  void writeSign(std::ostream& out) const;
  Type getType() const { return (Type) queryOwnField(); }
  void clearFull() { clearFullField(); }
  OperatorPunctuatorToken& setType(Type type)
    { assert(!hasOwnField()); mergeOwnField(type); return *this; }
  virtual bool isValid() const
    { return inherited::isValid()
          && (inherited::getType() == TOperatorPunctuator)
          && hasOwnField() && (queryOwnField() < TEnd);
    }

  bool isOperator() const
    { int type = queryOwnField();
      return ((type >= TPlus) && (type < TEnd));
    }
  bool isPunctuator() const
    { int type = queryOwnField();
      return ((type >= TOpenBrace) && (type <= TPunctStar));
    }
  bool isOverloadable() const
    { Type type = getType();
      return type == TOpenBracket || type == TOpenParen
        || (type >= TComma && type <= TMinusMinus)
        || (type >= TImplies && type <= TColonGT);
    }

  virtual std::string text() const;

  typedef std::unordered_map<std::string, Type> Map;
  typedef std::pair<std::string, OperatorPunctuatorToken::Type> Connection;

  static Connection mapUnicode[];
  static Map _unicodePunctuators;

};

/*! @class Token
 *  @brief The class Token encapsulates the AbstractToken access for the needs
 *    of the class Lexer in the ACSL language.
 *
 *  The two kinds of token defined by the class AbstractToken are managed
 *    by our class. The \b enum tokens are entirely defined by the _type field
 *    whereas the \b elaborate tokens use the _content field. \n
 *  To write such a token, we need a concrete token with a valid virtual _write
 *    method. So it is convenient to obtain a valid _content on need. For
 *    \b enum token, the method assumeContent provides the conversion
 *    algorithms from the _type field to the _content field.
 *  @sa{ getFullToken, getContent, assumeContent, Lexer::queryToken,
 *    Lexer::assumeContentToken, Lexer::getContentToken }
 */
class Token {
private:
  unsigned _type;
    //!< @brief this field enables to decode an AbstractToken and to find the
    //!<   complete token type.
    //!< It is in direct correspondence with AbstractToken::params()
  std::unique_ptr<AbstractToken> _content;
    //!< this field provides the additional content of an AbstractToken.

public:
  Token() : _type(0) {}
  Token(unsigned type, AbstractToken* token) : _type(type), _content(token) {}
  Token(const AbstractToken& fullToken) : _type(fullToken.queryParams()) {}
  Token(AbstractToken* token)
    { assert(token);
      _content.reset(token);
      _type = token->queryParams();
    }
  Token(const Token& source)
    : _type(source._type),
      _content(const_cast<Token&>(source)._content.release())
    { const_cast<Token&>(source)._type = AbstractToken::TUndefined; }
  Token& operator=(const Token& source)
    { _type = source._type;
      _content =
        std::unique_ptr<AbstractToken>(
          const_cast<Token&>(source)._content.release());
      const_cast<Token&>(source)._type = AbstractToken::TUndefined;
      return *this;
    }
  AbstractToken getFullToken() const
    { assert(_type != 0);
      return AbstractToken(_type);
    }

  int getType () const { return _type; }
  void assumeContent();
    //!< Fills the _content field with the right concrete class to explore the
    //!<   AbstractToken class hierarchy.
  AbstractToken* extractContent()
    { assert(_content.get()); return _content.release(); }
  const AbstractToken& getContent() const
    { assert(_content.get()); return *_content; }
  AbstractToken& getSContent() const
    { assert(_content.get()); return *_content; }
  bool hasContent() const { return _content.get(); }

  //!< Returns a pretty printed token: type and content
  //!< Note that it might modify the token if its content
  //!< has not been computed so far.
  std::string str();

  //!< Returns just the source text for this token
  std::string text() const;

  //!< Returns a string representation of the token type
  std::string type_text() const;
};

}} // end of namespace Acsl::DLexer

#endif // ACSL_TokenH

