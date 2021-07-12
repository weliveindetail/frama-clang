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
//   Definition of the ACSL++ lexer.
//

#ifndef ACSL_LexerH
#define ACSL_LexerH

#include <list>
#include "DescentParse.h"
#include "ACSLToken.h"

extern "C" {

#include "intermediate_format.h"

}

#include "Clang_utils.h"
#include "clang/AST/DeclCXX.h"
#include "clang/Lex/Token.h"

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


/** @file */

namespace Acsl {

/*! @class Lexer
 *  @brief Builds a token Token from a string buffer.
 *
 *  The main method of the class Lexer is readToken. It reads characters from
 *    the input string buffer and then it returns the token that has been read.
 *    readToken returns either RRHasToken, in which case lexer.queryToken()
 *    returns the token, or RRFinished, in which case the input has been completely lexed.
 *    \n \n
 *    The lexer is setup by first calling the constructor, and then calling setBuffer to
 *    set the input. setBuffer can be called repeatedly; each call to setBuffer will
 *    reset the internal state of the lexer.
 *    \n\n
 *    If queryToken() reveals the token to
 *    be a first kind enum token, then a simple static_cast conversion
 *    gives an access to what it is. If queryToken() reveals to be a second kind
 *    elaborate token the method getContentToken gives a read access to its
 *    content. \n \n
 *
 *    The lexer uses one of two methods to lex the input. The frist method is to
 *    delegate the lexing to clang. In this case the input buffer is completely
 *    lexed into a series of clang tokens, which are then converted to ACSL tokens
 *    as they are requested by calls to readToken(). Note that a single clang token
 *    is sometimes multiple ACSL tokens and sometimes multiple clang tokens
 *    constitute a single ACSL token. By using clang, we delegate all of the
 *    preprocessing macro substitution logic to clang.
 *    \n\n
 *    The second lexing method is to lex the input directly with methods in this class.
 *    This method is used to perform a first pass through the input to check for
 *    preprocessing directives that are not permitted in ACSL. This method is also
 *    incompletely implemented, in that it does not implemente all preprocessing directives
 *    (e.g. evaluating #if directives) and does not closely implement the details of
 *    macro substition, digraphs, trigraphs, backslash-newlines and likely other details.
 */
class Lexer : public Parser::Base {
public:
  /*! @class Error
   *  @brief Defines a lexing error to be reported into a Acsl::ErrorMessage.
   */
  class Error {
  public:
    std::string filePos;
    unsigned linePos; //!< Starting with 1
    unsigned columnPos; //!< Starting with 1 -- FIXME check this
    std::string message;

    /*! Creates a Error message, copying information from the beginning token location */
    Error(location position, const std::string& msg);
    Error(const std::string& file, unsigned line, unsigned column,
        const std::string& msg)
      : filePos(file), linePos(line), columnPos(column), message(msg) {}

    std::string str() const;
    friend std::ostream & operator <<( std::ostream &os, const Error &err ) {
      return (os << err.str());
    }
  };

  typedef DLexer::AbstractToken AbstractToken;

private:
  typedef ReadResult (Lexer::*ReadPointerMethod)(const std::string& buffer,
      size_t& position, location loc);
  typedef DLexer::Token Token;
  typedef Parser::TTextBuffer<char> TextBuffer;
  typedef std::list<std::pair<std::string,AbstractToken> > Utf8SymbolSet;

  std::string _buffer; //!< The text material being lexed
  size_t _position; //!< The current position within _buffer
  bool _hasFinished; //!< set true by the lexer when the end of input has been reached


  location _tokenLocation;
    //!< The ACSL location of the current token in the source text, updated as the source text is read
  clang::SourceLocation _clangSourceLocation;
    //!< Location of the annotation text (the contents of _buffer) as provided by clang (not updated as tokens are lexed)

  TextBuffer _currentToken;
    //!< text content of _token that the lexer is currently reading.
  Token _token;    //!< Token that the lexer most recently completed
  bool _hasNewlineToken; //!< if the previous token was a comment  -- FIXME explain this

  char _context;   //!< context for comments and for constant reading.
  char _extension; //!< additional information for reading a literal extension.

  enum { Unknown, Dec, Oct, Hex, Bin } _digits;
    //!< kind of digits allowed when parsing numeric constant
  enum { LeadZero, Digits, FracPart, Exponent, ExpNext, ISuf, FSuf } _litState;
    //!< current state of numeric literal parsing
  DLexer::CharacterLiteralToken::Type _charLitKind;
  std::list<Error> _errorList; //!< List of errors produced by the lexer.

  // macro arguments for clang::TokenLexer
  typedef std::vector<std::list<std::pair<unsigned,
        DLexer::AbstractToken*> > > MacroTokensStack;
  MacroTokensStack _macroTokensStack;
  std::vector<clang::MacroArgs*> _currentMacroArgumentsStack;
  std::set<std::string> _usedMacros;
  enum StateLexer { SLStandard, SLMacroArgs, SLMacroTokens} _stateLexer;
  mutable std::vector<std::string> _stringsForToken;

  const clang::Sema* _clangSema;
    //!< Pointer to the clang Sema structure, for access to various Clang services

  unsigned lexerWarning;
  unsigned lexerError;
  unsigned ppWarning;
  unsigned ppError;


  Utf8SymbolSet _AcceptedUtf8Symbols;
    //!< utf8-encoded symbols that are parsed in ACSL specifications

  //! Stack of tokens from expanding macros; these are the next tokens to be read
  std::stack<DLexer::Token> _token_stack;

  std::list<Token> _acslTokens;
    //!< next tokens to be read, produced when a clang token represents multiple ACSL tokens
  std::list<clang::Token> _clangTokens;
    //!< list of clang tokens representing the input
  bool _clangTokensSet;
    //!< true if lexer used clang to do the actual lexing (so take tokens from _clangTokens)

  bool _rawOnly;
    //!< If true, then do not expand macros (only valid when NOT using clang)

  //! If true, the ACSL preprocessor only does a check for ASCL-specific PP restrictions, and
  //! leaves all other error reporting, etc., to the clang preprocessor
  bool _ppCheckOnly;


  /*! whether the given character could be the first character of an
      accepted utf8 symbol.
   */
  bool isUtf8SymbolStart(char cid);

  /*! Advance position until a non-space (and non-@) character is reached; skips backslash-newlines,
   *  skips comments, and if skipNewLines is true, skips new line characters as well; the position
   *  argument and the (beginning) line and character positions in the loc argument are updated,
   *  and will point to the first non-space character when the function returns (and the character
   *  at that position is returned). An '@' symbol is space.
   */
  // FIXME - is this still used
  char skipSpace(const std::string& buffer, size_t& position, location loc, bool skipNewLines=true);

  // FIXME - document
  void handlePPDirectiveInACSL(const std::string& buffer, size_t& position, size_t start, location loc);

  // FIXME - document
  // FIXME - is this still used
  const std::string getPreprocessorToken(const std::string& buffer, size_t& position, location loc, bool skipNewLines, bool raw);

  //! advances to end of line, issuing a warning about any non-white-space, non-comment material present.
  // FIXME - is this still used
  void complainAboutExcessMaterial(const std::string& buffer, size_t& position, location loc, bool warn);

  //! Advances Lexer to just before the end of line, ignoring everything, but advancing past backslash-newlines
// FIXME - is this still used
  const std::string skipUpToEndOfLine(const std::string& buffer, size_t& position, location loc);

  //! Skips to next preprocessing directive, reading and returning it; used to skip material within conditional if/ifdef/ifndef blocks
  const std::string skipToNextPPDirective(const std::string& buffer, size_t& position, location loc);

  // FIXME - is this still used?
  void skipThroughToken(const std::string& tok, const std::string& buffer, size_t& position, location loc);

  // FIXME - is this still used?
  const std::string getAndTrimRestOfLine(const std::string& buffer, size_t& position, location loc);

  // Utilities for handling macros

  /*! Consults clang to see if the given string has a macro definition */
  bool isDefinedMacro(const std::string& id);

  /*! Gets macro information from clang (defined only if isDefinedMacro is true) */
  clang::MacroInfo*  getMacro(const std::string& name) const;

  /*! Expands an identifier if it is a macro, returning the first token and pushing other tokens
   * on to the _token_stack; returns the token itself if it is not a macro.
   */
  DLexer::Token expandIfMacro(const DLexer::Token& token, Parser::Base::ReadResult& result);

  // FIXME - is this needed?
  bool handleMacroExpandedIdentifier(const std::string& identifier,
      clang::MacroInfo *macro, ReadResult& parseResult);

  /*! Used to read the arguments of a macro */
  clang::MacroArgs* readFunctionLikeMacroArgs(const std::string& identifier, clang::MacroInfo *macro);

  /*! Converts a clang token into an ACSL token; if the clang token represents multiple ACSL tokens,
   *  the extra ACSL tokens are pushed onto _acslTokens
   */
  DLexer::Token convertClangTokenToACSLToken(const clang::Token& source) const;

  //! Converts an ACSL token to a clang token
  //!
  clang::Token convertToClang(DLexer::Token source) const ;

  // Note here that charnum2/linenum2 are the end of a token (or the current position while
  // accumulating a token); charnum1/linenum1 are the beginning of the token.
  // Error grabs charnum1 -- the beginning of the token.

  /*! Adds current character to _currentToken and advances the end-position of the token
   * (the resulting position and loc information points to just after the stored token),
   * returns the character at the new position
   */
  char advanceChar2(const std::string& buffer, size_t& position, location loc) {
    _currentToken << buffer[position];
    position++;
    loc->charnum2++;
    char ch = buffer[position];
    if (ch == '\0') {
      if (getMoreCharacters()) ch = buffer[position];
    }
    return ch;
  }

  /*! Advances the position and begin-position of loc, returning the character at the new position,
   * without affecting the accumulating token; skips over backslash-newlines. FIXME - what about comments
   */
  char advanceChar1NoToken(const std::string& buffer, size_t& position, location loc);

  /*! Advances the position and end-position of loc, returning the character at the new position,
   * without affecting the accumulating token; skips over backslash-newlines. FIXME - what about comments
   */  // FIXME - more detail, should this be used?
  char advanceChar2NoToken(const std::string& buffer, size_t& position, location loc);

  /*! returns true if the character is a valid digit for the currently
   * selected base. Assumes that _digits is not UNKNOWN.
   */
  bool isDigit(char ch) const {
    assert(_digits);
    if (ch == '0' || ch == '1') return true;
    if (_digits == Bin) return false;
    if ( '0' <= ch && ch <= '7') return true;
    if (_digits == Oct) return false;
    if (ch == '8' || ch == '9') return true;
    if (_digits == Dec) return false;
    if ('a' <= ch && ch <= 'f') return true;
    return ('A' <= ch && ch <= 'F');
  }

  /*! sets the type of the given token based on the value of _digits */
  void setType(DLexer::IntegerLiteralToken *intToken) const {
    if (_digits == Hex)
      intToken->setType(DLexer::IntegerLiteralToken::THexaDecimal);
    if (_digits == Bin)
      intToken->setType(DLexer::IntegerLiteralToken::TBit);
    if (_digits == Oct)
      intToken->setType(DLexer::IntegerLiteralToken::TOctal);
  }

  /*! Returns an identifier or keyword token for the given text (without
   *  an initial backslash) according to whether the text is a protected token
   *  (cf. AcslToken.h)
   */
  Token protectedKeywordOrIdentifier(const std::string& textNoBS);

  void reparseWithClang(const std::string& text, clang::SourceLocation clangLoc);

protected:

  //! Internal utility function to read a token beginning at the given position,
  //! called by readToken()
  ReadResult readToken(const std::string& buffer, size_t& position, location loc);

  //! sets the stored token; only valid if not currently set
  //!
  void setToken(const Token& token)
    { assert(_token.getType() == AbstractToken::TUndefined);
      _token = token;
    }

  /*! Utility function that comments out the remainder of a line within the text, starting
   *  at the given offset in the input buffer
   */
  void removeFromRevision(size_t start);
  /*! reads the next token beginning at position and  and stores it in _token,
   *  updating position and leaving loc with the new tokens beginning and end positions;
   *  position will be the character after the lexed token (FIXME - check this)
   * FIXME - explain  result, here and in the following
   */
  ReadResult readMain(const std::string& buffer, size_t& position, location loc);

  //! read the end of a CommentToken, depending of the kind of comment
  //! (a line one or a delimited one).
  ReadResult readEndComment(const std::string& buffer, size_t& position, location loc);

  //! read an IdentifierToken from buffer beginning at position, putting the token
  //! in _token and updating position and loc
  ReadResult readIdentifierToken(const std::string& buffer, size_t& position,
      location loc);

  //! read a character literal
  //! in _token and updating position and loc
  ReadResult readNumberToken(const std::string& buffer, size_t& position, location loc);

  //! read a Character Token from buffer beginning at position, putting the token
  //! in _token and updating position and loc
  ReadResult readCharLiteral(const std::string& buffer, size_t& position, location loc);

  //! read a protected Token (one starting with a backslash)
  //! from buffer beginning at position, putting the token
  //! in _token and updating position and loc
  ReadResult readProtectedToken(const std::string& buffer, size_t& position, location loc);

  //! reads one or more chars in buffer, starting at position, interpreting them as a
  //! UTF8 character; only a predefined set of UTF8 characters are recognizezd
  ReadResult readUtf8Symbol(const std::string& buffer, size_t& position, location loc);

  /*! A common point to call for not-yet-implemented features (issues an error message) */
  void notImplemented(const clang::Token& source) const;

// FIXME - want this to be static so it can be reused
    /*! When using clang, call this method on new input to lex the entire input into clang preprocessor tokens,
     * which are placed in the _clangTokens list
     */
   void lexUsingClang(const clang::Sema* _sema, const std::string& input, clang::SourceLocation loc, std::list<clang::Token>& clangTokens);

private:
   Lexer(const Lexer& source) = delete;

public:
  //! creates a lexer
  Lexer(const clang::Sema* sema);



  /*! Destructs internal state of the lexer */
  ~Lexer() {
    if (!_macroTokensStack.empty()) {
      MacroTokensStack::iterator iterEnd = _macroTokensStack.end();
      for (MacroTokensStack::iterator iter = _macroTokensStack.begin();
          iter != iterEnd; ++iter) {
        std::list<std::pair<unsigned, DLexer::AbstractToken*> >::iterator
          tokenIterEnd = iter->end();
        for (std::list<std::pair<unsigned, DLexer::AbstractToken*> >
            ::iterator tokenIter = iter->begin();
            tokenIter != tokenIterEnd; ++tokenIter)
          if (tokenIter->second)
            delete tokenIter->second;
      };
    };
  }

  /*! returns true if all tokens have been read */
  bool hasFinished() {
    return _hasFinished;
  }

  /*! sets the input to a new buffer, replacing any old state and buffer */
  Lexer& setBuffer(const std::string& buffer, const clang::SourceLocation& sourceLocation, int position = 0, bool useClang = true, bool raw = false) {
    _buffer = buffer;
    _revised = buffer;
    _position = position;
    if (_tokenLocation) free_location(_tokenLocation);
    _tokenLocation = makeLocation(sourceLocation);
    _clangSourceLocation = sourceLocation;
    _clangTokensSet = false;
    _rawOnly = raw;
    _hasFinished = false;
    _acslTokens.clear();
     if (useClang) initFromClang();
     return *this;
  }

  /*! revised input text, in cases where some error recovery is possible */
  std::string _revised;
  

  /*! The routine to use to read tokens by means of the lexer; tokens are read from
   * buffer beginning at position; the token is stored in _token, with loc holding the
   * beginning and end position of the the token. On return position will point to the character
   * just after the token (FIXME - check this). Lexer sips over initial white space
   * comments, and backslash-newlines
   */ // FIXME - loc has end position or one beyond end?
  // FIXME - what about trigraphs, digraphs
  ReadResult readToken();


public:

  // FIXME - explain
  void eatToken(ReadResult& result);

  //! returns the stored token; note that tokens have a single owner, so the caller
  //! will be the actively owning instance
  Token& extractToken() { return _token; }

  //! returns the abstract token contained in the stored token (which must be valid)
  //!
  AbstractToken queryToken() { return _token.getFullToken(); }

  //! returns (a pointer to) the token location (does not own the returned value)
  //!
  location seeTokenLocation() const { return _tokenLocation; }

  // FIXME _ explain
  const AbstractToken& getContentToken() const { return _token.getContent(); }

  // FIXME - explain
  void assumeContentToken() { _token.assumeContent(); }

  //! returns true if errors have been accumulated by the lexer
  //!
  bool hasErrors() const { return !_errorList.empty(); }

  //! returns (a reference to) the list of lexer errors;
  //! error instances can be copied from and deleted using this reference
  std::list<Error>& errorList() { return _errorList; }

  //! returns true if there is a stored token
  //!
  bool doesNeedClear() const { return _token.getType(); }

  //! deletes (frees) the stored token and prepares the lexer to read the next token
  void clearToken()
    { _currentToken.clear();
      _context = '\0';
      _token = Token();
    }


  // FIXME - document - does this need to be public?
  void initFromClang() {
    lexUsingClang(_clangSema, _buffer, _clangSourceLocation, _clangTokens);
    _clangTokensSet = true;
  }

  std::string str(const location loc) {
    std::ostringstream s;
    s << loc->filename1 << ":" << loc->linenum1 << ":" << loc->charnum1 << "::"   << loc->filename2 << ":" << loc->linenum2 << ":" << loc->charnum2;
    return s.str();
  }
  /*! returns verbose information about a clang token (including start and end location) */
  std::string str(const clang::Token& t) const;
  /*! returns verbose information about a clang source location */
  std::string str(const clang::SourceLocation& loc) const;
  /*! returns the source text for a clang token */
  std::string text(const clang::Token& t) const;
  /*! makes a ACSL location from a clang source location */
  location makeLocation(clang::SourceLocation source) const;
  /*! sets _tokenLocation from a pair (beginning and end) clang locations */
  void setLocation(const clang::SourceLocation& begin, const clang::SourceLocation& end);
  /*! returns true if two clang locations are the same */
  bool sameLocation(const clang::SourceLocation& begin, const clang::SourceLocation& end) const;


protected:
  // If the input buffers are such that they do not necessarily contain the whole input, then
  // getMoreCharacters() should be implemented to add material to the buffer when called.

   /*! Adds more material to _buffer, resetting _position as needed; returns false if no more
    * material was added.
    */
    // There are not yet any non-vacuous implementations of this function so its uses may not be correct
  bool getMoreCharacters() { return false; }

};



} // end of namespace Acsl

#endif // ACSL_LexerH
