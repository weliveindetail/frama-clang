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
//  Implementation of the ACSL++ lexer.
//

#ifdef __GNUC__
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wclass-memaccess"
#endif
#include <sstream>
#include <climits>
#include <string>

#include "clang/Basic/Version.h"
#include "clang/Basic/Diagnostic.h"
#include "llvm/ADT/SmallString.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/DeclTemplate.h"
#include "clang/Lex/Preprocessor.h"
#include "clang/Sema/Sema.h"
#include "clang/Sema/Lookup.h"
#include "clang/Basic/TargetInfo.h"
#include "clang/Lex/MacroArgs.h"
#ifdef __GNUC__
#pragma GCC diagnostic pop
#endif

#include "ACSLLexer.h"
#include "intermediate_format.h"

namespace Acsl {

using namespace DLexer;

Lexer::Error::Error(location position, const std::string& msg)
  : filePos(position->filename1), linePos(position->linenum1),
    columnPos(position->charnum1), message(msg) {}

std::string
Lexer::Error::str() const {
  std::ostringstream s;
  s << filePos << ":" << linePos << ":" << columnPos << ": [lexer error] " << message;
  return s.str();
}

Lexer::Lexer(const clang::Sema* sema):
  _hasFinished(false),
  _tokenLocation(NULL),
  _hasNewlineToken(false),
  _context('\0'),
  _extension(0),
  _charLitKind(DLexer::CharacterLiteralToken::TUndefined),
  _stateLexer(SLStandard),
  _clangSema(sema),
  _AcceptedUtf8Symbols(),
  _clangTokensSet(false),
  _ppCheckOnly(true)
{
  // TODO - can we avoid creating these everytime we create a lexer
  lexerWarning = _clangSema->Diags.getCustomDiagID(clang::DiagnosticsEngine::Warning,"[lexer] %0");
  lexerError = _clangSema->Diags.getCustomDiagID(clang::DiagnosticsEngine::Error,"[lexer] %0");
  ppWarning = _clangSema->Diags.getCustomDiagID(clang::DiagnosticsEngine::Warning,"[pp] %0");
  ppError = _clangSema->Diags.getCustomDiagID(clang::DiagnosticsEngine::Error,"[pp] %0");
}


Lexer::ReadResult
Lexer::readEndComment(const std::string& buffer, size_t& position, location loc) {
  size_t pos;
  if (_context == '*')
    pos = buffer.find("*/", position);
  else
    pos = buffer.find('\n', position);
  unsigned lineEnd = loc->linenum2;
  unsigned charEnd = loc->charnum2;
  if (_context == '*') {
    unsigned previousCharEnd = charEnd;
    size_t subpos = buffer.find('\n', position);
    if (subpos != std::string::npos
        && (pos == std::string::npos || subpos < pos)) {
      ++lineEnd;
      previousCharEnd = (subpos-position)+charEnd;
      charEnd = 1;
      size_t subsubpos;
      bool doesContinue;
      do {
        subsubpos = buffer.find('\n', subpos);
        doesContinue = (subsubpos != std::string::npos
            && (pos == std::string::npos || subsubpos < pos));
        if (doesContinue) {
          ++lineEnd;
          previousCharEnd = (subsubpos-subpos)+1;
          subpos = subsubpos;
        };
      } while (doesContinue);
      charEnd = (pos != std::string::npos) ? (pos-subpos)+2
                                           : (buffer.length()-subpos-1);
      if (charEnd == 0) {
        charEnd = previousCharEnd;
        if (lineEnd > loc->linenum2)
          --lineEnd;
      };
    }
    else
      charEnd += (pos != std::string::npos)
          ? (pos-position)+1 : (buffer.length()-position-1);
  }
  else
    charEnd += (pos != std::string::npos)
        ? (pos-position) : (buffer.length()-position-1);


  if (pos != std::string::npos) {
    _currentToken.readFrom(buffer, position, pos-position); // FIXME - won't translate characters
    position = pos;
    if (_context == '*')
      position += 2;
    else {
      position++;
      _hasNewlineToken = true;
    };
    CommentToken* result = new CommentToken;
    _token = Token(result);
    _currentToken >> result->content();
    loc->linenum2 = lineEnd;
    loc->charnum2 = charEnd;
    return RRHasToken;
  };
  
  loc->linenum2 = lineEnd;
  loc->charnum2 = charEnd+1;
  if (buffer.length() > 0 && buffer[buffer.length()-1] == '\n') {
    ++loc->linenum2;
    loc->charnum2 = 1;
  };

  if (_context == '*') {
    _errorList.push_back(Error(loc, "comment not terminated"));
    return RRFinished;
  };
    
  _currentToken.readFrom(buffer, position, buffer.size()-position);
  position = buffer.size();
  CommentToken* result = new CommentToken;
  _token = Token(result);
  _currentToken >> result->content();
  loc->linenum2 = lineEnd;
  loc->charnum2 = charEnd;
  return RRHasToken;
}

Lexer::ReadResult
Lexer::readProtectedToken(const std::string& buffer, size_t& position, location loc) {
  char ch = buffer[position];
  while (isalnum(ch) || ch == '_') {
    ch = advanceChar2(buffer,position,loc);
  };
  std::string result;
  _currentToken >> result;
  _token = protectedKeywordOrIdentifier(result);
  return RRHasToken;
}

Token Lexer::protectedKeywordOrIdentifier(const std::string& textNoBS) {
  KeywordToken::Map::const_iterator
    found = KeywordToken::_protectedKeywords.find(textNoBS);
  if (found != KeywordToken::_protectedKeywords.end()) {
      KeywordToken result(found->second);
      return Token(result);
  }
  else {
    // treat it as a (built-in) identifier
    IdentifierToken* ident = new IdentifierToken("\\" + textNoBS);
    return Token(AbstractToken::TIdentifier,ident);
  };
}
  
Lexer::ReadResult
Lexer::readIdentifierToken(const std::string& buffer, size_t& position, location loc) {
  char ch = buffer[position];
  while (isalnum(ch) || ch == '_') { // FIXME - $$ in identifier?
    ch = advanceChar2(buffer,position,loc);
  };
  std::string ident;
  _currentToken >> ident;

  KeywordToken::Map::const_iterator found =
      KeywordToken::_unprotectedKeywords.find(ident);
  if (found != KeywordToken::_unprotectedKeywords.end()) {
    KeywordToken* result = new KeywordToken;
    result->setType(found->second);
    _token = Token(result);
  }
  else {
    IdentifierToken* result = new IdentifierToken(ident);
    _token = Token(AbstractToken::TIdentifier, result);
  }
  return RRHasToken;
}

Lexer::ReadResult
Lexer::readNumberToken(const std::string& buffer, size_t& position,
    location loc) {
  while(true) {
    char ch = buffer[position];
    switch (_litState) {
      case LeadZero: {
        if ( ch == 'x' || ch == 'X' ) {
          _digits = Hex;
          _litState = Digits;
          advanceChar2(buffer,position,loc);
          continue;
        }
        if (ch == 'b' || ch == 'B' ) {
          _digits = Bin;
          _litState = Digits;
          advanceChar2(buffer,position,loc);
          continue;
        }
        if (ch == '.') {
          if (buffer[position+1] == '.') {
            // special case: 0..xxx is a range of integers.
            // Just return the lexeme 0 as an int constant.
            IntegerLiteralToken* zero = new IntegerLiteralToken;
            zero->setType(IntegerLiteralToken::TOctal);
            _currentToken >> zero->value();
            _token = Token(zero);
            return RRHasToken;
          }
          _digits = Dec;
          _litState = FracPart;
          advanceChar2(buffer,position,loc);
          continue;
        }
        _digits = Oct;
        _litState = Digits;
        continue;
      }
      case Digits: {
        while (isDigit(ch)) {
          advanceChar2(buffer,position,loc);
          ch = buffer[position]; // = continue;
        }
        // We only support decimal or hexadecimal floats
        if (ch == '.' && (_digits != Oct)) {
          if (buffer[position+1] == '.') {
            // special case: xxx..expr is a range of integers.
            // Just return the lexeme xxx as an int constant.
            IntegerLiteralToken* cst = new IntegerLiteralToken;
            setType(cst);
            _currentToken >> cst->value();
            _token = Token(cst);
            return RRHasToken;  // FIXME - set secondaryState?
          }
          _litState = FracPart;
          advanceChar2(buffer,position,loc);
          continue;
        }
        if ((ch == 'e' || ch == 'E') && (_digits == Dec || _digits == Bin)) {
          _litState = Exponent;
          advanceChar2(buffer,position,loc);
          continue;
        }
        if ((ch == 'p' || ch == 'P') && _digits == Hex) {
          _litState = Exponent;
          advanceChar2(buffer,position,loc);
          continue;
        }
        // We are seeing an integer. It remains to check for a suffix.
        IntegerLiteralToken* intToken = new IntegerLiteralToken;
        setType(intToken);
        _token = Token(intToken);
        _litState = ISuf;
        continue;
      }
      case FracPart: {
        while (isDigit(ch)) {
          advanceChar2(buffer,position,loc);
          ch = buffer[position]; // = continue;
        }
        if ((ch == 'e' || ch == 'E') && _digits == Dec) {
          _litState = Exponent;
          advanceChar2(buffer,position,loc);
          continue;
        }
        if ((ch == 'p' || ch == 'P') && _digits == Hex) {
          _litState = Exponent;
          advanceChar2(buffer,position,loc);
          continue;
        }
        FloatingLiteralToken* floatToken = new FloatingLiteralToken;
        if (_digits == Dec)
          floatToken->setType(FloatingLiteralToken::TDecimal);
        if (_digits == Bin)
          floatToken->setType(FloatingLiteralToken::TBit);
        if (_digits == Hex)
          floatToken->setType(FloatingLiteralToken::THexaDecimal);
        _token = Token(floatToken);
        _litState = FSuf;
        continue;
      }
      case Exponent: {
        if (ch == '+' || ch == '-') {
          _litState = ExpNext;
          advanceChar2(buffer,position,loc);
          continue;
        }
        _litState = ExpNext;
        continue;
      }
      case ExpNext: {
        if (isdigit(ch)) {
          advanceChar2(buffer,position,loc);
          continue;
        }
        FloatingLiteralToken* floatToken = new FloatingLiteralToken;
        if (_digits == Dec)
          floatToken->setType(FloatingLiteralToken::TDecimal);
        if (_digits == Bin)
          floatToken->setType(FloatingLiteralToken::TBit);
        if (_digits == Hex)
          floatToken->setType(FloatingLiteralToken::THexaDecimal);
        _token = Token(floatToken);
        _litState = FSuf;
        continue;
      }
      case ISuf: {
        IntegerLiteralToken& intToken =
          (IntegerLiteralToken &)_token.getSContent();
        if (ch == 'l' || ch == 'L') {
          advanceChar2(buffer,position,loc);
          if (intToken.isInt()) {
            intToken.mergeExtension(IntegerLiteralToken::ELong);
            continue;
          }
          if (intToken.isLong()) {
            intToken.mergeExtension(IntegerLiteralToken::ELongLong);
            continue;
          }
          std::string constant;
          _currentToken >> constant;
          std::ostringstream msg;
          msg << "Unknown suffix for integer literal constant: "
              << constant << ".";
          _errorList.push_back(Error(loc,msg.str()));
          // release the token
          delete _token.extractContent();
          return RRFinished;
        }
        if (ch == 'u' || ch == 'U') {
          advanceChar2(buffer,position,loc);
          if (intToken.isUnsigned()) {
            std::string constant;
            _currentToken >> constant;
            std::ostringstream msg;
            msg << "Unknown suffix for integer literal constant: "
                << constant << ".";
            _errorList.push_back(Error(loc,msg.str()));
            // release the token
            delete _token.extractContent();
            return RRFinished;
          }
          intToken.mergeExtension(IntegerLiteralToken::EUnsigned);
          continue;
        }
        _currentToken >> intToken.value();
        return RRHasToken;
      }
      case FSuf: {
        FloatingLiteralToken& floatToken =
          (FloatingLiteralToken &)_token.getSContent();
        if (ch == 'l' || ch == 'L') {
          advanceChar2(buffer,position,loc);
          if (floatToken.isReal()) {
            floatToken.mergeSuffix(FloatingLiteralToken::FSLongDouble);
            continue;
          }
          std::string constant;
          _currentToken >> constant;
          std::ostringstream msg;
          msg << "Unknown suffix for Real literal constant: "
              << constant << ".";
          _errorList.push_back(Error(loc,msg.str()));
          // release the token
          delete _token.extractContent();
          return RRFinished;
        }
        if (ch == 'd' || ch == 'D') {
          advanceChar2(buffer,position,loc);
          if (floatToken.isReal()) {
            floatToken.mergeSuffix(FloatingLiteralToken::FSDouble);
            continue;
          }
          std::string constant;  // FIXME - set secondaryState?
          _currentToken >> constant;
          std::ostringstream msg;
          msg << "Unknown suffix for Real literal constant: "
              << constant << ".";
          _errorList.push_back(Error(loc,msg.str()));
          // release the token
          delete _token.extractContent();
          return RRFinished;
        }
        if (ch == 'f' || ch == 'F') {
          advanceChar2(buffer,position,loc);
          if (floatToken.isReal()) {
            floatToken.mergeSuffix(FloatingLiteralToken::FSFloat);
            continue;
          }
          std::string constant;
          _currentToken >> constant;
          std::ostringstream msg;
          msg << "Unknown suffix for Real literal constant: "
              << constant << ".";
          _errorList.push_back(Error(loc,msg.str()));
          // release the token
          delete _token.extractContent();
          return RRFinished;
        }
        _currentToken >> floatToken.value();
        return RRHasToken;
      }
    }
  }
  return RRNeedChars;
}

bool Lexer::isUtf8SymbolStart(char ch) {
  _AcceptedUtf8Symbols.clear();
  std::string symb;
  symb = AbstractToken::utf8_convert(0x2200);
  if (symb[0] == ch) {
    DLexer::KeywordToken tok;
    tok.setType(DLexer::KeywordToken::TForall);
    _AcceptedUtf8Symbols.push_front(
      std::pair<std::string,AbstractToken>(symb,tok));
  }
  symb = AbstractToken::utf8_convert(0x2203);
  if(symb[0] == ch) {
    DLexer::KeywordToken tok;
    tok.setType(DLexer::KeywordToken::TExists);
    _AcceptedUtf8Symbols.push_front(
      std::pair<std::string,AbstractToken>(symb,tok));
  }
  symb = AbstractToken::utf8_convert(0x2261);
  if(symb[0] == ch) {
    DLexer::OperatorPunctuatorToken tok;
    tok.setType(DLexer::OperatorPunctuatorToken::TEqual);
    _AcceptedUtf8Symbols.push_front(
      std::pair<std::string,AbstractToken>(symb,tok));
  }
  symb = AbstractToken::utf8_convert(0x2262);
  if (symb[0] == ch) {
    DLexer::OperatorPunctuatorToken tok;
    tok.setType(DLexer::OperatorPunctuatorToken::TDifferent);
    _AcceptedUtf8Symbols.push_front(
      std::pair<std::string,AbstractToken>(symb,tok));
  }
  symb = AbstractToken::utf8_convert(0x2264);
  if (symb[0] == ch) {
    DLexer::OperatorPunctuatorToken tok;
    tok.setType(DLexer::OperatorPunctuatorToken::TLessOrEqual);
    _AcceptedUtf8Symbols.push_front(
      std::pair<std::string,AbstractToken>(symb,tok));
  }
  symb = AbstractToken::utf8_convert(0x2265);
  if (symb[0] == ch) {
    DLexer::OperatorPunctuatorToken tok;
    tok.setType(DLexer::OperatorPunctuatorToken::TGreaterOrEqual);
    _AcceptedUtf8Symbols.push_front(
      std::pair<std::string,AbstractToken>(symb,tok));
  }
  symb = AbstractToken::utf8_convert(0x2212);
  if (symb[0] == ch) {
    DLexer::OperatorPunctuatorToken tok;
    tok.setType(DLexer::OperatorPunctuatorToken::TMinus);
    _AcceptedUtf8Symbols.push_front(
      std::pair<std::string,AbstractToken>(symb,tok));
  }
  symb = AbstractToken::utf8_convert(0x21D2);
  if (symb[0] == ch) {
    DLexer::OperatorPunctuatorToken tok;
    tok.setType(DLexer::OperatorPunctuatorToken::TImplies);
    _AcceptedUtf8Symbols.push_front(
      std::pair<std::string,AbstractToken>(symb,tok));
  }
  symb = AbstractToken::utf8_convert(0x21D4);
  if (symb[0] == ch) {
    DLexer::OperatorPunctuatorToken tok;
    tok.setType(DLexer::OperatorPunctuatorToken::TEquiv);
    _AcceptedUtf8Symbols.push_front(
      std::pair<std::string,AbstractToken>(symb,tok));
  }
  symb = AbstractToken::utf8_convert(0x2227);
  if (symb[0] == ch) {
    DLexer::OperatorPunctuatorToken tok;
    tok.setType(DLexer::OperatorPunctuatorToken::TLogicalAnd);
    _AcceptedUtf8Symbols.push_front(
      std::pair<std::string,AbstractToken>(symb,tok));
  }
  symb = AbstractToken::utf8_convert(0x2228);
  if (symb[0] == ch) {
    DLexer::OperatorPunctuatorToken tok;
    tok.setType(DLexer::OperatorPunctuatorToken::TLogicalOr);
    _AcceptedUtf8Symbols.push_front(
      std::pair<std::string,AbstractToken>(symb,tok));
  }
  symb = AbstractToken::utf8_convert(0x00AC);
  if (symb[0] == ch) {
    DLexer::OperatorPunctuatorToken tok;
    tok.setType(DLexer::OperatorPunctuatorToken::TNot);
    _AcceptedUtf8Symbols.push_front(
      std::pair<std::string,AbstractToken>(symb,tok));
  }
  symb = AbstractToken::utf8_convert(0x22BB);
  if (symb[0] == ch) {
    DLexer::OperatorPunctuatorToken tok;
    tok.setType(DLexer::OperatorPunctuatorToken::TLogicalXor);
    _AcceptedUtf8Symbols.push_front(
      std::pair<std::string,AbstractToken>(symb,tok));
  }
  symb = AbstractToken::utf8_convert(0x2208);
  if (symb[0] == ch) {
    DLexer::KeywordToken tok;
    tok.setType(DLexer::KeywordToken::TSubset);
    _AcceptedUtf8Symbols.push_front(
      std::pair<std::string,AbstractToken>(symb,tok));
  }
  symb = AbstractToken::utf8_convert(0x1D539);
  if (symb[0] == ch) {
    DLexer::KeywordToken tok;
    tok.setType(DLexer::KeywordToken::TBoolean);
    _AcceptedUtf8Symbols.push_front(
      std::pair<std::string,AbstractToken>(symb,tok));
  }
  symb = AbstractToken::utf8_convert(0x2124);
  if (symb[0] == ch) {
    DLexer::KeywordToken tok;
    tok.setType(DLexer::KeywordToken::TInteger);
    _AcceptedUtf8Symbols.push_front(
      std::pair<std::string,AbstractToken>(symb,tok));
  }
  symb = AbstractToken::utf8_convert(0x211D);
  if (symb[0] == ch) {
    DLexer::KeywordToken tok;
    tok.setType(DLexer::KeywordToken::TReal);
    _AcceptedUtf8Symbols.push_front(
      std::pair<std::string,AbstractToken>(symb,tok));
  }
  return !_AcceptedUtf8Symbols.empty();
}

Lexer::ReadResult
Lexer::readUtf8Symbol(const std::string& buffer, size_t& position, location loc) {
  size_t i = 1;
  while(!_AcceptedUtf8Symbols.empty()) {
    if (position+i>=buffer.size()) break;
    if (_AcceptedUtf8Symbols.size() == 1) {
      std::string symb = _AcceptedUtf8Symbols.front().first;
      size_t length = symb.size();
      while(i<length) {
        if (position+i >= buffer.size() || symb[i] != buffer[position+i]) {
          //TODO: use buffer[position] to determine the expected length of
          // the character in buffer
          size_t last = position+i>=buffer.size()?buffer.size()-1:position+i;
          std::ostringstream msg;
          msg << "unknown character A: "
              << buffer.substr(position, last)
              << ".";
          _errorList.push_back(Error(loc,msg.str()));
          position=last+1;
          return RRContinueLexing;
        }
        i++;
      }
      position+=i;
      loc->charnum2+=i;
      _token = _AcceptedUtf8Symbols.front().second;
      return RRHasToken;
    } else {
      Utf8SymbolSet::iterator it = _AcceptedUtf8Symbols.begin();
      Utf8SymbolSet::iterator end = _AcceptedUtf8Symbols.end();
      while(it != end) {
        if ((*it).first[i] != buffer[position+i]) {
          Utf8SymbolSet::iterator tmp = it;
          it++;
          _AcceptedUtf8Symbols.erase(tmp,it);
        } else it++;
      }
    }
    i++;
  }
  std::ostringstream msg;
  msg << "unknown character B: "
      << buffer.substr(position, position+i-1)
      << ".";
  _errorList.push_back(Error(loc,msg.str()));
  position+=i;
  return RRContinueLexing;
}

Lexer::ReadResult
Lexer::readCharLiteral(const std::string& buffer,
                       size_t& position, location loc) {
  DLexer::CharacterLiteralToken* tok = new CharacterLiteralToken;
  _token = Token(tok);
  tok->setType(_charLitKind);
  size_t length = buffer.length();
  if (buffer[position] == '\\') {
    position++;
    loc->charnum2++;
    if (position>=length) {
      _errorList.push_back(Error(loc, "unterminated escape sequence"));
      return RRFinished;
    }
    switch(buffer[position]) {
      case '\'': tok->set_value('\''); break;
      case '"': tok->set_value('"'); break;
      case '?': tok->set_value('?'); break;
      case '\\': tok->set_value('\\'); break;
      case 'a': tok->set_value('\a'); break;
      case 'b': tok->set_value('\b'); break;
      case 'f': tok->set_value('\f'); break;
      case 'n': tok->set_value('\n'); break;
      case 'r': tok->set_value('\r'); break;
      case 't': tok->set_value('\t'); break;
      case 'v': tok->set_value('\v'); break;
      case 'x': {
        unsigned long long res = 0;
        while(true) {
          position++;
          loc->charnum2++;
          if (position>=length) {
            _errorList.push_back(Error(loc,"unterminated char literal"));
            return RRFinished;
          }
          if ('0'<=buffer[position] && buffer[position]<= '9')
            res = 16*res + (buffer[position]-'0');
          else if ('a'<=buffer[position]&&buffer[position]<='f')
            res = 16*res + 10 + buffer[position]-'a';
          else if ('A'<=buffer[position]&&buffer[position]<='F')
            res = 16*res + 10 + buffer[position]-'A';
          else { loc->charnum2--; position--; break; }
        }
        if (_charLitKind == DLexer::CharacterLiteralToken::TWideChar) {
          if (res > 1ULL << (8*sizeof(wchar_t))) {
            _errorList.push_back(
              Error(loc,"escape sequence not in wide char range"));
            return RRFinished;
          }
          tok->wchar_value() = res;
        } else {
          if (res > UCHAR_MAX) {
            _errorList.push_back(
              Error(loc,"escape sequence not in char range"));
            return RRFinished;
          }
          tok->char_value() = res;
        }
        break;
      }
      default:
        if ('0'<= buffer[position] && buffer[position] <= '9') {
          unsigned res = 0;
          for (int i = 0; i<3; i++) {
            if(position>=length) {
              _errorList.push_back(
                  Error(loc,"unterminated char literal"));
              return RRFinished;
            }
            if(buffer[position] < '0' || buffer[position] > '7') break;
            res = res*8 + (buffer[position]-'0');
            position++;
            loc->charnum2++;
          }
          position--;
          loc->charnum2--;
          if (_charLitKind == DLexer::CharacterLiteralToken::TWideChar) {
            // assume wchar_t is wide enough to accomodate the 0-512 range.
            tok->wchar_value() = res;
          } else {
            if (res > UCHAR_MAX) {
              _errorList.push_back(
                Error(loc,"escape sequence not in char range"));
              return RRFinished;
            }
            tok->char_value() = res;
          }
        } else
          // Just ignore the '\' (\ followed by an unknown character can be
          // supported in an implementation-defined manner as per [lex.ccon.3]
          tok->set_value(buffer[position]);
        break;
    }
  } else { tok->set_value(buffer[position]); }
  bool first_char = true;
  while(true) {
    position++;
    loc->charnum2++;
    if (position >= length) {
      _errorList.push_back(Error(loc,"unterminated char literal"));
      return RRFinished;
    }
    if (buffer[position] == '\'') {
      position++;
      return RRHasToken;
    }
    if(first_char) {
      std::cerr <<
        loc->filename1 << ":" << loc->linenum1 << ":" << 
        loc->charnum1 << "-" << loc->charnum2 <<
        " Character literal has more than one char. Ignoring the other ones\n";
      first_char = false;
    }
    if (buffer[position] == '\\') position++;
  }
  assert(false);
}

const std::string Lexer::getPreprocessorToken(const std::string& buffer, size_t& position, location loc, bool skipNewLines, bool raw) {
  bool debug = false;
  char ch;
  while (true) {
    skipSpace(buffer,position,loc,skipNewLines);
    ch = buffer[position];
    // FIXME - what about continuation lines within or outside of comments
    if (ch == '/' && buffer[position+1] == '/') {
      do {
        ch = advanceChar1NoToken(buffer,position,loc);
      } while (ch != '\0' && ch != '\n' && ch != '\r');
      continue;
    }
    break;
  }
  size_t p = position;
  if (ch == '\0') return "";
  if (ch == '#') {
    // position is just after the returned string
    ch = advanceChar1NoToken(buffer,position,loc);
    return "#";
  }
  // FIXME - digraphs, trigraphs
  if (ch == '"') {
    // Read a quoted string
    size_t p = position;
    do {
      ch = advanceChar1NoToken(buffer,position,loc);
      if (ch == '\\') {
        ch = advanceChar1NoToken(buffer,position,loc);
        ch = advanceChar1NoToken(buffer,position,loc);
      }
      // FIXME - escaped characters, digraphs, trigraphs
    } while (ch != '\0' && ch != '"');
    if (ch == '\0') {
      // FIXME - unclosed string
    } else if (ch == '"') {
      ch = advanceChar1NoToken(buffer,position,loc);
      return std::string(buffer,p,position-p);
      // position is just after the closing quote
      // FIXME - return raw token, or actual string
    }
  }
  if (ch == '\'') {
    // Read a quoted character string (PP allows multiple characters within single quotes)
    size_t p = position;
    do {
      ch = advanceChar1NoToken(buffer,position,loc);
      if (ch == '\\') {
        ch = advanceChar1NoToken(buffer,position,loc);
        ch = advanceChar1NoToken(buffer,position,loc);
      }
     // FIXME - escaped characters, digraphs, trigraphs
    } while (ch != '\0' && ch != '\'');
    if (ch == '\0') {
      // FIXME - unclosed string
    } else if (ch == '"') {
      ch = advanceChar1NoToken(buffer,position,loc);
      // FIXME - return raw token, or actual string
    }
    return std::string(buffer,p,position-p);
    // position is just after the closing quote
  }
  while (isalnum(ch) || ch == '_' ) { // FIXME - also $?
    ch = advanceChar1NoToken(buffer,position,loc);
  }
  if ((size_t) p != position) {
    // An identifiers preprocessor token
    const std::string id = std::string(buffer,p,position-p);
    if (!raw) {
      if (isDefinedMacro(id)) {
        clang::MacroInfo* macro = getMacro(id);
        if (macro->isFunctionLike()) {
          if (debug)
            std::cout << "Not Expanding " << id
               << " -- is function like" << std::endl;
        } else {
          //std::cout << "Expanding " << id << " : ";
//          for (int i=0; i < macro->getNumTokens(); i++) {
//            std::cout << macro->getReplacementToken(i).getName()  << " ";
//          }
//          std::cout << std::endl;
        }
      }
    }
    return id;
  }
  // FIXME - is there a fixed set of operator tokens? or just one characer each? or any sequence
  while (!isalnum(ch) && ch != '_' && !isspace(ch) && ch != '@' && ch != '\0') {
    ch = advanceChar1NoToken(buffer,position,loc);
  }
  if (position != (size_t) p) advanceChar1NoToken(buffer,position,loc);
  return std::string(buffer,p,position-p);
  // FIXME - what about non-printable tokens or illegal tokens
}

DLexer::Token
Lexer::expandIfMacro(const DLexer::Token& token, Parser::Base::ReadResult& res) {
  bool debug=false;
  if (_rawOnly) return token;
  const std::string id = token.text();
  if (isDefinedMacro(id)) {
    clang::MacroInfo* macro = getMacro(id);
    if (macro->isFunctionLike()) {
      if (debug)
        std::cout << "Not Expanding " << id
            << " -- is function like" << std::endl;
      return token;
    } else {
      //std::cout << "Expanding " << id << std::endl;
      int i = macro->getNumTokens();
      if (i == 1) {
        const clang::Token& clang_token = macro->getReplacementToken(0);
        Token t = convertClangTokenToACSLToken(clang_token);
        t = expandIfMacro(t, res);
        //std::cout << "  Expanded to " <<  t.str() << std::endl;
        return t;
      } else {
        while (--i >= 0) {
          const clang::Token& clang_token = macro->getReplacementToken(i);
          _token_stack.push(convertClangTokenToACSLToken(clang_token));
          //std::cout << "Pushed    " << _token_stack.top().str()  << std::endl;
        }
        //std::cout << std::endl;
        if (_token_stack.empty()) {
          // Macro expanded to nothing
          return Token();
        } else {
          Token t = _token_stack.top();
          _token_stack.pop();
          //std::cout << "Popped " << t.str() << std::endl;
          t = expandIfMacro(t, res);
          return t;
        }
      }
    }
  }
  return token;
}


char
Lexer::skipSpace(const std::string& buffer, size_t& position, location loc, bool skipNewLines) {
  char ch = buffer[position];
  while ((isspace(ch) || ch == '@' || ch == '/' ) && (skipNewLines || (ch != '\n' && ch != '\r'))) {
    if (ch == '@') {
      ch = '@';
    }
    if (ch == '/') {
      if (buffer[position+1] != '/') break;
      if (buffer[position+2] == '@') {
        _revised[position+0] = ' ';
        _revised[position+1] = ' ';
        _revised[position+2] = ' ';
      } else {
        removeFromRevision(position);
      }
      do {
        ch = advanceChar1NoToken(buffer,position,loc);
      } while (ch != '\0' && ch != '\n' && ch != '\r');
      continue;
    }
    ++position;
    if (ch == '\n') {
      ++loc->linenum1;
      loc->charnum1 = 1;
    }
    else
      ++loc->charnum1;
    ch = buffer[position];
  };
  return ch;
}

Lexer::ReadResult Lexer::readToken() {
  bool debug = false;
  if (!_acslTokens.empty()) {
    _token = _acslTokens.front();
    _acslTokens.pop_front();
    // FIXME - location
    return RRHasToken;
  }
  if (_clangTokensSet) {
    while (!_clangTokens.empty()) {
      clang::Token t = _clangTokens.front();
      if (debug) {
        std::cout << "POPPED CLANG " << str(t) << std::endl;
      }
      if (t.is(clang::tok::TokenKind::unknown)) {
        const clang::SourceLocation& end = t.getEndLoc();
        _clangTokens.pop_front();

        if (text(t) == "\\") {
          clang::Token& tt = _clangTokens.front();
          if (debug) std::cout << "POPPED CLANG " << str(tt) << std::endl;

          if (tt.isOneOf(clang::tok::identifier,clang::tok::kw_true,clang::tok::kw_false,clang::tok::kw_this)) {

            clang::IdentifierInfo* identifierInfo = tt.getIdentifierInfo();
            std::string text = std::string(identifierInfo->getNameStart(),
                identifierInfo->getLength());

            if (!sameLocation(end, tt.getLocation())) {
              _clangSema->Diags.Report(tt.getLocation(),lexerWarning)
                              << "White space not permitted between the \\ and the identifier";
              // Continue on though
            }
            _token = protectedKeywordOrIdentifier(text);
            setLocation(tt.getLocation(),tt.getEndLoc()); // FIXME prefer using t.getLocation() but that is not always valid on an unknown token
            _clangTokens.pop_front();
          } else {
            _clangSema->Diags.Report(tt.getLocation(),lexerError)
                          << ( "Expected an identifier after the backslash: " + text(tt));
            continue;
          }
        } else if (text(t) == "@") {
          continue; // In ACSL '@' is a space
        } else {
          _clangSema->Diags.Report(t.getLocation(),lexerWarning)
                        << ( "Skipping unknown token: " + text(t));
          continue; // Just skip token
        }
      } else {
        _token = convertClangTokenToACSLToken(t);
        setLocation(t.getLocation(),t.getEndLoc());
        if (!t.getLocation().isValid() && debug)
          std::cout << "BEGIN LOC INVALID " + str(t) << std::endl;
        if (!t.getEndLoc().isValid() && debug)
          std::cout << "END LOC INVALID " + str(t) << std::endl;

        size_t p;
        if (t.is(clang::tok::TokenKind::identifier)) {
          _clangTokens.pop_front();
        } else if (t.is(clang::tok::TokenKind::numeric_constant)) {
          if ((p=text(t).find("..")) != std::string::npos) {
            // .. within a numeric PP token
            std::string ts = text(t);
            std::string t1 = ts.substr(0,p);
            std::string t2 = ts.substr(p+2,std::string::npos);

            _clangTokens.pop_front();
            if (!t2.empty()) reparseWithClang(t2,t.getLocation().getLocWithOffset(p+2));
            reparseWithClang("..",t.getLocation().getLocWithOffset(p));
            if (!t1.empty()) reparseWithClang(t1,t.getLocation());
            continue; // Now go back to pick off the first token
          } else {
            _clangTokens.pop_front();
            // FIXME - should we check here whether the PP numeric token is a valid lexer numeric token
          }
        } else if (text(t) == "<=") {
          _clangTokens.pop_front();
          clang::Token& tt = _clangTokens.front();
          clang::Token& ttt = *(++_clangTokens.begin());
          if (text(tt) == "=" && text(ttt) == ">") {
            _token = OperatorPunctuatorToken().setType(
                OperatorPunctuatorToken::TEquiv);
            setLocation(t.getLocation(),ttt.getEndLoc());
            _clangTokens.pop_front();
            _clangTokens.pop_front();
          }
        } else if (text(t) == "==") {
          _clangTokens.pop_front();
          clang::Token& tt = _clangTokens.front();
          if (text(tt) == ">") {
            _token = OperatorPunctuatorToken().setType(
                OperatorPunctuatorToken::TImplies);
            setLocation(t.getLocation(),tt.getEndLoc());
            _clangTokens.pop_front();
          }
        } else if (text(t) == "..") {
          _token = OperatorPunctuatorToken().setType(
              OperatorPunctuatorToken::TRange);
          setLocation(t.getLocation(),t.getEndLoc());
          _clangTokens.pop_front();
        } else if (text(t) == ".") {
          _clangTokens.pop_front();
          clang::Token& tt = _clangTokens.front();
          clang::Token& ttt = *(++_clangTokens.begin());
          if (text(tt) == ".") {
            if (text(ttt) == ".") { // FIXME - Ellipsis within a numeric token?  Ellipsis a CLang token of its own?
              _token = OperatorPunctuatorToken().setType(
                  OperatorPunctuatorToken::TEllipsis);
              setLocation(t.getLocation(),ttt.getEndLoc());
              _clangTokens.pop_front();
              _clangTokens.pop_front();
            } else {
              _token = OperatorPunctuatorToken().setType(
                  OperatorPunctuatorToken::TRange);
              setLocation(t.getLocation(),tt.getEndLoc());
              _clangTokens.pop_front();
            }
          }

        } else {
          _clangTokens.pop_front();
        }
      }
      if (debug) {
        std::cout << " NEW TOKEN " << _token.str() << std::endl;
      }
      return RRHasToken;
    }
    _hasFinished = true;
    return RRFinished;

  }
  ReadResult r =  readToken(_buffer, _position, _tokenLocation);
  if (debug && r == RRHasToken) {
    std::cout << " ACSL TOKEN " << _token.str() << std::endl;
  }
  return r;
}

void
Lexer::reparseWithClang(const std::string& text, clang::SourceLocation clangLoc) {
  Lexer lexer2(_clangSema);
  lexer2.setBuffer(text,clangLoc,0,true);
  auto iter = lexer2._clangTokens.rbegin();
  while (iter != lexer2._clangTokens.rend()) {
    _clangTokens.push_front(*iter++);
  }
}


bool
Lexer::sameLocation(const clang::SourceLocation& begin, const clang::SourceLocation& end) const {
  clang::SourceManager& sm = _clangSema->getPreprocessor().getSourceManager();
  clang::PresumedLoc PLoc = sm.getPresumedLoc(begin);
  clang::PresumedLoc PLoc2 = sm.getPresumedLoc(end);
  if (PLoc.getLine() != PLoc2.getLine()) return false;
  if (PLoc.getColumn() != PLoc2.getColumn()) return false;
  if (strcmp(PLoc.getFilename(),PLoc2.getFilename()) != 0) return false;
  return true;
}

void
Lexer::setLocation(const clang::SourceLocation& begin, const clang::SourceLocation& end) {
  clang::SourceManager& sm = _clangSema->getPreprocessor().getSourceManager();
  clang::PresumedLoc PLoc = sm.getPresumedLoc(begin);
  _tokenLocation->filename1 = strdup(PLoc.getFilename());
  _tokenLocation->linenum1 = PLoc.getLine();
  _tokenLocation->charnum1 = PLoc.getColumn();
  PLoc = sm.getPresumedLoc(end);
  _tokenLocation->filename2 = strdup(PLoc.getFilename());
  _tokenLocation->linenum2 = PLoc.getLine();
  _tokenLocation->charnum2 = PLoc.getColumn();
}

Lexer::ReadResult Lexer::readToken(const std::string& buffer, size_t& position, location loc)
  { ReadResult r;
    do { r = readMain(buffer, position, loc);
    } while ( r == RRContinueLexing);
    //if (r == RRHasToken) std::cout << "  READ " << _token.str() << std::endl;
    return r;
  }

std::string
Lexer::str(const clang::Token& t) const {
  std::ostringstream s;
  s << t.getName() << " " << _clangSema->getPreprocessor().getSpelling(t) << " " << t.getLocation().printToString(_clangSema->getPreprocessor().getSourceManager())
              << " " << t.getEndLoc().printToString(_clangSema->getPreprocessor().getSourceManager());
  return s.str();
}

std::string
Lexer::str(const clang::SourceLocation& loc) const {
  std::ostringstream s;
  s << loc.printToString(_clangSema->getPreprocessor().getSourceManager());
  return s.str();
}

std::string
Lexer::text(const clang::Token& t) const {
  return _clangSema->getPreprocessor().getSpelling(t);
}

Lexer::ReadResult
Lexer::readMain(const std::string& buffer, size_t& position, location loc) {
  if (!_token_stack.empty()) {
    ReadResult res = RRHasToken;
    _token = _token_stack.top();
    _token_stack.pop();
    _token = expandIfMacro(_token, res);
    return res;
  }
  loc->linenum1 = loc->linenum2;
  loc->charnum1 = loc->charnum2+1;
  if (_hasNewlineToken) {
    _hasNewlineToken = false;
    ++loc->linenum1;
    loc->charnum1 = 1;
  };
  char ch = skipSpace(buffer,position,loc);
  if (ch == '/' && buffer[position+1] == '*') {
    // Embedded block comment - abort
    _revised = _revised.substr(0,position);
    //_errorList.push_back(Error(loc,"Block comments may not be nested inside specification annotations - aborting processing comment"));
    return RRFinished;
  }
  if (ch == '\0') return RRFinished;

  loc->linenum2 = loc->linenum1;
  loc->charnum2 = loc->charnum1-1;
  switch (ch) {
    case '\\':
      _context = ch;
      advanceChar2NoToken(buffer,position,loc);
      return readProtectedToken(buffer, position, loc);
    case '<':
      if (buffer.length() - position < 4) getMoreCharacters();
      if (buffer[position+1] == '=') {
        if (buffer[position+2] == '=') {
          if (buffer[position+3] == '>') {
            position += 4;
            loc->charnum2 += 4;
            _token = OperatorPunctuatorToken().setType(
                OperatorPunctuatorToken::TEquiv);
            return RRHasToken;
          };
        };
        position += 2;
        loc->charnum2 += 2;
        _token = OperatorPunctuatorToken().setType(
            OperatorPunctuatorToken::TLessOrEqual);
        return RRHasToken;
      }
      else if (buffer[position+1] == '-') {
        if (buffer[position+2] == '-') {
          if (buffer[position+3] == '>') {
            position += 4;
            loc->charnum2 += 4;
            _token = OperatorPunctuatorToken().setType(
                OperatorPunctuatorToken::TBitEquiv);
            return RRHasToken;
          };
        };
      }
      else if (buffer[position+1] == '<') {
        if (buffer[position+2] == '=') {
          position += 3;
          loc->charnum2 += 3;
          _token = OperatorPunctuatorToken().setType(
              OperatorPunctuatorToken::TLeftShiftAssign);
          return RRHasToken;
        };
        position += 2;
        loc->charnum2 += 2;
        _token = OperatorPunctuatorToken().setType(
            OperatorPunctuatorToken::TLeftShift);
        return RRHasToken;
      }
      else if (buffer[position+1] == ':') {
        position += 2;
        loc->charnum2 += 2;
        _token = OperatorPunctuatorToken().setType(
            OperatorPunctuatorToken::TLTColon);
        return RRHasToken;
      };
      position += 1;
      loc->charnum2 += 1;
      _token = OperatorPunctuatorToken().setType(
          OperatorPunctuatorToken::TLess);
      return RRHasToken;
    case '>':
      if (buffer.length() - position < 3) getMoreCharacters();
      if (buffer[position+1] == '=') {
        position += 2;
        loc->charnum2 += 2;
        _token = OperatorPunctuatorToken().setType(
            OperatorPunctuatorToken::TGreaterOrEqual);
        return RRHasToken;
      }
      else if (buffer[position+1] == '>') {
        if (buffer[position+2] == '=') {
          position += 3;
          loc->charnum2 += 3;
          _token = OperatorPunctuatorToken().setType(
              OperatorPunctuatorToken::TRightShiftAssign);
          return RRHasToken;
        };
        position += 2;
        loc->charnum2 += 2;
        _token = OperatorPunctuatorToken().setType(
            OperatorPunctuatorToken::TRightShift);
        return RRHasToken;
      };
      position += 1;
      loc->charnum2 += 1;
      _token = OperatorPunctuatorToken().setType(
          OperatorPunctuatorToken::TGreater);
      return RRHasToken;
    case '!':
      if (buffer.length() - position < 2) getMoreCharacters();
      if (buffer[position+1] == '=') {
        position += 2;
        loc->charnum2 += 2;
        _token = OperatorPunctuatorToken().setType(
            OperatorPunctuatorToken::TDifferent);
        return RRHasToken;
      }
      position += 1;
      loc->charnum2 += 1;
      _token = OperatorPunctuatorToken().setType(OperatorPunctuatorToken::TNot);
      return RRHasToken;
    case '=':
      if (buffer.length() - position < 3) getMoreCharacters();
      if (buffer[position+1] == '=') {
        if (buffer[position+2] == '>') {
          position += 3;
          loc->charnum2 += 3;
          _token = OperatorPunctuatorToken().setType(
              OperatorPunctuatorToken::TImplies);
          return RRHasToken;
        };
        position += 2;
        loc->charnum2 += 2;
        _token = OperatorPunctuatorToken().setType(
            OperatorPunctuatorToken::TEqual);
        return RRHasToken;
      };
      position += 1;
      loc->charnum2 += 1;
      _token = OperatorPunctuatorToken().setType(
          OperatorPunctuatorToken::TAssign);
      return RRHasToken;
    case '&':
      if (buffer.length() - position < 2) getMoreCharacters();
      if (buffer[position+1] == '&') {
        position += 2;
        loc->charnum2 += 2;
        _token = OperatorPunctuatorToken().setType(
            OperatorPunctuatorToken::TLogicalAnd);
        return RRHasToken;
      }
      else if (buffer[position+1] == '=') {
        position += 2;
        loc->charnum2 += 2;
        _token = OperatorPunctuatorToken().setType(
            OperatorPunctuatorToken::TBitAndAssign);
        return RRHasToken;
      }
      position += 1;
      loc->charnum2 += 1;
      _token = OperatorPunctuatorToken().setType(
          OperatorPunctuatorToken::TAmpersand);
      return RRHasToken;
    case '|':
      if (buffer.length() - position < 2) getMoreCharacters();
      if (buffer[position+1] == '|') {
        position += 2;
        loc->charnum2 += 2;
        _token = OperatorPunctuatorToken().setType(
            OperatorPunctuatorToken::TLogicalOr);
        return RRHasToken;
      }
      else if (buffer[position+1] == '=') {
        position += 2;
        loc->charnum2 += 2;
        _token = OperatorPunctuatorToken().setType(
            OperatorPunctuatorToken::TBitOrAssign);
        return RRHasToken;
      }
      position += 1;
      loc->charnum2 += 1;
      _token = OperatorPunctuatorToken().setType(
          OperatorPunctuatorToken::TBitOr);
      return RRHasToken;
    case '^':
      if (buffer.length() - position < 2) getMoreCharacters();
      if (buffer[position+1] == '^') {
        position += 2;
        loc->charnum2 += 2;
        _token = OperatorPunctuatorToken().setType(
            OperatorPunctuatorToken::TLogicalXor);
        return RRHasToken;
      }
      else if (buffer[position+1] == '=') {
        position += 2;
        loc->charnum2 += 2;
        _token = OperatorPunctuatorToken().setType(
            OperatorPunctuatorToken::TBitXorAssign);
        return RRHasToken;
      }
      position += 1;
      loc->charnum2 += 1;
      _token = OperatorPunctuatorToken().setType(
          OperatorPunctuatorToken::TBitXor);
      return RRHasToken;
    case '-':
      if (buffer.length() - position < 3) getMoreCharacters();
      if (buffer[position+1] == '-') {
        if (buffer[position+2] == '>') {
          position += 3;
          loc->charnum2 += 3;
          _token = OperatorPunctuatorToken().setType(
              OperatorPunctuatorToken::TBitImplies);
          return RRHasToken;
        };
        position += 2;
        loc->charnum2 += 2;
        _token = OperatorPunctuatorToken().setType(
            OperatorPunctuatorToken::TMinusMinus);
        return RRHasToken;
      }
      else if (buffer[position+1] == '>') {
        if (buffer[position+2] == '*') {
          position += 3;
          loc->charnum2 += 3;
          _token = OperatorPunctuatorToken().setType(
              OperatorPunctuatorToken::TArrowStar);
          return RRHasToken;
        };
        position += 2;
        loc->charnum2 += 2;
        _token = OperatorPunctuatorToken().setType(
            OperatorPunctuatorToken::TArrow);
        return RRHasToken;
      }
      else if (buffer[position+1] == '=') {
        position += 2;
        loc->charnum2 += 2;
        _token = OperatorPunctuatorToken().setType(
            OperatorPunctuatorToken::TMinusAssign);
        return RRHasToken;
      };
      position += 1;
      loc->charnum2 += 1;
      _token = OperatorPunctuatorToken().setType(
          OperatorPunctuatorToken::TMinus);
      return RRHasToken;
    case '+':
      if (buffer.length() - position < 2) getMoreCharacters();
      if (buffer[position+1] == '+') {
        position += 2;
        loc->charnum2 += 2;
        _token = OperatorPunctuatorToken().setType(
            OperatorPunctuatorToken::TPlusPlus);
        return RRHasToken;
      }
      else if (buffer[position+1] == '=') {
        position += 2;
        loc->charnum2 += 2;
        _token = OperatorPunctuatorToken().setType(
            OperatorPunctuatorToken::TPlusAssign);
        return RRHasToken;
      };
      position += 1;
      loc->charnum2 += 1;
      _token = OperatorPunctuatorToken().setType(
          OperatorPunctuatorToken::TPlus);
      return RRHasToken;
    case '{':
      position += 1;
      loc->charnum2 += 1;
      _token = OperatorPunctuatorToken().setType(
          OperatorPunctuatorToken::TOpenBrace);
      return RRHasToken;
    case '}':
      position += 1;
      loc->charnum2 += 1;
      _token = OperatorPunctuatorToken().setType(
          OperatorPunctuatorToken::TCloseBrace);
      return RRHasToken;
    case '[':
      position += 1;
      loc->charnum2 += 1;
      _token = OperatorPunctuatorToken().setType(
          OperatorPunctuatorToken::TOpenBracket);
      return RRHasToken;
    case ']':
      position += 1;
      loc->charnum2 += 1;
      _token = OperatorPunctuatorToken().setType(
          OperatorPunctuatorToken::TCloseBracket);
      return RRHasToken;
    case '(':
      position += 1;
      loc->charnum2 += 1;
      _token = OperatorPunctuatorToken().setType(
          OperatorPunctuatorToken::TOpenParen);
      return RRHasToken;
    case ')':
      position += 1;
      loc->charnum2 += 1;
      _token = OperatorPunctuatorToken().setType(
          OperatorPunctuatorToken::TCloseParen);
      return RRHasToken;
    case ';':
      position += 1;
      loc->charnum2 += 1;
      _token = OperatorPunctuatorToken().setType(
          OperatorPunctuatorToken::TSemiColon);
      return RRHasToken;
    case ':':
      if (buffer.length() - position < 2) getMoreCharacters();
      if (buffer[position+1] == ':') {
        position += 2;
        loc->charnum2 += 2;
        _token = OperatorPunctuatorToken().setType(
            OperatorPunctuatorToken::TColonColon);
        return RRHasToken;
      }
      else if (buffer[position+1] == '>') {
        position += 2;
        loc->charnum2 += 2;
        _token = OperatorPunctuatorToken().setType(
            OperatorPunctuatorToken::TColonGT);
        return RRHasToken;
      };
      position += 1;
      loc->charnum2 += 1;
      _token = OperatorPunctuatorToken().setType(
          OperatorPunctuatorToken::TColon);
      return RRHasToken;
    case '.':
      if (buffer.length() - position < 2) getMoreCharacters();
      if (buffer[position+1] == '.') {
        if (buffer[position+2] == '.') {
          position += 3;
          loc->charnum2 += 3;
          _token = OperatorPunctuatorToken().setType(
              OperatorPunctuatorToken::TEllipsis);
          return RRHasToken;
        };
        position += 2;
        loc->charnum2 += 2;
        _token = OperatorPunctuatorToken().setType(
            OperatorPunctuatorToken::TRange);
        return RRHasToken;
      }
      else if (buffer[position+1] == '*') {
        position += 2;
        loc->charnum2 += 2;
        _token = OperatorPunctuatorToken().setType(
            OperatorPunctuatorToken::TPunctStar);
        return RRHasToken;
      }
      else if (isdigit(buffer[position+1])) {
        advanceChar2(buffer,position,loc);
        _digits = Dec;
        _litState = FracPart;
        return readNumberToken(buffer, position, loc);
      }
      position += 1;
      loc->charnum2 += 1;
      _token = OperatorPunctuatorToken().setType(
          OperatorPunctuatorToken::TPunct);
      return RRHasToken;
    case '?':
      position += 1;
      loc->charnum2 += 1;
      _token = OperatorPunctuatorToken().setType(
          OperatorPunctuatorToken::TQuery);
      return RRHasToken;
    case '*':
      if (buffer.length() - position < 2) getMoreCharacters();
      if (buffer[position+1] == '=') {
        position += 2;
        loc->charnum2 += 2;
        _token = OperatorPunctuatorToken().setType(
            OperatorPunctuatorToken::TMultAssign);
        return RRHasToken;
      }
      position += 1;
      loc->charnum2 += 1;
      _token = OperatorPunctuatorToken().setType(
          OperatorPunctuatorToken::TStar);
      return RRHasToken;
    case '/':
      if (buffer.length() - position < 2) getMoreCharacters();
      if (buffer[position+1] == '=') {
        position += 2;
        loc->charnum2 += 2;
        _token = OperatorPunctuatorToken().setType(
            OperatorPunctuatorToken::TDivideAssign);
        return RRHasToken;
      }
      else if (buffer[position+1] == '/') {
        position += 2;
        loc->charnum2 += 2;
        _context = '/';
        return readEndComment(buffer, position, loc);
      }
      else if (buffer[position+1] == '*') {
        position += 2;
        loc->charnum2 += 2;
        _context = '*';
        return readEndComment(buffer, position, loc);
      };
      position += 1;
      loc->charnum2 += 1;
      _token = OperatorPunctuatorToken().setType(
          OperatorPunctuatorToken::TDivide);
      return RRHasToken;
    case '%':
      if (buffer.length() - position < 2) getMoreCharacters();
      if (buffer[position+1] == '=') {
        position += 2;
        loc->charnum2 += 2;
        _token = OperatorPunctuatorToken().setType(
            OperatorPunctuatorToken::TModuloAssign);
        return RRHasToken;
      }
      position += 1;
      loc->charnum2 += 1;
      _token = OperatorPunctuatorToken().setType(
          OperatorPunctuatorToken::TProcent);
      return RRHasToken;
    case '~':
      position += 1;
      loc->charnum2 += 1;
      _token = OperatorPunctuatorToken().setType(
          OperatorPunctuatorToken::TTilda);
      return RRHasToken;
    case ',':
      position += 1;
      loc->charnum2 += 1;
      _token = OperatorPunctuatorToken().setType(
          OperatorPunctuatorToken::TComma);
      return RRHasToken;
//    case '#':  // FIXME - fix interactions with checking for PP directives
//      position += 1;
//      loc->charnum2 += 1;
//      _token = OperatorPunctuatorToken().setType(
//          OperatorPunctuatorToken::THash);
//      return RRHasToken;
    case '\'':
      position+=1;
      loc->charnum2+=1;
      _charLitKind = DLexer::CharacterLiteralToken::TChar;
      return readCharLiteral(buffer,position,loc);
    case 'L':
      if (buffer[position+1] == '\'') {
        position+=2;
        loc->charnum2+=2;
        _charLitKind = DLexer::CharacterLiteralToken::TWideChar;
        return readCharLiteral(buffer,position,loc);
      } else break;
    case '0':
      advanceChar2(buffer,position,loc);
      _litState = LeadZero;
      return readNumberToken(buffer,position,loc);
    case '"':
      size_t i, n;
      for (i = 1, n = buffer.length();
           i < n && buffer[position+i] != '"' && buffer[position+i-1] != '\\';
           i++);
      if (position + i >= n) {
        std::cerr << "no closing double quotes before EOF" << std::endl;
        break;
      }
      std::string literal(buffer, position, i+1);
      DLexer::StringLiteralToken* result =
        new DLexer::StringLiteralToken(literal);
      _token = DLexer::Token(result);
      position += i+1;
      return RRHasToken;
  };
  if (isalpha(ch) || ch == '_') {
    ReadResult res = readIdentifierToken(buffer, position, loc);
    if (res == RRHasToken) {
      _token = expandIfMacro(_token,res);
      if (res == RRContinueLexing) return RRContinueLexing;
    }
    return res;
  };
  if (isdigit(ch)) {
    advanceChar2(buffer,position,loc);
    _digits = Dec;
    _litState = Digits;
    return readNumberToken(buffer, position, loc);
  };

  if (isUtf8SymbolStart(ch)) {
    return readUtf8Symbol(buffer,position,loc);
  }
  std::ostringstream msg;
  if (ch == '#') {
    size_t start = position;
    advanceChar1NoToken(buffer, position, loc);
    handlePPDirectiveInACSL(buffer, position, start, loc);
    return RRContinueLexing;
  } else {
    // illegal character. Just add an error message.
    msg << "unknown character C: " << ch << ".";
    _errorList.push_back(Error(loc, msg.str()));
    ++position; // otherwise, we're stuck in an infinite loop
  }
  return RRContinueLexing;
}

// FIXME - no check for out of place ELSE

const int PP_NO_ANNOTATION = 0; // Not in an if/ifdef/ifndef block
const int PP_IN_IF = 1; // Processing current statements
const int PP_SKIP_TO_ELIF = 2; // Skipping to a future elseif to test it
const int PP_SKIP_TO_END = 3; // Processed a true block, now skipping all elses to an endif

// PP_NO_ANNOTATION >> if/ifdef/ifndef true >> push current state, new state is PP_IN_IF
// PP_NO_ANNOTATION >> if/ifdef/ifndef false >> PP_SKIP_TO_ELIF
// PP_NO_ANNOTATION >> else/elif/endif : ERROR
// PP_IN_IF >> else/elif >> PP_SKIP_TO_END
// PP_IN_IF >> endif >> pop state (an error if state stack is empty)
// PP_IN_IF >> if/ifdef/ifndef >> nesting, push current state, new state is PP_IN_IF
// PP_SKIP_TO_ELIF >> else >> PP_IN_IF
// PP_SKIP_TO_ELIF >> elif true >> PP_IN_IF
// PP_SKIP_TO_ELIF >> elif false >> PP_SKIP_TO_ELIF
// PP_SKIP_TO_ELIF >> endif >> pop state (an error if state stack is empty)
// PP_SKIP_TO_ELIF >> if/ifdef/ifndef >> nesting, push current state, new state is PP_SKIP_TO_END
// PP_SKIP_TO_END >> if/ifdef/ifndef >> nesting, push current state, new state is PP_SKIP_TO_END
// PP_SKIP_TO_END >> else/elif >> PP_SKIP_TO_END
// PP_SKIP_TO_END >> endif >> pop state (an error if state stack is empty)

// FIXME - are unknown directives in skipped blocks errors?

int ppstate = PP_NO_ANNOTATION;
// Constant globals for the pre-defined preprocessor directives
const std::string pp_empty(" ");
const std::string pp_ifdef("ifdef");
const std::string pp_ifndef("ifndef");
const std::string pp_if("if");
const std::string pp_endif("endif");
const std::string pp_else("else");
const std::string pp_elif("elif");
const std::string pp_error("error");
const std::string pp_warning("warning");
const std::string pp_line("line");
const std::string pp_include("include");
const std::string pp_define("define");
const std::string pp_undef("undef");
const std::string pp_pragma("pragma");

std::stack<int> state_stack;

void Lexer::complainAboutExcessMaterial(const std::string& buffer, size_t& position, location loc, bool warn) {
  if (warn) {
    Error junkerror(loc,"");
    const std::string junk = getPreprocessorToken(buffer,position,loc,false,true);
    if (!junk.empty()) {
      std::ostringstream msg;
      msg << "Invalid excess material after preprocessor directive: " << junk;
      junkerror.message = msg.str();
      _errorList.push_back(junkerror);
    }
  }
  while (!getPreprocessorToken(buffer,position,loc,false,true).empty()) {}
}


// Requires that 'start' is the position of the '#' character
// and that the current token is the identifier following the '#' character
// (perhaps with intervening whitespace)
// and that the current position is just after the end of that identifier.
// Also presumes that the entire ACSL annotation (C++ comment is in buffer).
void Lexer::handlePPDirectiveInACSL(const std::string& buffer, size_t& position, size_t start, location loc) {
  const clang::SourceManager& sourceMgr = _clangSema->getPreprocessor().getSourceManager();
  const clang::FileID fileID = sourceMgr.getFileID(_clangSourceLocation);

  clang::SourceLocation hashloc = sourceMgr.translateLineCol(fileID,loc->linenum1,loc->charnum1);
  skipSpace(buffer,position,loc,false);
  clang::SourceLocation idloc = sourceMgr.translateLineCol(fileID,loc->linenum1,loc->charnum1);

  size_t p = position; // first char of identifier
  Lexer::readIdentifierToken(buffer, position, loc);
  // We either have a non-empty identifier, or a keyword, or an empty identifier
  // (if the next character is not a valid identifier start character, such as punctuation)
  std::string id(buffer,p,position-p);
  if (position == p) id = " ";

  std::ostringstream msg;
  bool complain;
  while (true) {
    complain = true;
    if (id.empty()) { // End of ACSL annotation with no directive
      if (ppstate != PP_NO_ANNOTATION) {
        msg << "ACSL annotation ended with missing #endif directive";
        _errorList.push_back(Error(loc, msg.str())); // FIXME - put in the location of the if?
      }
      ppstate = PP_NO_ANNOTATION;
      complain = false;
    } else if (id == pp_if) {
      state_stack.push(ppstate);
      skipUpToEndOfLine(buffer,position,loc);
      complain = false;
      if (ppstate == PP_NO_ANNOTATION) {
        if (!_ppCheckOnly) {
          std::string slice(buffer,start,position-start);
          msg << "#if is not implemented (Presuming true): " << slice;
          _clangSema->Diags.Report(idloc,ppError) << msg.str();
        }
        ppstate = PP_IN_IF;
      } else if (ppstate == PP_IN_IF) {
        if (!_ppCheckOnly) {
          std::string slice(buffer,start,position-start);
          msg << "#if is not implemented (Presuming true): " << slice;
          _clangSema->Diags.Report(idloc,ppError) << msg.str();
        }
        ppstate = PP_IN_IF;
      } else {
        skipUpToEndOfLine(buffer,position,loc);
        std::string slice(buffer,start,position-start);
        _errorList.push_back(Error(loc, msg.str()));
        ppstate = PP_SKIP_TO_END;
      }
    } else if (id == pp_elif) {
      skipUpToEndOfLine(buffer,position,loc);
      complain = false;
      if (!_ppCheckOnly) {
        std::string slice(buffer,start,position-start);
        msg << "#elif is not implemented (Presuming false): " << slice;
        _clangSema->Diags.Report(idloc,ppError) << msg.str();
      }
      ppstate = PP_SKIP_TO_ELIF;
    } else if (id == pp_ifdef || id == pp_ifndef) {
      state_stack.push(ppstate);
      bool negate = id == pp_ifndef;
      const std::string idd = getPreprocessorToken(buffer,position,loc,false,true);
      if (ppstate == PP_NO_ANNOTATION || ppstate == PP_IN_IF) {
        bool useBody = (negate != isDefinedMacro(idd));
        if (!useBody) {
          ppstate = PP_SKIP_TO_ELIF;
        } else {
          ppstate = PP_IN_IF;
        }
      } else {
        ppstate = PP_SKIP_TO_END;
      }
    } else if (id == pp_endif) {
      if (ppstate == PP_NO_ANNOTATION) {
        msg << "No matching #if for this #endif (ignoring line)";
        _clangSema->Diags.Report(idloc,ppError) << msg.str();
        removeFromRevision(start);
      } else {
        ppstate = state_stack.top();
        state_stack.pop();
      }
    } else if (id == pp_else) {
      if (ppstate == PP_NO_ANNOTATION) {
        msg << "No matching #if for this #else (ignoring line)";
        _clangSema->Diags.Report(idloc,ppError) << msg.str();
        removeFromRevision(start);
      } else if (ppstate == PP_IN_IF) {
        ppstate = PP_SKIP_TO_END;
      } else if (ppstate == PP_SKIP_TO_ELIF) {
        ppstate = PP_IN_IF;
      } else if (ppstate == PP_SKIP_TO_END) {
        // continue skipping to the next endif
      }
    } else if (id == pp_error || id == pp_warning) {
      // FIXME - does not check that the remainder of the line consists of valid tokens
      // Content is NOT macro substituted, per cpp documentation
      const std::string rest = skipUpToEndOfLine(buffer,position,loc);
      if (!_ppCheckOnly && (ppstate == PP_IN_IF || ppstate == PP_NO_ANNOTATION)) {
        _clangSema->Diags.Report(idloc,ppError) << rest;
      }
      complain = false;
    } else if (id == pp_include) {
      // FIXME - does not check that the remainder of the line consists of valid tokens
      // Content is NOT macro substituted, per cpp documentation
      const std::string rest = skipUpToEndOfLine(buffer,position,loc);
//      if (!_ppCheckOnly && (ppstate == PP_IN_IF || ppstate == PP_NO_ANNOTATION)) {
//        _clangSema->Diags.Report(idloc,ppError) << rest;
//      }
      complain = false;
    } else if (id == pp_line) {
      _clangSema->Diags.Report(idloc,ppWarning) << "#line directive not yet implemented";
//      Error number_error(loc,"");
//      const std::string number = getPreprocessorToken(buffer,position,loc,false,false);
//      int line;
//      bool failed = true;
//      if (number.empty()) {
//        msg << "No line number to read (ignoring #line directive)";
//        error.message = msg.str();
//        _errorList.push_back(error);
//        removeFromRevision(start);
//      } else if (number.find_first_not_of("0123456789",0,10) != std::string::npos) {
//        msg << "The number token in a #line directive must be all digits: " << number;
//        number_error.message = msg.str();
//        _errorList.push_back(number_error);
//        removeFromRevision(start);
//      } else try {
//        size_t p;
//        //line = std::string::stoi(number, &p);
//        line = atoi(number.c_str()); // FIXME - does not find errors
//        failed = false;
//      } catch (std::exception e) {
//        msg << "Failed to read line number (ignoring #line directive): " << number;
//        number_error.message = msg.str();
//        _errorList.push_back(number_error);
//        removeFromRevision(start);
//      }
//      if (failed) {
//        skipUpToEndOfLine(buffer,position,loc);
//        complain = false;
//      } else {
//        loc->linenum2 = line - 1; // The -1 is because we have yet to read the line termination at the end of line directive and the number in the line directive is the new number of the **next** line
//        Error filename_error(loc,"");
//        std::string filename = getPreprocessorToken(buffer,position,loc,false,false);
//        if (filename.empty()) {
//          // No filename present - OK
//        } else if (filename.c_str()[0] == '"') {
//          // OK - got a string
//          loc->filename2 = strdup(filename.c_str());
//        } else {
//          msg << "Failed to read filename (ignoring directive): " << std::string(buffer,start,position-start);;
//          filename_error.message = msg.str();
//          _errorList.push_back(filename_error);
//          removeFromRevision(start);
//        }
//        //skipUpToEndOfLine(buffer,position,loc);
//        // FIXME - complain about dangling material
//          // FIXME - locations for error messages on line and filename are not correct
//        // FIXME - needs macro expansion
//        // FIXME - how are comments supposed to be handled
//        // FIXME - are line directive used when in text that is being skipped
//          // FIXME - check for dangling #if blocks at end of annotation
//      }
    } else if (id == pp_define || id == pp_undef || id == pp_pragma) {
      skipUpToEndOfLine(buffer,position,loc);
      complain = false;
      std::string slice(buffer,start,position-start);
      msg << "Preprocessor directive is not permitted in ACSL++ annotation (ignoring line): " << slice;
      _clangSema->Diags.Report(idloc,ppError) << msg.str();
      removeFromRevision(start);
    } else if (id == " ") { // missing directive
      skipUpToEndOfLine(buffer,position,loc);
      complain = false;
      std::string slice(buffer,start,position-start);
      msg << "Missing preprocessor directive (ignoring line): " << slice;
      _clangSema->Diags.Report(hashloc,ppError) << msg.str();
      removeFromRevision(start);
    } else { // unknown directive
      skipUpToEndOfLine(buffer,position,loc);
      complain = false;
      std::string slice(buffer,start,position-start);
      msg << "Invalid preprocessor directive [" << id << "] (ignoring line): " << slice;
      _clangSema->Diags.Report(idloc,ppError) << msg.str();
      removeFromRevision(start);
    }
    complainAboutExcessMaterial(buffer,position,loc,complain);
    if (ppstate == PP_NO_ANNOTATION || ppstate == PP_IN_IF) break;
    id = skipToNextPPDirective(buffer,position,loc);
  }
}

//! Puts in comment markers to comment out a bad directive (to the end of line);
//! 'start' must be the position in the buffer of the '#' pp directive character
// FIXME - not valid if there is an embedded multi-line comment
// FIXME - not valid if there is a # immediately followed by newline
void
Lexer::removeFromRevision(size_t start) {
  if (_revised[start+1] == '\n') {
    _revised[start] = ' ';
  } else {
    _revised[start] = '/';
    _revised[start+1] = '/';
  }
  while (_revised[start] != '\n' && _revised[start] != 0) {
    _revised[start] = ' ';
    start++;
  }
}

// Advances position to the end-of-line character (or end of file), returning
// a string of the skipped over contents and updating 'position'
const std::string Lexer::skipUpToEndOfLine(const std::string& buffer, size_t& position, location loc) {
  size_t start = position;
	while (true) {
		char ch = buffer[position];
		if (ch == '\n' || ch == '\r' || ch == '\0') {
		  return std::string(buffer,start,position-start);
		}
    advanceChar1NoToken(buffer,position,loc);
	}
}

const std::string Lexer::getAndTrimRestOfLine(const std::string& buffer, size_t& position, location loc) {
  while (true) {
    char ch = buffer[position];
    if (!std::isspace(ch)) break;
    advanceChar1NoToken(buffer,position,loc);
  }
  size_t start = position;
  while (true) {
    char ch = buffer[position];
    if (std::isspace(ch)) break;
    if ((ch == '\n' || ch == '\r' || ch == '\0')) break;
    advanceChar1NoToken(buffer,position,loc);
  }
  size_t end = position;
  while (true) {
    char ch = buffer[position];
    if ((ch == '\n' || ch == '\r' || ch == '\0')) break;
    advanceChar1NoToken(buffer,position,loc);
  }

  return std::string(buffer, start, end - start);
}

// Advances character position
char Lexer::advanceChar1NoToken(const std::string& buffer, size_t& position, location loc) {
  char ch;
  while (true) {
    position++;
    loc->charnum1++;
    ch = buffer[position];
    if (ch == '\\') {
      size_t p = position;
      char c;
      do {
        c = buffer[++p];
      } while (c != '\n' && (isspace(c) || c == '@'));
      if (c == '\n') {
        // we just saw a backslash-whitespace-newline sequence; ignore it.
        loc->linenum1++;
        loc->charnum1 = 0;
        position = p;
        continue;
      }
    }
    break;
  }
  return ch;
}

// Advances character position
char Lexer::advanceChar2NoToken(const std::string& buffer, size_t& position, location loc) {
  char ch;
  while (true) {
    position++;
    loc->charnum2++;
    ch = buffer[position];
    if (ch == '\\') {
      size_t p = position;
      char c;
      do {
        c = buffer[++p];
      } while (c != '\n' && (isspace(c) || c == '@'));
      if (c == '\n') {
        // we just saw a backslash-whitespace-newline sequence; ignore it.
        loc->linenum1++;
        loc->charnum2 = 0;
        position = p;
        continue;
      }
    }
    break;
  }
  return ch;
}


bool Lexer::isDefinedMacro(const std::string& id) {
  clang::IdentifierInfo& identifierInfo
      = _clangSema->getPreprocessor().getIdentifierTable().get(id);
  return identifierInfo.hasMacroDefinition();
}

clang::MacroInfo*
Lexer::getMacro(const std::string& name) const {
  clang::IdentifierInfo& identifierInfo
    = _clangSema->getPreprocessor().getIdentifierTable().get(name);
  return _clangSema->getPreprocessor().getMacroInfo(&identifierInfo);
}



const std::string Lexer::skipToNextPPDirective(const std::string& buffer, size_t& position, location loc) {
  char ch;
  while (true) {
    unsigned int n = loc->linenum1;
    skipSpace(buffer, position, loc); // Use this routine so lines are properly counted
    ch = buffer[position];
    if (ch == '\0') return ""; // No token found
    bool atLineStart = (size_t) n != loc->linenum1;
    if (atLineStart && ch == '#') {
      n = loc->linenum1;
      advanceChar1NoToken(buffer,position,loc);
      skipSpace(buffer,position,loc);
      if ((size_t) n != loc->linenum1) {
        // FIXME - does not handle lines with only comments after the #
        // Empty directive
        return std::string(" ");
      }
      size_t start = position;
      while (!isspace(ch) && ch != '\0') {
        ch = advanceChar1NoToken(buffer,position,loc);
      }
      size_t end = position;
      return std::string(buffer,start,end-start);
    } else {
      atLineStart = false;
      ch = advanceChar1NoToken(buffer,position,loc); // Must not be a line ending
    }
  }
}

// FIXME replicates Clang_utils::makeLocation
// FIXME - I think the strdup strings here are never deleted, or else multiply deleted
location
Lexer::makeLocation(clang::SourceLocation source) const {
  clang::SourceManager& sm = _clangSema->getPreprocessor().getSourceManager();
  clang::PresumedLoc PLoc = sm.getPresumedLoc(source);
  if (PLoc.isValid()) {
    const char* f = strdup(PLoc.getFilename());
    size_t line = PLoc.getLine();
    size_t col = PLoc.getColumn();
    return cons_location(f,line,col,strdup(f),line,col);
  } else {
    return cons_location("",0,0,"",0,0);
  }
}

DLexer::Token
Lexer::convertClangTokenToACSLToken(const clang::Token& source) const {
  switch (source.getKind()) {
    case clang::tok::eof: // End of file.
    case clang::tok::eod: // End of preprocessing directive (end of line inside
                          //   a directive).
    case clang::tok::code_completion: // Code completion marker
      assert(false); // unimplemented
    case clang::tok::comment:
      { DLexer::CommentToken* result = new DLexer::CommentToken;
        result->content() = std::string(source.getLiteralData(),
            source.getLength());
        return DLexer::Token(result);
      };
    // C99 6.4.2: Identifiers.
    case clang::tok::identifier:          // abcde123
      { clang::IdentifierInfo* identifierInfo = source.getIdentifierInfo();
        std::string text = std::string(identifierInfo->getNameStart(),
            identifierInfo->getLength());

        KeywordToken::Map::const_iterator found =
          KeywordToken::_unprotectedKeywords.find(text);
        if (found != KeywordToken::_unprotectedKeywords.end()) {
          KeywordToken* result = new KeywordToken;
          result->setType(found->second);
          return DLexer::Token(result);
        }
        found =
          KeywordToken::_unicodeKeywords.find(text);
        if (found != KeywordToken::_unicodeKeywords.end()) {
          KeywordToken* result = new KeywordToken;
          result->setType(found->second);
          return DLexer::Token(result);
        }

        OperatorPunctuatorToken::Map::const_iterator foundp =
          OperatorPunctuatorToken::_unicodePunctuators.find(text);
        if (foundp != OperatorPunctuatorToken::_unicodePunctuators.end()) {
          OperatorPunctuatorToken* result = new OperatorPunctuatorToken;
          result->setType(foundp->second);
          return DLexer::Token(result);
        }

        {
          IdentifierToken* result = new IdentifierToken(text);
          return Token(AbstractToken::TIdentifier,result);
        }

      };
    case clang::tok::raw_identifier:      // Used only in raw lexing mode.
      { DLexer::IdentifierToken* result = new DLexer::IdentifierToken;
        result->content() = source.getRawIdentifier().str();
        return DLexer::Token(result);
      };

    // C99 6.4.4.1: Integer Constants
    // C99 6.4.4.2: Floating Constants
    case clang::tok::numeric_constant:
      // Clang does not distinguish between integer and floating literals:
      // we have to lex the constant properly ourselves.
      { llvm::SmallString<128> spellingBuffer;
        spellingBuffer.resize(source.getLength() + 1);
        bool isInvalid = false;
        std::string tokSpelling = _clangSema->getPreprocessor()
          .getSpelling(source, spellingBuffer, &isInvalid).str();
        if (isInvalid)
          return DLexer::Token();

        // FIXME - better to use a specialized routine than to make a whole new literal?
        Acsl::Lexer lexer(_clangSema);
        lexer.setBuffer(tokSpelling, _clangSourceLocation, 0, false);
        ReadResult readResult;
        do {
          readResult = lexer.readToken();
        } while (readResult <= Acsl::Lexer::RRContinueLexing);
        return lexer.extractToken();
      };

    // C99 6.4.4: Character Constants
    case clang::tok::char_constant:       // 'a'
    case clang::tok::wide_char_constant:  // L'b'
    // C++0x Character Constants
    case clang::tok::utf16_char_constant: // u'a'
    case clang::tok::utf32_char_constant: // U'a'
      // see clang::Sema::ActOnCharacterConstant
      { llvm::SmallString<16> charBuffer;
        bool isInvalid = false;
        std::string thisTok = _clangSema->getPreprocessor().getSpelling(source,
            charBuffer, &isInvalid).str();
        if (isInvalid)
          return DLexer::Token();
        ReadResult readResult;
        size_t position = 1;
        Acsl::Lexer lexer(_clangSema);
        lexer.setBuffer(thisTok, _clangSourceLocation, position, false); // FIXME - is this needed
        do {
          if (thisTok[0] == '\'') {
            lexer._charLitKind = CharacterLiteralToken::TChar;
          }
          else if (thisTok[0] == 'L' && thisTok[1] == '\'') {
            lexer._charLitKind = CharacterLiteralToken::TWideChar;
            position++;
          }

          readResult = lexer.readCharLiteral(thisTok, position, lexer.seeTokenLocation());
        } while (readResult <= Acsl::Lexer::RRContinueLexing);
        // FIXME - free the location
        Token tt = lexer.extractToken();
        return tt;
      };

    // C99 6.4.5: String Literals.
    case clang::tok::string_literal:      // "foo"
    case clang::tok::wide_string_literal: // L"foo"
#if CLANG_VERSION_MAJOR < 9
    case clang::tok::angle_string_literal:// <foo>
#endif
    // C++0x String Literals.
    case clang::tok::utf8_string_literal: // u8"foo"
    case clang::tok::utf16_string_literal:// u"foo"
    case clang::tok::utf32_string_literal:// U"foo"
      // see clang::Sema::ActOnStringLiteral
      // [TODO] note that multiple string tokens should be converted into
      // one string token!
      { DLexer::StringLiteralToken* result = new DLexer::StringLiteralToken(
          std::string(source.getLiteralData(), source.getLength()));
        return DLexer::Token(result);
      };

    // C99 6.4.6: Punctuators.
    case clang::tok::l_square:
      return DLexer::Token(DLexer::OperatorPunctuatorToken()
          .setType(DLexer::OperatorPunctuatorToken::TOpenBracket));
    case clang::tok::r_square:
      return DLexer::Token(DLexer::OperatorPunctuatorToken()
          .setType(DLexer::OperatorPunctuatorToken::TCloseBracket));
    case clang::tok::l_paren:
      return DLexer::Token(DLexer::OperatorPunctuatorToken()
          .setType(DLexer::OperatorPunctuatorToken::TOpenParen));
    case clang::tok::r_paren:
      return DLexer::Token(DLexer::OperatorPunctuatorToken()
          .setType(DLexer::OperatorPunctuatorToken::TCloseParen));
    case clang::tok::l_brace:
      return DLexer::Token(DLexer::OperatorPunctuatorToken()
          .setType(DLexer::OperatorPunctuatorToken::TOpenBrace));
    case clang::tok::r_brace:
      return DLexer::Token(DLexer::OperatorPunctuatorToken()
          .setType(DLexer::OperatorPunctuatorToken::TCloseBrace));
    case clang::tok::period:
      return DLexer::Token(DLexer::OperatorPunctuatorToken()
          .setType(DLexer::OperatorPunctuatorToken::TPunct));
    case clang::tok::ellipsis:
      return DLexer::Token(DLexer::OperatorPunctuatorToken()
          .setType(DLexer::OperatorPunctuatorToken::TEllipsis));
    case clang::tok::amp:
      return DLexer::Token(DLexer::OperatorPunctuatorToken()
          .setType(DLexer::OperatorPunctuatorToken::TAmpersand));
    case clang::tok::ampamp:
      return DLexer::Token(DLexer::OperatorPunctuatorToken()
          .setType(DLexer::OperatorPunctuatorToken::TLogicalAnd));
    case clang::tok::ampequal:
      return DLexer::Token(DLexer::OperatorPunctuatorToken()
          .setType(DLexer::OperatorPunctuatorToken::TBitAndAssign));
    case clang::tok::star:
      return DLexer::Token(DLexer::OperatorPunctuatorToken()
          .setType(DLexer::OperatorPunctuatorToken::TStar));
    case clang::tok::starequal:
      return DLexer::Token(DLexer::OperatorPunctuatorToken()
          .setType(DLexer::OperatorPunctuatorToken::TMultAssign));
    case clang::tok::plus:
      return DLexer::Token(DLexer::OperatorPunctuatorToken()
          .setType(DLexer::OperatorPunctuatorToken::TPlus));
    case clang::tok::plusplus:
      return DLexer::Token(DLexer::OperatorPunctuatorToken()
          .setType(DLexer::OperatorPunctuatorToken::TPlusPlus));
    case clang::tok::plusequal:
      return DLexer::Token(DLexer::OperatorPunctuatorToken()
          .setType(DLexer::OperatorPunctuatorToken::TPlusAssign));
    case clang::tok::minus:
      return DLexer::Token(DLexer::OperatorPunctuatorToken()
          .setType(DLexer::OperatorPunctuatorToken::TMinus));
    case clang::tok::arrow:
      return DLexer::Token(DLexer::OperatorPunctuatorToken()
          .setType(DLexer::OperatorPunctuatorToken::TArrow));
    case clang::tok::minusminus:
      return DLexer::Token(DLexer::OperatorPunctuatorToken()
          .setType(DLexer::OperatorPunctuatorToken::TMinusMinus));
    case clang::tok::minusequal:
      return DLexer::Token(DLexer::OperatorPunctuatorToken()
          .setType(DLexer::OperatorPunctuatorToken::TMinusAssign));
    case clang::tok::tilde:
      return DLexer::Token(DLexer::OperatorPunctuatorToken()
          .setType(DLexer::OperatorPunctuatorToken::TTilda));
    case clang::tok::exclaim:
      return DLexer::Token(DLexer::OperatorPunctuatorToken()
          .setType(DLexer::OperatorPunctuatorToken::TNot));
    case clang::tok::exclaimequal:
      return DLexer::Token(DLexer::OperatorPunctuatorToken()
          .setType(DLexer::OperatorPunctuatorToken::TDifferent));
    case clang::tok::slash:
      return DLexer::Token(DLexer::OperatorPunctuatorToken()
          .setType(DLexer::OperatorPunctuatorToken::TDivide));
    case clang::tok::slashequal:
      return DLexer::Token(DLexer::OperatorPunctuatorToken()
          .setType(DLexer::OperatorPunctuatorToken::TDivideAssign));
    case clang::tok::percent:
      return DLexer::Token(DLexer::OperatorPunctuatorToken()
          .setType(DLexer::OperatorPunctuatorToken::TProcent));
    case clang::tok::percentequal:
      return DLexer::Token(DLexer::OperatorPunctuatorToken()
          .setType(DLexer::OperatorPunctuatorToken::TModuloAssign));
    case clang::tok::less:
      return DLexer::Token(DLexer::OperatorPunctuatorToken()
          .setType(DLexer::OperatorPunctuatorToken::TLess));
    case clang::tok::lessless:
      return DLexer::Token(DLexer::OperatorPunctuatorToken()
          .setType(DLexer::OperatorPunctuatorToken::TLeftShift));
    case clang::tok::lessequal:
      return DLexer::Token(DLexer::OperatorPunctuatorToken()
          .setType(DLexer::OperatorPunctuatorToken::TLessOrEqual));
    case clang::tok::lesslessequal:
      return DLexer::Token(DLexer::OperatorPunctuatorToken()
          .setType(DLexer::OperatorPunctuatorToken::TLeftShiftAssign));
    case clang::tok::greater:
      return DLexer::Token(DLexer::OperatorPunctuatorToken()
          .setType(DLexer::OperatorPunctuatorToken::TGreater));
    case clang::tok::greatergreater:
      return DLexer::Token(DLexer::OperatorPunctuatorToken()
          .setType(DLexer::OperatorPunctuatorToken::TRightShift));
    case clang::tok::greaterequal:
      return DLexer::Token(DLexer::OperatorPunctuatorToken()
          .setType(DLexer::OperatorPunctuatorToken::TGreaterOrEqual));
    case clang::tok::greatergreaterequal:
      return DLexer::Token(DLexer::OperatorPunctuatorToken()
          .setType(DLexer::OperatorPunctuatorToken::TRightShiftAssign));
    case clang::tok::caret:
      return DLexer::Token(DLexer::OperatorPunctuatorToken()
          .setType(DLexer::OperatorPunctuatorToken::TBitXor));
    case clang::tok::caretequal:
      return DLexer::Token(DLexer::OperatorPunctuatorToken()
          .setType(DLexer::OperatorPunctuatorToken::TBitXorAssign));
    case clang::tok::pipe:
      return DLexer::Token(DLexer::OperatorPunctuatorToken()
          .setType(DLexer::OperatorPunctuatorToken::TBitOr));
    case clang::tok::pipepipe:
      return DLexer::Token(DLexer::OperatorPunctuatorToken()
          .setType(DLexer::OperatorPunctuatorToken::TLogicalOr));
    case clang::tok::pipeequal:
      return DLexer::Token(DLexer::OperatorPunctuatorToken()
          .setType(DLexer::OperatorPunctuatorToken::TBitOrAssign));
    case clang::tok::question:
      return DLexer::Token(DLexer::OperatorPunctuatorToken()
          .setType(DLexer::OperatorPunctuatorToken::TQuery));
    case clang::tok::colon:
      return DLexer::Token(DLexer::OperatorPunctuatorToken()
          .setType(DLexer::OperatorPunctuatorToken::TColon));
    case clang::tok::semi:
      return DLexer::Token(DLexer::OperatorPunctuatorToken()
          .setType(DLexer::OperatorPunctuatorToken::TSemiColon));
    case clang::tok::equal:
      return DLexer::Token(DLexer::OperatorPunctuatorToken()
          .setType(DLexer::OperatorPunctuatorToken::TAssign));
    case clang::tok::equalequal:
      return DLexer::Token(DLexer::OperatorPunctuatorToken()
          .setType(DLexer::OperatorPunctuatorToken::TEqual));
    case clang::tok::comma:
      return DLexer::Token(DLexer::OperatorPunctuatorToken()
          .setType(DLexer::OperatorPunctuatorToken::TComma));
    case clang::tok::hash:
      return DLexer::Token(DLexer::OperatorPunctuatorToken()
          .setType(DLexer::OperatorPunctuatorToken::THash));
    case clang::tok::hashhash:
    case clang::tok::hashat:
      notImplemented(source);
      assert(false);

    // C++ Support
    case clang::tok::periodstar:
      return DLexer::Token(DLexer::OperatorPunctuatorToken()
          .setType(DLexer::OperatorPunctuatorToken::TPunctStar));
    case clang::tok::arrowstar:
      return DLexer::Token(DLexer::OperatorPunctuatorToken()
          .setType(DLexer::OperatorPunctuatorToken::TArrowStar));
    case clang::tok::coloncolon:
      return DLexer::Token(DLexer::OperatorPunctuatorToken()
          .setType(DLexer::OperatorPunctuatorToken::TColonColon));

    // Objective C support.
    case clang::tok::at:
      assert(false); // unimplemented

    // CUDA support.
    case clang::tok::lesslessless:
    case clang::tok::greatergreatergreater:
      notImplemented(source);
      assert(false);

    // C99 6.4.1: Keywords.  These turn into kw_* tokens.
    case clang::tok::kw_auto:
      return DLexer::Token(DLexer::KeywordToken()
          .setType(DLexer::KeywordToken::TAuto));
    case clang::tok::kw_break:
      notImplemented(source);
      assert(false);
      // return DLexer::Token(DLexer::KeywordToken()
      //     .setType(DLexer::KeywordToken::TBreak));
    case clang::tok::kw_case:
      return DLexer::Token(DLexer::KeywordToken()
          .setType(DLexer::KeywordToken::TCase));
    case clang::tok::kw_char:
      return DLexer::Token(DLexer::KeywordToken()
          .setType(DLexer::KeywordToken::TChar));
    case clang::tok::kw_const:
      return DLexer::Token(DLexer::KeywordToken()
          .setType(DLexer::KeywordToken::TConst));
    case clang::tok::kw_continue:
      notImplemented(source);
      assert(false);
      // return DLexer::Token(DLexer::KeywordToken()
      //     .setType(DLexer::KeywordToken::TContinue));
    case clang::tok::kw_default:
      return DLexer::Token(new DLexer::IdentifierToken(text(source)));
    case clang::tok::kw_do:
      assert(false); // unimplemented
      // return DLexer::Token(DLexer::KeywordToken()
      //     .setType(DLexer::KeywordToken::TDo));
    case clang::tok::kw_double:
      return DLexer::Token(DLexer::KeywordToken()
          .setType(DLexer::KeywordToken::TDouble));
    case clang::tok::kw_else:
      return DLexer::Token(DLexer::KeywordToken()
          .setType(DLexer::KeywordToken::TElse));
    case clang::tok::kw_enum:
      return DLexer::Token(DLexer::KeywordToken()
          .setType(DLexer::KeywordToken::TEnum));
    case clang::tok::kw_extern:
      assert(false); // unimplemented
      // return DLexer::Token(DLexer::KeywordToken()
      //    .setType(DLexer::KeywordToken::TExtern));
    case clang::tok::kw_float:
      return DLexer::Token(DLexer::KeywordToken()
          .setType(DLexer::KeywordToken::TFloat));
    case clang::tok::kw_for:
      return DLexer::Token(DLexer::KeywordToken()
          .setType(DLexer::KeywordToken::TFor));
    case clang::tok::kw_goto:
      assert(false); // unimplemented
      // return DLexer::Token(DLexer::KeywordToken()
      //     .setType(DLexer::KeywordToken::TGoto));
    case clang::tok::kw_if:
      return DLexer::Token(DLexer::KeywordToken()
          .setType(DLexer::KeywordToken::TIf));
    case clang::tok::kw_inline:
      assert(false); // unimplemented
      // return DLexer::Token(DLexer::KeywordToken()
      //     .setType(DLexer::KeywordToken::TInline));
    case clang::tok::kw_int:
      return DLexer::Token(DLexer::KeywordToken()
          .setType(DLexer::KeywordToken::TInt));
    case clang::tok::kw_long:
      return DLexer::Token(DLexer::KeywordToken()
          .setType(DLexer::KeywordToken::TLong));
    case clang::tok::kw_register:
      assert(false); // unimplemented
      // return DLexer::Token(DLexer::KeywordToken()
      //     .setType(DLexer::KeywordToken::TRegister));
    case clang::tok::kw_restrict:
      assert(false); // unimplemented
      // return DLexer::Token(DLexer::KeywordToken()
      //     .setType(DLexer::KeywordToken::TRestrict));
    case clang::tok::kw_return:
      assert(false); // unimplemented
      // return DLexer::Token(DLexer::KeywordToken()
      //     .setType(DLexer::KeywordToken::TReturn));
    case clang::tok::kw_short:
      return DLexer::Token(DLexer::KeywordToken()
          .setType(DLexer::KeywordToken::TShort));
    case clang::tok::kw_signed:
      return DLexer::Token(DLexer::KeywordToken()
          .setType(DLexer::KeywordToken::TSigned));
    case clang::tok::kw_sizeof:
      return DLexer::Token(DLexer::KeywordToken()
          .setType(DLexer::KeywordToken::TSizeof));
    case clang::tok::kw_static:
      return DLexer::Token(DLexer::KeywordToken()
          .setType(DLexer::KeywordToken::TStatic));
    case clang::tok::kw_struct:
      return DLexer::Token(DLexer::KeywordToken()
          .setType(DLexer::KeywordToken::TStruct));
    case clang::tok::kw_switch:
      assert(false); // unimplemented
      // return DLexer::Token(DLexer::KeywordToken()
      //     .setType(DLexer::KeywordToken::TSwitch));
    case clang::tok::kw_typedef:
      assert(false); // unimplemented
      // return DLexer::Token(DLexer::KeywordToken()
      //     .setType(DLexer::KeywordToken::TTypedef));
    case clang::tok::kw_union:
      return DLexer::Token(DLexer::KeywordToken()
          .setType(DLexer::KeywordToken::TUnion));
    case clang::tok::kw_unsigned:
      return DLexer::Token(DLexer::KeywordToken()
          .setType(DLexer::KeywordToken::TUnsigned));
    case clang::tok::kw_void:
      return DLexer::Token(DLexer::KeywordToken()
          .setType(DLexer::KeywordToken::TVoid));
    case clang::tok::kw_volatile:
      return DLexer::Token(DLexer::KeywordToken()
          .setType(DLexer::KeywordToken::TVolatile));
    case clang::tok::kw_while:
      return DLexer::Token(DLexer::KeywordToken()
          .setType(DLexer::KeywordToken::TWhile));
    case clang::tok::kw__Alignas:
    case clang::tok::kw__Alignof:
    case clang::tok::kw__Atomic:
    case clang::tok::kw__Bool:
    case clang::tok::kw__Complex:
    case clang::tok::kw__Generic:
    case clang::tok::kw__Imaginary:
    case clang::tok::kw__Static_assert:
    case clang::tok::kw___func__:
    case clang::tok::kw___objc_yes:
    case clang::tok::kw___objc_no:
      assert(false); // unimplemented

    // C++ 2.11p1: Keywords.
    case clang::tok::kw_asm:
      assert(false); // unimplemented
      // return DLexer::Token(DLexer::KeywordToken()
      //     .setType(DLexer::KeywordToken::TAsm));
    case clang::tok::kw_bool:
      return DLexer::Token(DLexer::KeywordToken()
          .setType(DLexer::KeywordToken::TBool));
    case clang::tok::kw_catch:
      assert(false); // unimplemented
      // return DLexer::Token(DLexer::KeywordToken()
      //     .setType(DLexer::KeywordToken::TCatch));
    case clang::tok::kw_class:
      return DLexer::Token(DLexer::KeywordToken()
          .setType(DLexer::KeywordToken::TClass));
    case clang::tok::kw_const_cast:
      return DLexer::Token(DLexer::KeywordToken()
          .setType(DLexer::KeywordToken::TConstCast));
    case clang::tok::kw_delete:
      assert(false); // unimplemented
      // return DLexer::Token(DLexer::KeywordToken()
      //     .setType(DLexer::KeywordToken::TDelete));
    case clang::tok::kw_dynamic_cast:
      return DLexer::Token(DLexer::KeywordToken()
          .setType(DLexer::KeywordToken::TDynamicCast));
    case clang::tok::kw_explicit:
      assert(false); // unimplemented
      // return DLexer::Token(DLexer::KeywordToken()
      //     .setType(DLexer::KeywordToken::TExplicit));
    case clang::tok::kw_export:
      assert(false); // unimplemented
      // return DLexer::Token(DLexer::KeywordToken()
      //     .setType(DLexer::KeywordToken::TExport));
    case clang::tok::kw_false:
      return DLexer::Token(DLexer::KeywordToken()
          .setType(DLexer::KeywordToken::TFalse));
    case clang::tok::kw_friend:
      notImplemented(source);
      assert(false);
      // return DLexer::Token(DLexer::KeywordToken()
      //     .setType(DLexer::KeywordToken::TFriend));
    case clang::tok::kw_mutable:
      notImplemented(source);
      assert(false);
      // return DLexer::Token(DLexer::KeywordToken()
      //     .setType(DLexer::KeywordToken::TMutable));
    case clang::tok::kw_namespace:
      notImplemented(source);
      assert(false);
      // return DLexer::Token(DLexer::KeywordToken()
      //     .setType(DLexer::KeywordToken::TNamespace));
    case clang::tok::kw_new:
      notImplemented(source);
      assert(false);
      // return DLexer::Token(DLexer::KeywordToken()
      //     .setType(DLexer::KeywordToken::TNew));
    case clang::tok::kw_operator:
      return DLexer::Token(DLexer::KeywordToken()
          .setType(DLexer::KeywordToken::TOperator));
    case clang::tok::kw_private:
      notImplemented(source);
      assert(false);
      // return DLexer::Token(DLexer::KeywordToken()
      //     .setType(DLexer::KeywordToken::TPrivate));
    case clang::tok::kw_protected:
      notImplemented(source);
      assert(false);
      // return DLexer::Token(DLexer::KeywordToken()
      //     .setType(DLexer::KeywordToken::TProtected));
    case clang::tok::kw_public:
      notImplemented(source);
      assert(false);
      // return DLexer::Token(DLexer::KeywordToken()
      //     .setType(DLexer::KeywordToken::TPublic));
    case clang::tok::kw_reinterpret_cast:
      return DLexer::Token(DLexer::KeywordToken()
          .setType(DLexer::KeywordToken::TReinterpretCast));
    case clang::tok::kw_static_cast:
      return DLexer::Token(DLexer::KeywordToken()
          .setType(DLexer::KeywordToken::TStaticCast));
    case clang::tok::kw_template:
      notImplemented(source);
      assert(false);
      // return DLexer::Token(DLexer::KeywordToken()
      //     .setType(DLexer::KeywordToken::TTemplate));
    case clang::tok::kw_this:
      { DLexer::IdentifierToken* result = new DLexer::IdentifierToken;
         result->content() = "this";
         return DLexer::Token(result);
      }
    case clang::tok::kw_throw:
      notImplemented(source);
      assert(false);
      // return DLexer::Token(DLexer::KeywordToken()
      //     .setType(DLexer::KeywordToken::TThrow));
    case clang::tok::kw_true:
      return DLexer::Token(DLexer::KeywordToken()
          .setType(DLexer::KeywordToken::TTrue));
    case clang::tok::kw_try:
      notImplemented(source);
      assert(false);
      // return DLexer::Token(DLexer::KeywordToken()
      //     .setType(DLexer::KeywordToken::TTry));
    case clang::tok::kw_typename:
      return DLexer::Token(DLexer::KeywordToken()
          .setType(DLexer::KeywordToken::TTypename));
    case clang::tok::kw_typeid:
      notImplemented(source);
      assert(false);
      // return DLexer::Token(DLexer::KeywordToken()
      //     .setType(DLexer::KeywordToken::TTypeid));
    case clang::tok::kw_using:
      notImplemented(source);
      assert(false);
      // return DLexer::Token(DLexer::KeywordToken()
      //     .setType(DLexer::KeywordToken::TUsing));
    case clang::tok::kw_virtual:
      return DLexer::Token(DLexer::KeywordToken()
          .setType(DLexer::KeywordToken::TVirtual));
    case clang::tok::kw_wchar_t:
      return DLexer::Token(DLexer::KeywordToken()
          .setType(DLexer::KeywordToken::TWcharT));

    default:
      notImplemented(source);
  }
  return DLexer::Token();
}

void
Lexer::notImplemented(const clang::Token& source) const {
  std::cerr << "Not implemented: " << str(source) << std::endl;
  assert(false); // unimplemented
}

clang::MacroArgs*
Lexer::readFunctionLikeMacroArgs(const std::string& identifier,
    clang::MacroInfo *macro) {
  // clang comment: The number of fixed arguments to parse.
#if CLANG_VERSION_MAJOR < 5
  unsigned numFixedArgsLeft = macro->getNumArgs();
#else
  unsigned numFixedArgsLeft = macro->getNumParams();
#endif
  bool isVariadic = macro->isVariadic();

  // argTokens - Build up a list of tokens that make up each argument.  Each
  // argument is separated by an EOF token.  Use a SmallVector so we can avoid
  // heap allocations in the common case.
  llvm::SmallVector<clang::Token, 64> argTokens;
  Lexer::ReadResult parseResult = RRHasToken;

  unsigned numActuals = 0;
  DLexer::AbstractToken readToken = queryToken();
  while (parseResult != Lexer::RRFinished
      && (readToken.getType() != DLexer::AbstractToken::TOperatorPunctuator
        || ((const DLexer::OperatorPunctuatorToken&) readToken).getType()
            != DLexer::OperatorPunctuatorToken::TCloseParen)) {
    assert(readToken.getType() == DLexer::AbstractToken::TOperatorPunctuator);
    DLexer::OperatorPunctuatorToken::Type firstTokenType =
      ((const DLexer::OperatorPunctuatorToken&) readToken).getType();
    assert(firstTokenType == DLexer::OperatorPunctuatorToken::TOpenParen
        || firstTokenType == DLexer::OperatorPunctuatorToken::TComma);
    // "l-paren-ness?", "only expect argument separators here"

    // C99 6.10.3p11: Keep track of the number of l_parens we have seen.  Note
    // that we already consumed the first one.
    unsigned numParens = 0;

    clearToken();
    while (1) {
      // Read arguments as unexpanded tokens.  This avoids issues, e.g., where
      // an argument value in a macro could expand to ',' or '(' or ')'.
      do {
        eatToken(parseResult);
      } while (parseResult != Lexer::RRHasToken
          && parseResult != Lexer::RRFinished);
      readToken = queryToken();

      if (parseResult == Lexer::RRFinished) // "#if f(<eof>" & "#if f(\n"
        break;
      else if (readToken.getType() == DLexer::AbstractToken::TOperatorPunctuator
        && ((const DLexer::OperatorPunctuatorToken&) readToken).getType()
            == DLexer::OperatorPunctuatorToken::TCloseParen) {
        // If we found the ) token, the macro arg list is done.
        if (numParens-- == 0)
          break;
      }
      else if (readToken.getType() == DLexer::AbstractToken::TOperatorPunctuator
        && ((const DLexer::OperatorPunctuatorToken&) readToken).getType()
            == DLexer::OperatorPunctuatorToken::TOpenParen)
        ++numParens;
      else if (numParens == 0
        && readToken.getType() == DLexer::AbstractToken::TOperatorPunctuator
        && ((const DLexer::OperatorPunctuatorToken&) readToken).getType()
            == DLexer::OperatorPunctuatorToken::TComma) {
        // Comma ends this argument if there are more fixed arguments expected.
        // However, if this is a variadic macro, and this is part of the
        // variadic part, then the comma is just an argument token.
        if (!isVariadic)
          break;
        if (numFixedArgsLeft > 1)
          break;
      }
      argTokens.push_back(convertToClang(extractToken()));
    }

    // If this was an empty argument list foo(), don't add this as an empty
    // argument.
    if (argTokens.empty()
        && (readToken.getType() == DLexer::AbstractToken::TOperatorPunctuator
        && ((const DLexer::OperatorPunctuatorToken&) readToken).getType()
            == DLexer::OperatorPunctuatorToken::TCloseParen))
      break;

    // If this is not a variadic macro, and too many args were specified, emit
    // an error.
    if (!isVariadic && numFixedArgsLeft == 0)
      return 0;

    // Add a marker EOF token to the end of the token list for this argument.
    clang::Token EOFTok;
    EOFTok.startToken();
    EOFTok.setKind(clang::tok::eof);
    // EOFTok.setLocation(Tok.getLocation());
    EOFTok.setLength(0);
    argTokens.push_back(EOFTok);
    ++numActuals;
    assert(numFixedArgsLeft != 0 && "Too many arguments parsed");
    --numFixedArgsLeft;
  }

  // Okay, we either found the r_paren.  Check to see if we parsed too few
  // arguments.
#if CLANG_VERSION_MAJOR < 5
  unsigned minArgsExpected = macro->getNumArgs();
#else
  unsigned minArgsExpected = macro->getNumParams();
#endif

  // See MacroArgs instance var for description of this.
  assert(numActuals == minArgsExpected);
  return clang::MacroArgs::create(macro, argTokens, false,
      _clangSema->getPreprocessor());
}

void
Lexer::eatToken(ReadResult& result) {
  if (_stateLexer == SLMacroTokens) {
    while (!_macroTokensStack.empty() && _macroTokensStack.back().empty()) {
       _macroTokensStack.pop_back();
       if (_currentMacroArgumentsStack.back())
         _currentMacroArgumentsStack.back()
           ->destroy(_clangSema->getPreprocessor());
       _currentMacroArgumentsStack.pop_back();
    }
    if (!_macroTokensStack.empty()) {
      std::pair<unsigned, DLexer::AbstractToken*>&
        token = _macroTokensStack.back().front();
      setToken(DLexer::Token(token.first, token.second));
      _macroTokensStack.back().pop_front();
      result = RRHasToken;
    }
    else {
      _usedMacros.clear();
      _stringsForToken.clear();
      _stateLexer = SLStandard;
    };
  }
  else
    assert(_stateLexer == SLStandard);
  if (_stateLexer == SLStandard) {
    result = readToken();
//    if (hasErrors())   // FIXME - what to do with this now that this code is in the Lexer
//      addErrorMessagesFromLexer();
  };
  if (result == RRHasToken) {
    DLexer::AbstractToken::Type type = queryToken().getType();
    if (type == DLexer::AbstractToken::TComment)
      result = RRContinueLexing;
  };
}

// FIXME - do we need this
// Converts an ACSL token to a Clang token
clang::Token
Lexer::convertToClang(DLexer::Token source) const {
  DLexer::AbstractToken token = source.getFullToken();
  switch (token.getType()) {
    case DLexer::AbstractToken::TIdentifier:
      { clang::Token identifierToken;
        identifierToken.startToken();
        identifierToken.clearFlag(clang::Token::NeedsCleaning);
        identifierToken.setIdentifierInfo(0);
        const std::string& identifier = ((const DLexer::IdentifierToken&)
              source.getContent()).content();
        // std::memset(&identifierToken, 0, sizeof(clang::Token));
        identifierToken.setLength(identifier.size());
        identifierToken.setLocation(_clangSourceLocation /* .getLocWithOffset(...) */);
        identifierToken.setKind(clang::tok::raw_identifier);
        _stringsForToken.push_back(identifier);
        identifierToken.setRawIdentifierData(_stringsForToken.back().c_str());
        return identifierToken;
      };
    case DLexer::AbstractToken::TKeyword:
      { clang::Token result;
        // result.setLength(...);
        // result.setLocation(...);
        switch (((const DLexer::KeywordToken&) token).getType()) {
          case DLexer::KeywordToken::TAuto:
            result.setKind(clang::tok::kw_auto);
            break;
          case DLexer::KeywordToken::TBool:
            result.setKind(clang::tok::kw_bool);
            break;
          case DLexer::KeywordToken::TCase:
            result.setKind(clang::tok::kw_case);
            break;
          case DLexer::KeywordToken::TChar:
            result.setKind(clang::tok::kw_char);
            break;
          case DLexer::KeywordToken::TClass:
            result.setKind(clang::tok::kw_class);
            break;
          case DLexer::KeywordToken::TConst:
            result.setKind(clang::tok::kw_const);
            break;
          case DLexer::KeywordToken::TConstCast:
            result.setKind(clang::tok::kw_const_cast);
            break;
          case DLexer::KeywordToken::TDouble:
            result.setKind(clang::tok::kw_double);
            break;
          case DLexer::KeywordToken::TDynamicCast:
            result.setKind(clang::tok::kw_dynamic_cast);
            break;
          case DLexer::KeywordToken::TElse:
            result.setKind(clang::tok::kw_else);
            break;
          case DLexer::KeywordToken::TEnum:
            result.setKind(clang::tok::kw_enum);
            break;
          case DLexer::KeywordToken::TFalse:
            result.setKind(clang::tok::kw_false);
            break;
          case DLexer::KeywordToken::TFloat:
            result.setKind(clang::tok::kw_float);
            break;
          case DLexer::KeywordToken::TFor:
            result.setKind(clang::tok::kw_for);
            break;
          case DLexer::KeywordToken::TIf:
            result.setKind(clang::tok::kw_if);
            break;
          case DLexer::KeywordToken::TInt:
            result.setKind(clang::tok::kw_int);
            break;
          case DLexer::KeywordToken::TLong:
            result.setKind(clang::tok::kw_long);
            break;
          case DLexer::KeywordToken::TOperator:
            result.setKind(clang::tok::kw_operator);
            break;
          case DLexer::KeywordToken::TReinterpretCast:
            result.setKind(clang::tok::kw_reinterpret_cast);
            break;
          case DLexer::KeywordToken::TShort:
            result.setKind(clang::tok::kw_short);
            break;
          case DLexer::KeywordToken::TSigned:
            result.setKind(clang::tok::kw_signed);
            break;
          case DLexer::KeywordToken::TSizeof:
            result.setKind(clang::tok::kw_sizeof);
            break;
          case DLexer::KeywordToken::TStatic:
            result.setKind(clang::tok::kw_static);
            break;
          case DLexer::KeywordToken::TStaticCast:
            result.setKind(clang::tok::kw_static_cast);
            break;
          case DLexer::KeywordToken::TStruct:
            result.setKind(clang::tok::kw_struct);
            break;
          case DLexer::KeywordToken::TTrue:
            result.setKind(clang::tok::kw_true);
            break;
          case DLexer::KeywordToken::TTypeId:
            result.setKind(clang::tok::kw_typeid);
            break;
          case DLexer::KeywordToken::TTypename:
            result.setKind(clang::tok::kw_typename);
            break;
          case DLexer::KeywordToken::TUnion:
            result.setKind(clang::tok::kw_union);
            break;
          case DLexer::KeywordToken::TUnsigned:
            result.setKind(clang::tok::kw_unsigned);
            break;
          case DLexer::KeywordToken::TVirtual:
            result.setKind(clang::tok::kw_virtual);
            break;
          case DLexer::KeywordToken::TVoid:
            result.setKind(clang::tok::kw_void);
            break;
          case DLexer::KeywordToken::TVolatile:
            result.setKind(clang::tok::kw_volatile);
            break;
          case DLexer::KeywordToken::TWcharT:
            result.setKind(clang::tok::kw_wchar_t);
            break;
          case DLexer::KeywordToken::TWhile:
            result.setKind(clang::tok::kw_while);
            break;
          default:
            break;
        };
        return result;
      };
    case DLexer::AbstractToken::TLiteral:
      { // result.setLength(...);
        // result.setLocation(...);
        clang::Token result;
        result.startToken();
        result.clearFlag(clang::Token::NeedsCleaning);
        result.setIdentifierInfo(0);
        // std::memset(&result, 0, sizeof(clang::Token));
        // result.setLocation(getSourceLocation(BufferPtr, TokLen));

        switch (((const DLexer::LiteralToken&) token).getType()) {
          case DLexer::LiteralToken::TInteger:
            result.setKind(clang::tok::numeric_constant);    // 0x123
            { std::ostringstream out;
              out << ((const DLexer::IntegerLiteralToken&)
                  source.getContent()).getValue();
              _stringsForToken.push_back(out.str());
              result.setLength(_stringsForToken.back().size());
              result.setLiteralData(_stringsForToken.back().c_str());
            };
            break;
          case DLexer::LiteralToken::TCharacter:
            result.setKind(clang::tok::char_constant);       // 'a'
            { std::string value;
              value += ((const DLexer::CharacterLiteralToken&)
                  source.getContent()).getChar();
              _stringsForToken.push_back(value);
              result.setLength(_stringsForToken.back().size());
              result.setLiteralData(_stringsForToken.back().c_str());
            };
            break;
          case DLexer::LiteralToken::TFloating:
            result.setKind(clang::tok::numeric_constant);    // 0x123
            { std::ostringstream out;
              out << ((const DLexer::FloatingLiteralToken&)
                  source.getContent()).getValueAsString();
              _stringsForToken.push_back(out.str());
              result.setLength(_stringsForToken.back().size());
              result.setLiteralData(_stringsForToken.back().c_str());
            };
            break;
          case DLexer::LiteralToken::TString:
            result.setKind(clang::tok::string_literal);      // "foo"
            _stringsForToken.push_back(((const DLexer::StringLiteralToken&)
                  source.getContent()).content());
              result.setLength(_stringsForToken.back().size());
            result.setLiteralData(_stringsForToken.back().c_str());
            break;
          default:
            break;
        };
        return result;
      };
    case DLexer::AbstractToken::TOperatorPunctuator:
      { clang::Token result;
        switch (((const DLexer::OperatorPunctuatorToken&) token).getType()) {
          case DLexer::OperatorPunctuatorToken::TOpenBrace:
            result.setKind(clang::tok::l_brace);
            break;
          case DLexer::OperatorPunctuatorToken::TCloseBrace:
            result.setKind(clang::tok::r_brace);
            break;
          case DLexer::OperatorPunctuatorToken::TOpenBracket:
            result.setKind(clang::tok::l_square);
            break;
          case DLexer::OperatorPunctuatorToken::TCloseBracket:
            result.setKind(clang::tok::r_square);
            break;
          case DLexer::OperatorPunctuatorToken::TOpenParen:
            result.setKind(clang::tok::l_paren);
            break;
          case DLexer::OperatorPunctuatorToken::TCloseParen:
            result.setKind(clang::tok::r_paren);
            break;
          case DLexer::OperatorPunctuatorToken::TSemiColon:
            result.setKind(clang::tok::semi);
            break;
          case DLexer::OperatorPunctuatorToken::TColon:
            result.setKind(clang::tok::colon);
            break;
          case DLexer::OperatorPunctuatorToken::TEllipsis:
            result.setKind(clang::tok::ellipsis);
            break;
          case DLexer::OperatorPunctuatorToken::TQuery:
            result.setKind(clang::tok::question);
            break;
          case DLexer::OperatorPunctuatorToken::TColonColon:
            result.setKind(clang::tok::coloncolon);
            break;
          case DLexer::OperatorPunctuatorToken::TPunct:
            result.setKind(clang::tok::period);
            break;
          case DLexer::OperatorPunctuatorToken::TPunctStar:
            result.setKind(clang::tok::periodstar);
            break;
          case DLexer::OperatorPunctuatorToken::TComma:
            result.setKind(clang::tok::comma);
            break;
          case DLexer::OperatorPunctuatorToken::TArrowStar:
            result.setKind(clang::tok::arrowstar);
            break;
          case DLexer::OperatorPunctuatorToken::TArrow:
            result.setKind(clang::tok::arrow);
            break;
          case DLexer::OperatorPunctuatorToken::TPlus:
            result.setKind(clang::tok::plus);
            break;
          case DLexer::OperatorPunctuatorToken::TMinus:
            result.setKind(clang::tok::minus);
            break;
          case DLexer::OperatorPunctuatorToken::TStar:
            result.setKind(clang::tok::star);
            break;
          case DLexer::OperatorPunctuatorToken::TDivide:
            result.setKind(clang::tok::slash);
            break;
          case DLexer::OperatorPunctuatorToken::TProcent:
            result.setKind(clang::tok::percent);
            break;
          case DLexer::OperatorPunctuatorToken::TBitXor:
            result.setKind(clang::tok::caret);
            break;
          case DLexer::OperatorPunctuatorToken::TAmpersand:
            result.setKind(clang::tok::amp);
            break;
          case DLexer::OperatorPunctuatorToken::TBitOr:
            result.setKind(clang::tok::pipe);
            break;
          case DLexer::OperatorPunctuatorToken::TTilda:
            result.setKind(clang::tok::tilde);
            break;
          case DLexer::OperatorPunctuatorToken::TNot:
            result.setKind(clang::tok::exclaim);
            break;
          case DLexer::OperatorPunctuatorToken::TAssign:
            result.setKind(clang::tok::equal);
            break;
          case DLexer::OperatorPunctuatorToken::TLess:
            result.setKind(clang::tok::less);
            break;
          case DLexer::OperatorPunctuatorToken::TGreater:
            result.setKind(clang::tok::greater);
            break;
          case DLexer::OperatorPunctuatorToken::TPlusAssign:
            result.setKind(clang::tok::plusequal);
            break;
          case DLexer::OperatorPunctuatorToken::TMinusAssign:
            result.setKind(clang::tok::minusequal);
            break;
          case DLexer::OperatorPunctuatorToken::TMultAssign:
            result.setKind(clang::tok::starequal);
            break;
          case DLexer::OperatorPunctuatorToken::TDivideAssign:
            result.setKind(clang::tok::slashequal);
            break;
          case DLexer::OperatorPunctuatorToken::TModuloAssign:
            result.setKind(clang::tok::percentequal);
            break;
          case DLexer::OperatorPunctuatorToken::TBitXorAssign:
            result.setKind(clang::tok::caretequal);
            break;
          case DLexer::OperatorPunctuatorToken::TBitAndAssign:
            result.setKind(clang::tok::ampequal);
            break;
          case DLexer::OperatorPunctuatorToken::TBitOrAssign:
            result.setKind(clang::tok::pipeequal);
            break;
          case DLexer::OperatorPunctuatorToken::TLeftShift:
            result.setKind(clang::tok::lessless);
            break;
          case DLexer::OperatorPunctuatorToken::TRightShift:
            result.setKind(clang::tok::greatergreater);
            break;
          case DLexer::OperatorPunctuatorToken::TLeftShiftAssign:
            result.setKind(clang::tok::lesslessequal);
            break;
          case DLexer::OperatorPunctuatorToken::TRightShiftAssign:
            result.setKind(clang::tok::greatergreaterequal);
            break;
          case DLexer::OperatorPunctuatorToken::TEqual:
            result.setKind(clang::tok::equalequal);
            break;
          case DLexer::OperatorPunctuatorToken::TDifferent:
            result.setKind(clang::tok::exclaimequal);
            break;
          case DLexer::OperatorPunctuatorToken::TLessOrEqual:
            result.setKind(clang::tok::lessequal);
            break;
          case DLexer::OperatorPunctuatorToken::TGreaterOrEqual:
            result.setKind(clang::tok::greaterequal);
            break;
          case DLexer::OperatorPunctuatorToken::TLogicalAnd:
            result.setKind(clang::tok::ampamp);
            break;
          case DLexer::OperatorPunctuatorToken::TLogicalOr:
            result.setKind(clang::tok::pipepipe);
            break;
          case DLexer::OperatorPunctuatorToken::TPlusPlus:
            result.setKind(clang::tok::plusplus);
            break;
          case DLexer::OperatorPunctuatorToken::TMinusMinus:
            result.setKind(clang::tok::minusminus);
            break;
          default:
            break;
        };
        return result;
      };
    case DLexer::AbstractToken::TComment:
      { clang::Token commentToken;
        commentToken.startToken();
        commentToken.clearFlag(clang::Token::NeedsCleaning);
        commentToken.setIdentifierInfo(0);
        // std::memset(&commentToken, 0, sizeof(clang::Token));
        const std::string& comment = ((const DLexer::CommentToken&)
              source.getContent()).content();
        commentToken.setLength(comment.size());
        // commentToken.setLocation(getSourceLocation(BufferPtr, TokLen));
        commentToken.setKind(clang::tok::comment);
        _stringsForToken.push_back(comment);
        commentToken.setLiteralData(_stringsForToken.back().c_str());
        return commentToken;
      };
    default:
      break;
  };
  return clang::Token();
}

void Lexer::lexUsingClang(const clang::Sema* _sema,  const std::string& input, clang::SourceLocation loc, std::list<clang::Token>& clangTokens) {
  clang::Preprocessor& pp = _sema->getPreprocessor();
  clang::SourceManager& _sourceManager = pp.getSourceManager();

  clang::PresumedLoc PLoc = _sourceManager.getPresumedLoc(loc);
  if (!PLoc.isValid()) {
    std::cout << "Invalid location for " << input << " " << str(loc) << std::endl;
  }
  const char* f = strdup(PLoc.getFilename());
  size_t line = PLoc.getLine();
  size_t col = PLoc.getColumn();
  clangTokens.clear();

  // This is a hack to make error positions come out right. There does not seem to be a way to
  // tell clang or a MemoryBuffer where to presume the material starts.

  std::ostringstream prefix;
  for (size_t i = 1; i<line; i++) prefix << "\n";
  for (size_t i = 1; i<col; i++) prefix << " "; // FIXME - original file may have had tabs

  // Append to the input exactly one token at the end of the string, so we can recognize when
  // the input has been fully lexed.
  std::string datastr = prefix.str() + input + " *";

  // Create a clang 'File' out of an llvm memory buffer that points to a copy of the ACSL text
  clang::FileID newFile = _sourceManager.createFileID(
                                    llvm::MemoryBuffer::getMemBufferCopy(datastr, llvm::Twine(f)));

  // Now declare that file as the lexer source
  bool res = pp.EnterSourceFile(newFile, pp.GetCurDirLookup(), loc);
  if (res) {
    // Error occurred
    // FIXME make a regular error message
    std::cerr << "Error on trying to parse annotation text" << std::endl;
    return ;
  }

  // And lex from it. We have to observe and catch the end of the string; otherwise
  // the Lexer, on reaching the end of this input, will pop the include stack and
  // continue lexing the next file. In some cases this is the file that contained
  // the text we are lexing now, causing an infinite loop (since we have not returned
  // from handling the comment, so the comment has not yet been discarded).
  clang::Token t;
  unsigned endmarker = datastr.size()-1;
  unsigned offset;
  while (true) {
    pp.Lex(t);

    // offset is the position in the character buffer
    offset = (_sourceManager.getDecomposedExpansionLoc(t.getLocation())).second;

    // FIXME - eof does not have the right location
    // FIXME - we get eof sometimes but not always?  just ending comments?
    if (t.is(clang::tok::eof)) break;
    if (offset >= endmarker) {
      //std::cerr << "Yes we do need the extra eof check" << std::endl;
      break;
    }
    clangTokens.push_back(t);
  }
  bool debug = false;
  if (debug) {
    std::cout << clangTokens.size() << " TOKENS" << std::endl;
    std::cout << "INPUT: " << input << std::endl;
    std::list<clang::Token>::const_iterator iter = clangTokens.begin();
    while (iter != clangTokens.end()) {
      clang::Token t = *iter;
      if (!t.getLocation().isValid()) std::cout << "BEGIN LOC INVALID " + str(t) << std::endl;
      if (!t.getEndLoc().isValid()) std::cout << "END LOC INVALID " + str(t) << std::endl;
      std::cout << "    CLANG-TOKEN " << str(*iter++) << std::endl;
    }
  }

}




} // end of namespace Acsl

