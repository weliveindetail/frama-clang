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
//   Implementation of the ACSL code annotations, like an assert.
//

#include "ACSLCodeAnnotation.h"

namespace Acsl {

using namespace DLexer;

Parser::ReadResult
CodeAnnotation::readToken(Parser::State& state, Parser::Arguments& arguments)
{ enum Delimiters
  { DBegin, DAssert, DForId, DAfterForId, DEnd };

  ReadResult result = RRNeedChars;
  switch (state.point()) {
    DefineParseCase(Begin)
      arguments.setCodeAnnotContext();
      // Logic label Pre, Here and Old are always present,
      // Post only exists in post-condition, assigns and allocates
      arguments.addLogicLabel("Pre");
      arguments.addLogicLabel("Here");
      arguments.addLogicLabel("Old");
      { AbstractToken token = arguments.queryToken();
        if (token.getType() == AbstractToken::TKeyword) {
          KeywordToken::Type type = ((const KeywordToken&) token).getType();
          if (type == KeywordToken::TAssert) {
            TermOrPredicate* pred = new TermOrPredicate;
            state.absorbRuleResult(&pred->setPredicate());
            { logic_type thisRecordType = arguments.queryThisType();
              if (thisRecordType)
                arguments.addLogicFormal("this", thisRecordType);
            }
            DefineShift(Assert, *pred, &TermOrPredicate::readToken)
          }
          if (type == KeywordToken::TFor) {
            if (_behaviors)
              DefineAddError("multiple 'for' behaviors in code annotation")
            DefineGotoCase(ForId)
          }
        };
      }
      arguments.resetAnnotContext();
      DefineAddError("expecting 'assert' or 'for' in code annotation")
      DefineGotoCaseAndParse(End)
    DefineParseCase(Assert)
      { Parser::State::RuleAccess::TCastFromRule<TermOrPredicate>
          rule(state.getRuleResult());
        predicate_named pred = rule->extractPredicate(arguments);
        state.freeRuleResult();
        if (pred) {
          _annotResult = code_annotation_Assert(_behaviors, pred);
          _behaviors = NULL;
          _behaviorAdder.clear();
        }
        else {
          arguments.resetAnnotContext();
          DefineAddError("expecting a predicate");
        }
      }
      DefineGotoCaseAndParse(End)
    DefineParseCase(ForId)
      if (arguments.queryToken().getType() == AbstractToken::TIdentifier) {
        const IdentifierToken& token
            = (const IdentifierToken&) arguments.getContentToken();
        _behaviorAdder.insertContainer(strdup(token.content().c_str()));
        DefineGotoCase(AfterForId)
      }
      if (arguments.queryToken().getType() == AbstractToken::TKeyword) {
        const KeywordToken& token
            = (const KeywordToken&) arguments.getContentToken();
        _behaviorAdder.insertContainer(strdup(token.text().c_str()));
        DefineGotoCase(AfterForId)
      }
      arguments.resetAnnotContext();
      DefineAddError("expecting identifier after 'for' in code annotation")
      DefineGotoCaseAndParse(End)
    DefineParseCase(AfterForId)
      { AbstractToken token = arguments.queryToken();
        if (token.getType() == AbstractToken::TOperatorPunctuator) {
          OperatorPunctuatorToken::Type
            type = ((const OperatorPunctuatorToken&) token).getType();
          if (type == OperatorPunctuatorToken::TComma)
            DefineGotoCase(ForId)
          if (type == OperatorPunctuatorToken::TColon)
            DefineGotoCase(Begin)
        };
      }
      arguments.resetAnnotContext();
      DefineAddError("expecting ',' or ':' in a code annotation")
      DefineGotoCaseAndParse(End)
    DefineParseCase(End)
      { AbstractToken token = arguments.queryToken();
        if (token.getType() == AbstractToken::TOperatorPunctuator) {
          OperatorPunctuatorToken::Type
            type = ((const OperatorPunctuatorToken&) token).getType();
          if (type == OperatorPunctuatorToken::TSemiColon) {
            arguments.resetAnnotContext();
            DefineReduce
              }
        };
      }
      arguments.resetAnnotContext();
      DefineAddError("expecting ';' at the end of a code annotation")
      DefineGotoCase(End)
  }
  return result;
}

} // end of namespace Acsl

