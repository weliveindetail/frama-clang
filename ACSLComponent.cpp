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
//   Implementation of the ACSL++ components.
//

#include "ACSLComponent.h"
#include "Clang_utils.h"
#include "clang/AST/DeclTemplate.h"
#include <sstream>
#include <cstdio>

namespace Acsl {

using namespace DLexer;

Parser::ReadResult
  Locations::readToken(Parser::State& state, Parser::Arguments& arguments) {
  enum Delimiters { DBegin, DLocation, DNothing };
  ReadResult result = RRNeedChars;
  switch (state.point()) {
    DefineParseCase(Begin) {
      AbstractToken token = arguments.queryToken();
      if (token.getType() == AbstractToken::TKeyword) {
        if (((const KeywordToken&) token).getType() == 
            KeywordToken::TNothing) {
          if (_locations.getFront()) {
            DefineAddError("\\nothing cannot be mixed with a list of lvalues")
            DefineReduceAndParse
          }
          else DefineGotoCase(Nothing)
        }
      };
      TermOrPredicate* term = new TermOrPredicate;
      state.absorbRuleResult(&term->setTerm());
      DefineShiftAndParse(Location,*term,&TermOrPredicate::readToken)
    }
    DefineParseCase(Location) {
      Parser::State::RuleAccess::TCastFromRule<TermOrPredicate>
          node(state.getRuleResult());
      logic_type ltype = NULL;
      term location = node->extractTermOrSet(arguments,ltype);
      state.freeRuleResult();
      if (!location) {
        DefineAddError("expecting a location");
        DefineReduceAndParse
      }
      _locations.insertContainer(location);
      AbstractToken token = arguments.queryToken();
      switch (token.getType()) {
        case AbstractToken::TOperatorPunctuator:
          { OperatorPunctuatorToken::Type type =
            ((const OperatorPunctuatorToken&)token).getType();
            if (type == OperatorPunctuatorToken::TComma) {
              DefineGotoCase(Begin)
            }
            else DefineReduceAndParse
          }
        default: DefineReduceAndParse
      }
    }
    DefineParseCase(Nothing) {
      AbstractToken token = arguments.queryToken();
      switch (token.getType()) {
        case AbstractToken::TOperatorPunctuator: {
          OperatorPunctuatorToken::Type type =
            ((const OperatorPunctuatorToken&)token).getType();
          if (type == OperatorPunctuatorToken::TComma) {
            DefineAddError("\\nothing cannot be mixed with a list of lvalues")
            DefineReduceAndParse
          } else DefineReduceAndParse
        }
        default: DefineReduceAndParse
      }
    }
    default:
      DefineAddError("internal error in parsing locations list")
  }
  return RRNeedChars;
}

Parser::ReadResult 
AssignsClause::readToken(Parser::State& state, Parser::Arguments& arguments) {
  enum Delimiters { DBegin, DLocation, DFrom, DEnd };
  ReadResult result = RRNeedChars;
  switch (state.point()) {
    DefineInitParseCase(Begin) {
      Locations* modified = new Locations(copy_loc(_loc));
      state.absorbRuleResult(modified);
      DefineShiftAndParse(Location,*modified,&Locations::readToken)
    }
    DefineParseCase(Location)
      { Parser::State::RuleAccess::TCastFromRule<Locations>
          node(state.getRuleResult());
        /*term*/ForwardList locations = node->getResult();
        state.freeRuleResult();
        AbstractToken token = arguments.queryToken();
        switch (token.getType()) {
          case AbstractToken::TOperatorPunctuator: {
            OperatorPunctuatorToken::Type type =
              ((const OperatorPunctuatorToken&)token).getType();
            if (type == OperatorPunctuatorToken::TSemiColon) {
              list modified = locations.getFront();
              while(modified) {
                term loc = (term)modified->element.container;
                _clause.insertContainer(from_cons(loc,deps_FromAny()));
                modified = modified -> next;
              }
              DefineReduceAndParse
            } else {
              DefineAddError(
                std::string("unexpected token '")
                .append(token.str()).append("' after assigns clause"))
              DefineReduceAndParse
            }
          }
          case AbstractToken::TKeyword: {
            KeywordToken::Type type = ((const KeywordToken &)token).getType();
              if (type == KeywordToken::TFrom) {
                if (locations.getFront()) {
                  _modified.append(locations);
                  DefineGotoCase(From)
                } else {
                  DefineAddError(
                    "'assigns \nothing' cannot have a '\from' part")
                  DefineReduceAndParse
                }
              }
              else {
                DefineAddError(std::string("unexpected token '")
                  .append(token.str()).append("' after assigns clause"))
                DefineReduceAndParse
              }
            }
          default:
            DefineAddError(std::string("unexpected token '").append(token.str())
              .append("' after assigns clause"))
            DefineReduceAndParse
        }
      }
    DefineParseCase(From) {
      Locations* froms =
        new Locations(arguments.newTokenLocation());
      state.absorbRuleResult(froms);
      DefineShiftAndParse(End,*froms,&Locations::readToken)
    }
    DefineParseCase(End) {
      Parser::State::RuleAccess::TCastFromRule<Locations>
        node(state.getRuleResult());
      /*term*/ForwardList locations = node->getResult();
      state.freeRuleResult();
      /*term*/list assigned = _modified.getFront();
      deps from = deps_From(locations.getFront());
      while (assigned) {
        term location = (term)assigned->element.container;
        _clause.insertContainer(from_cons(term_dup(location),deps_dup(from)));
        assigned = assigned->next;
      }
      DefineReduceAndParse
    }
    default:
      DefineAddError("internal error in parsing assigns clause")
  }
  return RRNeedChars;
}

Parser::ReadResult
AllocFreeClause::readToken(
  Parser::State& state, Parser::Arguments& arguments) {
  enum Delimiters { DBegin, DEnd };
  ReadResult result = RRNeedChars;
  switch (state.point()) {
    DefineInitParseCase(Begin) {
      Locations* alloc = new Locations(copy_loc(_loc));
      state.absorbRuleResult(alloc);
      DefineShiftAndParse(End,*alloc,&Locations::readToken)
    }
    DefineParseCase(End) {
      Parser::State::RuleAccess::TCastFromRule<Locations>
        node(state.getRuleResult());
      /*term*/ForwardList locations = node->getResult();
      state.freeRuleResult();
      _clause = _clause.append(locations);
      DefineReduceAndParse
    }
    default:
      DefineAddError("internal error in parsing frees/allocates clause")
  }
  return RRNeedChars;
}
} // end of namespace Acsl

