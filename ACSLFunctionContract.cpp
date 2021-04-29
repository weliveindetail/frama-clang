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
//   Implementation of the ACSL function contracts.
//

#include "ACSLComponent.h"

namespace Acsl {

using namespace DLexer;

#if defined(__clang__) || defined(__GNUC__)
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wunused-label"
#endif

const std::string default_behavior_name("default!");

Parser::ReadResult
FunctionContract::error_empty_behavior(Parser::Arguments& arguments) {
  DefineAddError (
    strcat(strdup("Empty behavior "), ((behavior)
       _spec->behavior->element.container)->beh_name))
  return RRNeedChars;
}

Parser::ReadResult
FunctionContract::check_bhv_position(Parser::Arguments& arguments) {
  switch (_state) {
    case BHV:
      return error_empty_behavior(arguments);
    case COMPLETE:
      DefineAddError ("behavior after complete/disjoint clauses")
      return RRNeedChars;
    default:
      return RRNeedChars;
  }
}

Parser::ReadResult
FunctionContract::check_terminates_position(Parser::Arguments& arguments) {
  switch (_state) {
    case BHV:
      DefineAddError("terminates clause in behavior")
      return RRNeedChars;
    case ASSUMES:
      DefineAddError("terminates clause after assumes")
      return RRNeedChars;
    case POST_COND:
      DefineAddError("terminates clause after post-condition")
      return RRNeedChars;
    case TERMINATES:
      DefineAddError("at most one terminates clause is allowed")
      return RRNeedChars;
    case VARIANT:
      DefineAddError("terminates clause after decreases clause")
      return RRNeedChars;
    case COMPLETE:
      DefineAddError("terminates clause after complete/disjoint clause")
      return RRNeedChars;
    case REQUIRES:
      if (_spec->behavior &&  strcmp( ((behavior) ((list)_spec->behavior)->element.plain )->beh_name, default_behavior_name.c_str()) != 0) {
        DefineAddError("terminates clause in behavior")
      }
      return RRNeedChars;
    default:
      return RRNeedChars;
  }
}

Parser::ReadResult
FunctionContract::check_variant_position(Parser::Arguments& arguments) {
  switch (_state) {
    case BHV:
      DefineAddError("decreases in behavior")
      return RRNeedChars;
    case ASSUMES:
      DefineAddError("decreases after assumes")
      return RRNeedChars;
    case POST_COND:
      DefineAddError("decreases after post-condition")
      return RRNeedChars;
    case VARIANT:
      DefineAddError("at most one decreases clause is allowed")
      return RRNeedChars;
    case COMPLETE:
      DefineAddError("decreases after complete/disjoint clause")
      return RRNeedChars;
    case REQUIRES:
      if (_spec->behavior) {
        DefineAddError("decreases in behavior")
      }
      return RRNeedChars;
    default: return RRNeedChars;
  }
}

Parser::ReadResult
FunctionContract::check_assumes_position(Parser::Arguments& arguments) {
  switch(_state) {
    case START:
    case VARIANT:
    case TERMINATES:
      DefineAddError("assumes clause in default behavior")
      return RRNeedChars;
    case REQUIRES:
      DefineAddError("assumes clause after requires clause")
      return RRNeedChars;
    case POST_COND:
      DefineAddError("assumes clause after post-condition")
      return RRNeedChars;
    case COMPLETE:
      DefineAddError("assumes clause after complete/disjoint clauses")
      return RRNeedChars;
    default:
      return RRNeedChars;
  }
}

Parser::ReadResult
FunctionContract::check_requires_position(Parser::Arguments& arguments) {
  switch(_state) {
    case TERMINATES:
      DefineAddError("requires clause after terminates")
      return RRNeedChars;
    case POST_COND:
      DefineAddError("requires clause after post-condition")
      return RRNeedChars;
    case VARIANT:
      DefineAddError("requires clause after variant")
      return RRNeedChars;
    case COMPLETE:
      DefineAddError("requires clause after complete/disjoint clauses")
      return RRNeedChars;
    default:
      return RRNeedChars;
  }
}

Parser::ReadResult
FunctionContract::check_post_cond_position(Parser::Arguments& arguments) {
  switch(_state) {
    case COMPLETE:
      DefineAddError("post-condition after complete/disjoint clause")
      return RRNeedChars;
    default:
      return RRNeedChars;
  }
}

Parser::ReadResult
FunctionContract::check_complete_position(Parser::Arguments& arguments) {
  switch(_state) {
    case BHV:
      return error_empty_behavior (arguments);
    default:
      return RRNeedChars;
  }
}

void
FunctionContract::add_behavior(const std::string& name) {
  behavior bhv = behavior_cons(copy_string(name),NULL,NULL,NULL,
      assigns_WritesAny(), allocation_FreeAllocAny(), NULL);
  _currentBehavior.insertContainer(bhv);
  _currentRequires = bhv->requires;
  _currentAssumes = bhv->assumes;
  _currentPostCond = bhv->post_cond;
  _currentAssigns = ForwardList();
  _currentFrees = ForwardList ();
  _currentAllocates = ForwardList ();
}

Parser::ReadResult
FunctionContract::parseSemiColumn(Parser::Arguments& arguments,
    const std::string& msg) {
  AbstractToken token = arguments.queryToken();
  if (token.getType() == AbstractToken::TOperatorPunctuator) {
    OperatorPunctuatorToken::Type type = 
      ((const OperatorPunctuatorToken&) token).getType();
    if (type == OperatorPunctuatorToken::TSemiColon)
      return RRNeedChars;
    else
      DefineAddError(std::string("Expecting ';' after ").append(msg))
  }
  else
    DefineAddError(std::string("Expecting ';' after ").append(msg))
  return RRContinueParsing;
}

Parser::ReadResult
FunctionContract::readToken(Parser::State& state, Parser::Arguments& arguments)
{ ReadResult result = RRNeedChars;
  enum Delimiters
  { DBegin, DBehaviorName, DBehavior, DRequires, DRequiresEnd, DTerminates,
    DTerminatesEnd, DDecreases, DDecreasesFor, DDecreasesForIdent,
    DAssumes, DAssumesEnd, DPostCond, DPostCondEnd, DAssigns, DAssignsEnd,
    DComplete, DCompleteBehavior, DAfterComplete, DDisjoint, DDisjointBehavior,
    DAfterDisjoint, DBeforeSemiColon, DAllocatesFrees, DAllocatesFreesEnd
  };

  switch (state.point()) {
    DefineParseCase(Begin)
      arguments.setFunSpecContext();
      // Logic label Pre, Here and Old are always present,
      // Post only exists in post-condition, assigns and allocates
      arguments.addLogicLabel("Here");
      arguments.addLogicLabel("Pre");
      arguments.addLogicLabel("Old");
      { AbstractToken token = arguments.queryToken();
      std::string s = token.str();
        if (token.getType() == AbstractToken::TKeyword) {
          KeywordToken::Type type = ((const KeywordToken&) token).getType();
          switch(type) {
            case KeywordToken::TBehavior:
              { result = check_bhv_position (arguments);
                if (result == RRFinished) return result;
                DefineGotoCase(BehaviorName)
              }
            case KeywordToken::TRequires:
              { result = check_requires_position(arguments);
                if(result == RRFinished) return result;
                DefineGotoCase(Requires)
              }
            case KeywordToken::TTerminates:
              { result = check_terminates_position(arguments);
                if(result == RRFinished) return result;
                DefineGotoCase(Terminates)
              }
            case KeywordToken::TDecreases:
              { result = check_variant_position(arguments);
                if(result == RRFinished) return result;
                DefineGotoCase(Decreases)
              }
            case KeywordToken::TAssumes:
              { result = check_assumes_position(arguments);
                if(result == RRFinished) return result;
                DefineGotoCase(Assumes)
              }
            case KeywordToken::TEnsures:
              { result = check_post_cond_position(arguments);
                if(result == RRFinished) return result;
                _postCondKind = NORMAL;
                arguments.set_result_context(!_isStatementContract);
                DefineGotoCase(PostCond)
              }
            case KeywordToken::TAssigns:
              { result = check_post_cond_position(arguments);
                if (result == RRFinished) return result;
                arguments.set_result_context(!_isStatementContract);
                DefineGotoCase(Assigns)
              }
            case KeywordToken::TAllocates:
            case KeywordToken::TFrees:
              {
                result = check_post_cond_position(arguments);
                if (result == RRFinished) return result;
                arguments.set_result_context(
                  !_isStatementContract && (type == KeywordToken::TAllocates));
                _allocClauseKind =
                  type==KeywordToken::TAllocates?ALLOCATES:FREES;
                DefineGotoCase(AllocatesFrees);
              }
            case KeywordToken::TExits:
              { result = check_post_cond_position(arguments);
                if(result == RRFinished) return result;
                _postCondKind = EXITS;
                DefineGotoCase(PostCond)
              }
            case KeywordToken::TDisjoint:
              DefineGotoCase(Disjoint)
            case KeywordToken::TComplete:
              DefineGotoCase(Complete)
            default:
              arguments.resetAnnotContext();
              DefineAddErrorAndParse(std::string("unexpected keyword ")
                  .append(token.str()).append(" in function spec"))
          }
        }
        else {
          arguments.resetAnnotContext();
          DefineAddErrorAndParse("expecting function spec")
        }
      }
    DefineParseCase(BehaviorName)
      { AbstractToken token = arguments.queryToken();
        if (token.getType() == AbstractToken::TKeyword) {
          // Allow keywords as behavior names, converting them to strings
          _behaviorName = arguments.getContentToken().text();
          DefineGotoCase(Behavior)
        }
        if (token.getType() == AbstractToken::TIdentifier) {
          _behaviorName = ((const IdentifierToken&)arguments.getContentToken())
              .content();
          DefineGotoCase(Behavior)
        };
        arguments.lexer().assumeContentToken();
        arguments.resetAnnotContext();
        DefineAddError(std::string("unexpected token '")
            .append(arguments.getContentToken().str())
            .append("' expecting name of behavior"));
        DefineReduce;
      }
    DefineParseCase(Behavior)
      { AbstractToken token = arguments.queryToken();
        token = arguments.queryToken();
        if (token.getType() != AbstractToken::TOperatorPunctuator
              || ((const OperatorPunctuatorToken&) token).getType ()
            != OperatorPunctuatorToken::TColon) {
          arguments.lexer().assumeContentToken();
          arguments.resetAnnotContext();
          DefineAddError(std::string("':' expected after behavior name, got '")
              .append(arguments.getContentToken().str())
              .append("'"));
          DefineReduce;
        }
        add_behavior(_behaviorName);
        _behaviorName = "";
        _state = BHV;
        DefineGotoCase(Begin);
      }
    DefineParseCase(Requires) {
       logic_type thisRecordType = arguments.queryThisType();
       if (thisRecordType)
        arguments.addLogicFormal("this", thisRecordType);
      TermOrPredicate* pred = new TermOrPredicate;
      state.absorbRuleResult(&pred->setPredicate());
      DefineShiftAndParse(RequiresEnd,*pred,&TermOrPredicate::readToken);
    }
    DefineParseCase(RequiresEnd)
      { Parser::State::RuleAccess::TCastFromRule<TermOrPredicate>
          node(state.getRuleResult());
        predicate_named pred = node->extractPredicate(arguments);
        state.freeRuleResult();
        if (!pred) {
          arguments.resetAnnotContext();
          DefineAddError("expecting a predicate");
          DefineGotoCaseAndParse(BeforeSemiColon)
        };
        result = parseSemiColumn(arguments, "requires clause");
        if (result == RRFinished)
          return result;
        if (result == RRContinueParsing) {
          result = RRNeedChars;
          DefineGotoCaseAndParse(BeforeSemiColon)
        };
        if (!_spec->behavior) {
          // Adding new default behavior
          add_behavior(default_behavior_name);
        }
        _currentRequires.insertContainer(pred);
        _state = REQUIRES;
        DefineGotoCase(Begin)
      }
    DefineParseCase(Terminates) {
       logic_type thisRecordType = arguments.queryThisType();
       if (thisRecordType)
        arguments.addLogicFormal("this", thisRecordType);
      TermOrPredicate* pred = new TermOrPredicate;
      state.absorbRuleResult(&pred->setPredicate());
      DefineShiftAndParse(TerminatesEnd,*pred,&TermOrPredicate::readToken);
    }
    DefineParseCase(TerminatesEnd)
      { Parser::State::RuleAccess::TCastFromRule<TermOrPredicate>
          node(state.getRuleResult());
        predicate_named pred = node->extractPredicate(arguments);
        state.freeRuleResult();
        if (!pred) {
          arguments.resetAnnotContext();
          DefineAddError("expecting a predicate");
          DefineGotoCaseAndParse(BeforeSemiColon)
        };
        result = parseSemiColumn(arguments, "terminates clause");
        if (result == RRFinished)
          return result;
        if (_spec->terminates->is_some) {
          free_predicate_named(pred);
          pred = NULL;
          arguments.resetAnnotContext();
          DefineAddError("a contract can only have one `terminates' clause");
          DefineGotoCaseAndParse(BeforeSemiColon)
        };
        free(_spec->terminates);
        _spec->terminates = opt_some_container(pred);
        if (result == RRContinueParsing) {
          result = RRNeedChars;
          DefineGotoCaseAndParse(BeforeSemiColon)
        };
        _state = TERMINATES;
        DefineGotoCase(Begin)
      }
    DefineParseCase(Decreases) {
       logic_type thisRecordType = arguments.queryThisType();
       if (thisRecordType)
        arguments.addLogicFormal("this", thisRecordType);
      TermOrPredicate* decreaseTerm = new TermOrPredicate;
      state.absorbRuleResult(&decreaseTerm->setTerm());
      DefineShiftAndParse(DecreasesFor, *decreaseTerm,
          &TermOrPredicate::readToken);
    }
    DefineParseCase(DecreasesFor)
      { Parser::State::RuleAccess::TCastFromRule<TermOrPredicate>
          node(state.getRuleResult());
        term decreaseTerm = node->extractTerm(arguments);
        state.freeRuleResult();
        if (!decreaseTerm) {
          arguments.resetAnnotContext();
          DefineAddError("expecting a term");
          DefineGotoCaseAndParse(BeforeSemiColon)
        };
        if (_spec->variant->is_some) {
          free_term(decreaseTerm);
          decreaseTerm = NULL;
          arguments.resetAnnotContext();
          DefineAddError("a contract can only have one `decreases' clause");
          DefineGotoCaseAndParse(BeforeSemiColon)
        };
        free(_spec->variant);
        _spec->variant = opt_some_container(variant_cons(decreaseTerm,
            opt_none()));
        AbstractToken token = arguments.queryToken();
        if (token.getType() == AbstractToken::TOperatorPunctuator) {
          if (((const OperatorPunctuatorToken&) token).getType()
              == OperatorPunctuatorToken::TSemiColon) {
            _state = TERMINATES;
            DefineGotoCase(Begin)
          };
          arguments.resetAnnotContext();
          DefineAddError("Expecting ';' after decreases clause");
        }
        else if (token.getType() == AbstractToken::TKeyword) {
          if (((const KeywordToken&) token).getType() == KeywordToken::TFor) {
            _state = TERMINATES;
            DefineGotoCase(DecreasesForIdent)
          };
          arguments.resetAnnotContext();
          DefineAddError("Expecting \"for\" after decreases clause");
        };
        DefineGotoCaseAndParse(BeforeSemiColon)
      }
    DefineParseCase(DecreasesForIdent)
      if (arguments.queryToken().getType() == AbstractToken::TIdentifier) {
        variant decreases = (variant) _spec->variant->content.container;
        assert(!decreases->vname->is_some);
        free(decreases->vname);
        decreases->vname = opt_some_container(strdup(((const IdentifierToken&)
            arguments.getContentToken()).content().c_str()));
        DefineGotoCase(BeforeSemiColon)
      }
      arguments.resetAnnotContext();
      DefineAddError("Expecting an identifier after decreases-for clause");
      DefineGotoCaseAndParse(BeforeSemiColon)
    DefineParseCase(Assumes)
      { logic_type thisRecordType = arguments.queryThisType();
        if (thisRecordType)
          arguments.addLogicFormal("this", thisRecordType);
        TermOrPredicate* pred = new TermOrPredicate;
        state.absorbRuleResult(&pred->setPredicate());
        DefineShiftAndParse(AssumesEnd,*pred,&TermOrPredicate::readToken)
      }
    DefineParseCase(AssumesEnd)
      { Parser::State::RuleAccess::TCastFromRule<TermOrPredicate>
          node(state.getRuleResult());
        predicate_named pred = node->extractPredicate(arguments);
        state.freeRuleResult();
        if (!pred) {
          DefineAddError("expecting a predicate");
          DefineReduceAndParse
        };
        result = parseSemiColumn(arguments, "assumes clause");
        if (result == RRFinished) return result;
        if (!_spec->behavior) {
          // Adding new default behavior
          add_behavior(default_behavior_name);
        }
        _currentAssumes.insertContainer(pred);
        _state = ASSUMES;
        DefineGotoCase(Begin)
      }
    DefineParseCase(PostCond)
      { logic_type thisRecordType = arguments.queryThisType();
        if (thisRecordType)
          arguments.addLogicFormal("this", thisRecordType);
        TermOrPredicate* pred = new TermOrPredicate;
        state.absorbRuleResult(&pred->setPredicate());
        arguments.addLogicLabel("Post");
        DefineShiftAndParse(PostCondEnd,*pred,&TermOrPredicate::readToken)
      }
    DefineParseCase(PostCondEnd)
      { Parser::State::RuleAccess::TCastFromRule<TermOrPredicate>
          node(state.getRuleResult());
        predicate_named pred = node->extractPredicate(arguments);
        state.freeRuleResult();
        if (!pred) {
          arguments.resetAnnotContext();
          DefineAddError("the body of the post-condition is not a predicate");
          _additionalMsg = "postcondition";
          DefineGotoCaseAndParse(BeforeSemiColon);
        };
        arguments.set_result_context(false);
        arguments.removeLogicLabel("Post");
        result = parseSemiColumn(arguments, "post-condition");
        if (result == RRFinished) return result;
        if (!_spec->behavior) {
          // Adding new default behavior
          add_behavior(default_behavior_name);
        }
        post_condition post = post_condition_cons(_postCondKind,pred);
        _currentPostCond.insertContainer(post);
        _state = POST_COND;
        DefineGotoCase(Begin)
      }
    DefineParseCase(Assigns)
      { 
        logic_type thisRecordType = arguments.queryThisType();
        if (thisRecordType)
          arguments.addLogicFormal("this", thisRecordType);
        AssignsClause* assigns
          = new AssignsClause(arguments.newTokenLocation());
        state.absorbRuleResult(assigns);
        arguments.addLogicLabel("Post");
        DefineShiftAndParse(AssignsEnd,*assigns,&AssignsClause::readToken);
      }
    DefineParseCase(AssignsEnd)
      { Parser::State::RuleAccess::TCastFromRule<AssignsClause>
          node(state.getRuleResult());
        ForwardList assigns = node->getResult();
        state.freeRuleResult();
        result = parseSemiColumn(arguments, "assigns");
        if (result == RRFinished) return result;
        if (!_spec->behavior) add_behavior(default_behavior_name);
        _currentAssigns.append(assigns);
        list current = _spec->behavior;
        while (current->next) current = current->next;
        behavior bhv = (behavior)current->element.container;
        if (bhv->assignements) free(bhv->assignements);
        bhv->assignements = assigns_Writes(_currentAssigns.getFront());
        DefineGotoCase(Begin)
      }
    DefineParseCase(AllocatesFrees)
    {
        logic_type thisRecordType = arguments.queryThisType();
        if (thisRecordType)
          arguments.addLogicFormal("this", thisRecordType);
        AllocFreeClause* allocFree
          = new AllocFreeClause(arguments.newTokenLocation());
        state.absorbRuleResult(allocFree);
        arguments.addLogicLabel("Post");
        DefineShiftAndParse(AllocatesFreesEnd,*allocFree,
                            &AllocFreeClause::readToken);
    }
    DefineParseCase(AllocatesFreesEnd)
    {
      Parser::State::RuleAccess::TCastFromRule<AllocFreeClause>
          node(state.getRuleResult());
      ForwardList allocFrees = node->getResult();
      state.freeRuleResult();
      result =
        parseSemiColumn(
          arguments,
          _allocClauseKind == ALLOCATES ? "allocates" : "frees");
      if (result == RRFinished) return result;
      if (!_spec->behavior) add_behavior(default_behavior_name);
      if (_allocClauseKind == ALLOCATES) {
        _currentAllocates.append(allocFrees);
      } else {
        _currentFrees.append(allocFrees);
      }
      list current = _spec->behavior;
      while (current->next) current = current->next;
      behavior bhv = (behavior)current->element.container;
      if (bhv->alloc) free(bhv->alloc);
      bhv->alloc =
        allocation_FreeAlloc(
          _currentFrees.getFront(), _currentAllocates.getFront());
      DefineGotoCase(Begin)
    }
    DefineParseCase(Complete)
    DefineParseCase(Disjoint)
      { AbstractToken token = arguments.queryToken();
        if (token.getType() == AbstractToken::TKeyword) {
          if (((const KeywordToken&) token).getType() 
              == KeywordToken::TBehaviors) {
            set_of_behaviors behaviorsSet = set_of_behaviors_cons(NULL);
            if (state.point() == DComplete)
              _complete.insertContainer(behaviorsSet);
            else
              _disjoint.insertContainer(behaviorsSet);
            _currentSetOfBehaviors
                = ForwardReferenceList(behaviorsSet->behaviors);
            DefineGotoCaseWithIncrement(DCompleteBehavior-DComplete,
              LCompleteBehavior);
          };
        };
        arguments.resetAnnotContext();
        if (state.point() == DComplete)
          DefineAddError("Expecting \"behaviors\" after complete construct")
        else
          DefineAddError("Expecting \"behaviors\" after disjoint construct")
        DefineGotoCaseAndParse(BeforeSemiColon)
      }
    DefineParseCase(CompleteBehavior)
    DefineParseCase(DisjointBehavior)
      { AbstractToken token = arguments.queryToken();
        if (token.getType() == AbstractToken::TIdentifier) {
          _currentSetOfBehaviors.insertContainer(
            strdup(((const IdentifierToken&) arguments.getContentToken())
                   .content().c_str()));
          DefineGotoCaseWithIncrement(DAfterComplete-DCompleteBehavior,
                                      LAfterComplete);
        };
        if (token.getType() == AbstractToken::TKeyword) {
          std::string name = arguments.getContentToken().text();
          _currentSetOfBehaviors.insertContainer(strdup(name.c_str()));
          DefineGotoCaseWithIncrement(DAfterComplete-DCompleteBehavior,
                                      LAfterComplete);
        };
        // Allow for empty lists: if no identifier has been added, we
        // accept a ';' and start parsing a new clause
        if (!_currentSetOfBehaviors.getFront() &&
            token.getType() == AbstractToken::TOperatorPunctuator &&
            ((const OperatorPunctuatorToken&)token).getType() ==
              OperatorPunctuatorToken::TSemiColon)
          DefineGotoCase(Begin);
        arguments.resetAnnotContext();
        if (state.point() == DCompleteBehavior)
          DefineAddError("Expecting an identifier after \"complete behaviors\" "
          "construct")
        else
          DefineAddError("Expecting an identifier after \"disjoint behaviors\" "
          "construct")
        DefineGotoCaseAndParse(BeforeSemiColon)
      }
    DefineParseCase(AfterComplete)
    DefineParseCase(AfterDisjoint)
      { AbstractToken token = arguments.queryToken();
        if (token.getType() == AbstractToken::TOperatorPunctuator) {
          OperatorPunctuatorToken::Type
            type = ((const OperatorPunctuatorToken&) token).getType();
          if (type == OperatorPunctuatorToken::TSemiColon)
            DefineGotoCase(Begin)
          if (type == OperatorPunctuatorToken::TComma)
            DefineGotoCaseWithIncrement(DCompleteBehavior-DAfterComplete,
              LCompleteBehavior);
        };
      }
      arguments.resetAnnotContext();
      if (state.point() == DAfterComplete)
        DefineAddError("Expecting ',' or ';' after complete construct")
      else
        DefineAddError("Expecting ',' or ';' after disjoint construct")
      DefineGotoCase(BeforeSemiColon)
    DefineParseCase(BeforeSemiColon)
      { AbstractToken token = arguments.queryToken();
        if (token.getType() == AbstractToken::TOperatorPunctuator) {
          OperatorPunctuatorToken::Type
            type = ((const OperatorPunctuatorToken&) token).getType();
          if (type == OperatorPunctuatorToken::TSemiColon)
            DefineGotoCase(Begin)
        };
        arguments.resetAnnotContext();
        DefineAddError(std::string("Expecting ';' after ")
            .append(_additionalMsg))
        DefineGotoCase(Begin)
      }
  } // End switch
  return result;
} // End readToken

#if defined(__clang__) || defined(__GNUC__)
#pragma GCC diagnostic pop
#endif

} // end of namespace Acsl

