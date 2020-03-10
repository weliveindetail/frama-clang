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
//   Implementation of the ACSL statement annotations.
//

#include "ACSLComponent.h"

namespace Acsl {

using namespace DLexer;

#if defined(__clang__) || defined(__GNUC__)
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wunused-label"
#endif

Parser::ReadResult
StatementAnnotation::readToken(Parser::State& state,
    Parser::Arguments& arguments) {
  enum Delimiters
  { DBegin, DAssumes, DRequires, DInvariant, DEnsures, DAssigns,
    DAllocates, DFrees, DAfterAllocates, DAfterFrees, DExits, DBreaks,
    DContinues, DReturns, DBehavior, DForId, DAfterForId, DEnd, DBeforeSemiColon
  };

  ReadResult result = RRNeedChars;
  switch (state.point()) {
    DefineParseCase(Begin)
      { AbstractToken token = arguments.queryToken();
        if (!_functionContractBehaviors) {
          absorbLoc(arguments.newTokenLocation());
        }
        else
          assert(_subloc);
        if (token.getType() == AbstractToken::TKeyword) {
          KeywordToken::Type type = ((const KeywordToken&) token).getType();
#if defined(__clang__) || defined(__GNUC__)
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wswitch"
#endif
          switch (type) {
            case KeywordToken::TAssumes:
              if (!_functionContractBehaviors) {
                DefineAddError("expecting a behavior id "
                    "before an assume-clause-statement");
                DefineGotoCase(BeforeSemiColon)
              };
              { TermOrPredicate* pred = new TermOrPredicate;
                state.absorbRuleResult(&pred->setPredicate());
                DefineShift(Assumes, *pred, &TermOrPredicate::readToken)
              };
            case KeywordToken::TRequires:
              { TermOrPredicate* pred = new TermOrPredicate;
                state.absorbRuleResult(&pred->setPredicate());
                DefineShift(Requires, *pred, &TermOrPredicate::readToken)
              };
            case KeywordToken::TInvariant:
              { TermOrPredicate* pred = new TermOrPredicate;
                state.absorbRuleResult(&pred->setPredicate());
                DefineShift(Invariant, *pred, &TermOrPredicate::readToken)
              };
            case KeywordToken::TEnsures:
              { TermOrPredicate* pred = new TermOrPredicate;
                state.absorbRuleResult(&pred->setPredicate());
                DefineShift(Ensures, *pred, &TermOrPredicate::readToken)
              };
            case KeywordToken::TAssigns:
              { logic_type thisRecordType = arguments.queryThisType();
                if (thisRecordType)
                  arguments.addLogicFormal("this", thisRecordType);
                AssignsClause* assigns
                  = new AssignsClause(arguments.newTokenLocation());
                state.absorbRuleResult(assigns);
                arguments.addLogicLabel("Post");
                DefineShift(Assigns, *assigns, &AssignsClause::readToken);
              };
            case KeywordToken::TAllocates:
              DefineGotoCase(Allocates)
            case KeywordToken::TFrees:
              DefineGotoCase(Frees)
            case KeywordToken::TExits:
              { TermOrPredicate* pred = new TermOrPredicate;
                state.absorbRuleResult(&pred->setPredicate());
                DefineShift(Exits, *pred, &TermOrPredicate::readToken)
              };
            case KeywordToken::TBreaks:
              { TermOrPredicate* pred = new TermOrPredicate;
                state.absorbRuleResult(&pred->setPredicate());
                DefineShift(Breaks, *pred, &TermOrPredicate::readToken)
              };
            case KeywordToken::TContinues:
              { TermOrPredicate* pred = new TermOrPredicate;
                state.absorbRuleResult(&pred->setPredicate());
                DefineShift(Continues, *pred, &TermOrPredicate::readToken)
              };
            case KeywordToken::TReturns:
              { TermOrPredicate* pred = new TermOrPredicate;
                state.absorbRuleResult(&pred->setPredicate());
                DefineShift(Returns, *pred, &TermOrPredicate::readToken)
              };
            case KeywordToken::TBehavior:
              if (_subloc) free_location(_subloc);
              _subloc = arguments.newTokenLocation();
              DefineGotoCase(Behavior)
            case KeywordToken::TFor:
              if (_behaviors)
                DefineAddError("multiple 'for' behaviors in code annotation")
              DefineGotoCase(ForId)
          };
#if defined(__clang__) || defined(__GNUC__)
#pragma GCC diagnostic pop
#endif
        };
      }
      DefineAddError("unexpected token in statement-contract")
      DefineGotoCaseAndParse(BeforeSemiColon)
    DefineParseCase(Assumes)
      { Parser::State::RuleAccess::TCastFromRule<TermOrPredicate>
          rule(state.getRuleResult());
        assert(_functionContractBehaviors);
        predicate_named pred = rule->extractPredicate(arguments);
        state.freeRuleResult();
        if (pred) {
          behavior current = (behavior) _functionContractBehaviorsAdder
              .getBack()->element.container;
          /* predicate_named */ list& assumes = current->assumes;
          while (assumes)
            assumes = assumes->next;
          assumes = cons_container(pred, NULL);
        }
        else
          DefineAddError("expecting a predicate");
      }
      DefineGotoCaseAndParse(End)
    DefineParseCase(Requires)
      { Parser::State::RuleAccess::TCastFromRule<TermOrPredicate>
          rule(state.getRuleResult());
        predicate_named pred = rule->extractPredicate(arguments);
        state.freeRuleResult();
        if (pred) {
          if (_functionContractBehaviors) {
            behavior current = (behavior) _functionContractBehaviorsAdder
                .getBack()->element.container;
            /* predicate_named */ list& requires = current->requires;
            while (requires)
              requires = requires->next;
            requires = cons_container(pred, NULL);
          }
          else {
            assert(false); // unimplemented
            // /* string */ list behaviors = _behaviors;
            // if (_hasUsedBehaviors && _behaviors) {
            //   behaviors = cons_container(strdup((char*)
            //       _behaviors->element.container(), NULL);
            //   /* string */ list& endBehaviors = behaviors->next;
            //   /* string */ list current = _behaviors->next;
            //   while (current) {
            //     endBehaviors = cons_container(strdup((char*)
            //       current->element.container(), NULL);
            //     endBehaviors = endBehaviors->next;
            //     current = current->next;
            //   };
            // };
            // _annotResult = code_annotation_Requires(behaviors, pred);
            // _hasUsedBehaviors = true;
          };
        }
        else
          DefineAddError("expecting a predicate");
      }
      DefineGotoCaseAndParse(End)
    DefineParseCase(Invariant)
      { Parser::State::RuleAccess::TCastFromRule<TermOrPredicate>
          rule(state.getRuleResult());
        predicate_named pred = rule->extractPredicate(arguments);
        state.freeRuleResult();
        if (pred) {
          /* string */ list behaviors = _behaviors;
          if (_hasUsedBehaviors && _behaviors) {
            behaviors = cons_container(strdup((char*)
                _behaviors->element.container), NULL);
            /* string */ list& endBehaviors = behaviors->next;
            /* string */ list current = _behaviors->next;
            while (current) {
              endBehaviors = cons_container(strdup((char*)
                current->element.container), NULL);
              endBehaviors = endBehaviors->next;
              current = current->next;
            };
          };
          _annotResult = code_annotation_Invariant(behaviors,
            INVARIANTASASSERTION, pred);
          _hasUsedBehaviors = true;
        }
        else
          DefineAddError("expecting a predicate");
      }
      DefineGotoCaseAndParse(End)
    DefineParseCase(Ensures)
    DefineParseCase(Exits)
    DefineParseCase(Breaks)
    DefineParseCase(Continues)
    DefineParseCase(Returns)
      { Parser::State::RuleAccess::TCastFromRule<TermOrPredicate>
          rule(state.getRuleResult());
        predicate_named pred = rule->extractPredicate(arguments);
        state.freeRuleResult();
        if (pred) {
          if (_functionContractBehaviors) {
            behavior current = (behavior) _functionContractBehaviorsAdder
                .getBack()->element.container;
            /* predicate_named */ list& post_cond = current->post_cond;
            while (post_cond)
              post_cond = post_cond->next;
            termination_kind tkind = NORMAL;
            switch (state.point()) {
              case DEnsures: tkind = NORMAL; break;
              case DExits: tkind = EXITS; break;
              case DBreaks: tkind = BREAKS; break;
              case DContinues: tkind = CONTINUES; break;
              case DReturns: tkind = RETURNS; break;
            };
            post_cond = cons_container(post_condition_cons(tkind, pred), NULL);
          }
          else {
            assert(false); // unimplemented
            // /* string */ list behaviors = _behaviors;
            // if (_hasUsedBehaviors && _behaviors) {
            //   behaviors = cons_container(strdup((char*)
            //       _behaviors->element.container(), NULL);
            //   /* string */ list& endBehaviors = behaviors->next;
            //   /* string */ list current = _behaviors->next;
            //   while (current) {
            //     endBehaviors = cons_container(strdup((char*)
            //       current->element.container(), NULL);
            //     endBehaviors = endBehaviors->next;
            //     current = current->next;
            //   };
            // };
            // _annotResult = code_annotation_Requires(behaviors, pred);
            // _hasUsedBehaviors = true;
          };
        }
        else
          DefineAddError("expecting a predicate");
      }
      DefineGotoCaseAndParse(End)
    DefineParseCase(Assigns)
      { AbstractToken token = arguments.queryToken();
        if (token.getType() == AbstractToken::TOperatorPunctuator) {
          OperatorPunctuatorToken::Type type = 
            ((const OperatorPunctuatorToken&) token).getType();
          if (type == OperatorPunctuatorToken::TSemiColon) {
            Parser::State::RuleAccess::TCastFromRule<AssignsClause>
              node(state.getRuleResult());
            ForwardList assigns = node->getResult();
            state.freeRuleResult();
            if (!_functionContractBehaviors) {
              code_annotation annotation = code_annotation_Assigns(NULL,
                  assigns_Writes(assigns.getFront()));
              arguments.extendLocationWithToken(_loc);
              _codeContainer.insertContainer(statement_Code_annot(
                  copy_loc(_loc), annotation));
              clear();
            }
            else {
              behavior current = (behavior) _functionContractBehaviorsAdder
                  .getBack()->element.container;
              if (current->assignements->tag_assigns == WRITESANY) {
                free(current->assignements);
                current->assignements = assigns_Writes(assigns.getFront());
              }
              else {
                assert(current->assignements->tag_assigns == WRITES);
                /* from */ list& froms = current->assignements->cons_assigns
                    .Writes.frm;
                while (froms)
                  froms = froms->next;
                froms = assigns.getFront();
              }
            };
            DefineGotoCase(Begin)
          }
        };
      }
      DefineAddError("Expecting ';' after assigns in statement annotation")
      DefineGotoCase(BeforeSemiColon)
    DefineParseCase(Allocates)
    DefineParseCase(Frees)
      { AbstractToken token = arguments.queryToken();
        if (token.getType() == AbstractToken::TKeyword) {
          if (((const KeywordToken&) token).getType() == KeywordToken::TNothing)
          { if (!_functionContractBehaviors)
              _annotResult = code_annotation_Allocation(NULL,
                  allocation_FreeAlloc(NULL, NULL));
            else {
              behavior current = (behavior) _functionContractBehaviorsAdder
                  .getBack()->element.container;
              if (current->alloc->tag_allocation == FREEALLOCANY) {
                free(current->alloc);
                current->alloc = allocation_FreeAlloc(NULL, NULL);
              }
              else {
                assert(current->alloc->tag_allocation == FREEALLOC);
              }
            };
            DefineGotoCase(End)
          };
        };
        TermOrPredicate* freeOrAllocates = new TermOrPredicate;
        state.absorbRuleResult(&freeOrAllocates->setSet());
        DefineShiftWithIncrement(DAfterAllocates - DAllocates,
            LAfterFreeOrAllocates, (TermOrPredicate&) *freeOrAllocates,
            &TermOrPredicate::readToken);
      };
    DefineParseCase(AfterAllocates)
    DefineParseCase(AfterFrees)
LAfterFreeOrAllocates:
      { AbstractToken token = arguments.queryToken();
        if (token.getType() == AbstractToken::TOperatorPunctuator) {
          OperatorPunctuatorToken::Type type = 
            ((const OperatorPunctuatorToken&) token).getType();
          if (type == OperatorPunctuatorToken::TComma
              || type == OperatorPunctuatorToken::TSemiColon) {
            Parser::State::RuleAccess::TCastFromRule<TermOrPredicate>
              rule(state.getRuleResult());
            logic_type ltype = NULL;
            term allocation = rule->extractSet(arguments, ltype);
            if (ltype)
               free_logic_type(ltype);
            /* term */ list* toAppend = NULL;
            if (!_functionContractBehaviors) {
              if (!_annotResult)
                _annotResult = code_annotation_Allocation(NULL,
                    allocation_FreeAlloc(NULL, NULL));
              toAppend = (state.point() == DAfterFrees)
                  ? &_annotResult->cons_code_annotation
                      .Allocation.alloc->cons_allocation.FreeAlloc.fst
                  : &_annotResult->cons_code_annotation
                      .Allocation.alloc->cons_allocation.FreeAlloc.snd;
            }
            else {
              behavior current = (behavior) _functionContractBehaviorsAdder
                  .getBack()->element.container;
              if (current->alloc->tag_allocation == FREEALLOCANY) {
                free(current->alloc);
                current->alloc = allocation_FreeAlloc(NULL, NULL);
              }
              else
                assert(current->alloc->tag_allocation == FREEALLOC);
              toAppend = (state.point() == DAfterFrees)
                  ? &current->alloc->cons_allocation.FreeAlloc.fst
                  : &current->alloc->cons_allocation.FreeAlloc.snd;
            }
            while (*toAppend)
              *toAppend = (*toAppend)->next;
            *toAppend = cons_container(allocation, NULL);

            if (type == OperatorPunctuatorToken::TComma) {
              rule->clear();
              DefineShiftWithIncrement(0, LAfterFreeOrAllocates, *rule,
                  &TermOrPredicate::readToken);
            };
            state.freeRuleResult();
            code_annotation annotation = _annotResult;
            _annotResult = NULL;
            arguments.extendLocationWithToken(_loc);
            _codeContainer.insertContainer(statement_Code_annot(
                copy_loc(_loc), annotation));
            clear();
            DefineGotoCase(Begin)
          }
        };
      }
      DefineAddError("Expecting ';' or ',' after allocates/frees "
          "in statement annotation")
      DefineGotoCase(BeforeSemiColon)
    DefineParseCase(Behavior)
      if (arguments.queryToken().getType() == AbstractToken::TIdentifier) {
        const IdentifierToken& token
            = (const IdentifierToken&) arguments.getContentToken();
        _functionContractBehaviorsAdder.insertContainer(
            behavior_cons(strdup(token.content().c_str()), /* requires */ NULL,
              /* assumes */ NULL, /* post_cond */ NULL, assigns_WritesAny(),
              allocation_FreeAllocAny(), /* extended */ NULL));
        DefineGotoCase(Begin)
      }
      DefineAddError("expecting identifier after 'for' in code annotation")
      DefineGotoCaseAndParse(BeforeSemiColon)
    DefineParseCase(ForId)
      if (arguments.queryToken().getType() == AbstractToken::TIdentifier) {
        const IdentifierToken& token
            = (const IdentifierToken&) arguments.getContentToken();
        _behaviorAdder.insertContainer(strdup(token.content().c_str()));
        DefineGotoCase(AfterForId)
      }
      DefineAddError("expecting identifier after 'for' in code annotation")
      DefineGotoCaseAndParse(BeforeSemiColon)
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
      DefineAddError("expecting ',' or ':' in a code annotation")
      DefineGotoCaseAndParse(End)
    DefineParseCase(End)
      { AbstractToken token = arguments.queryToken();
        if (token.getType() == AbstractToken::TOperatorPunctuator) {
          OperatorPunctuatorToken::Type
            type = ((const OperatorPunctuatorToken&) token).getType();
          if (type == OperatorPunctuatorToken::TSemiColon) {
            if (_annotResult) {
              code_annotation annotation = _annotResult;
              _annotResult = NULL;
              arguments.extendLocationWithToken(_loc);
              _codeContainer.insertContainer(statement_Code_annot(
                  copy_loc(_loc), annotation));
            };
            clear();
            DefineGotoCase(Begin)
          };
        };
      }
      DefineAddError("expecting ';' at the end of a code annotation")
      DefineGotoCase(BeforeSemiColon)
    DefineParseCase(BeforeSemiColon)
      { AbstractToken token = arguments.queryToken();
        if (token.getType() == AbstractToken::TOperatorPunctuator) {
          if (((const OperatorPunctuatorToken&) token).getType()
              == OperatorPunctuatorToken::TSemiColon) {
            clear();
            DefineGotoCase(Begin)
          }
        };
      };
      DefineGotoCase(BeforeSemiColon)
  }
  return result;
}

#if defined(__clang__) || defined(__GNUC__)
#pragma GCC diagnostic pop
#endif

} // end of namespace Acsl

