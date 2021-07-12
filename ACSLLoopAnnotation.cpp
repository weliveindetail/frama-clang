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
//   Implementation of the ACSL loop annotations.
//

#include "ACSLComponent.h"

namespace Acsl {

using namespace DLexer;

#if defined(__clang__) || defined(__GNUC__)
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wunused-label"
#endif

LoopAnnotation::~LoopAnnotation() {
  clear();
  if (!_hasUsedBehaviors) {
    while (_behaviors) {
      free((char*) _behaviors->element.container);
      list temp = _behaviors;
      _behaviors = _behaviors->next;
      free(temp);
    };
  };
  if (_loc) { free_location(_loc); _loc = NULL; }
  if (_annotationList.getFront()) {
    /* statement */ list annotations = _annotationList.getFront();
    _annotationList = ForwardList();
    do {
      free_statement((statement) annotations->element.container);
      list temp = annotations;
      annotations = annotations->next;
      free(temp);
    } while (annotations);
  };
}

Parser::ReadResult
LoopAnnotation::readToken(Parser::State& state, Parser::Arguments& arguments)
{ enum Delimiters
  { DInitial, DBegin, DLoop, DInvariant, DAssigns, DAllocates, DFrees,
    DAfterAllocates, DAfterFrees, DVariant, DVariantFor, DForId, DAfterForId,
    DEnd, DBeforeSemiColon
  };

  ReadResult result = RRNeedChars;
  switch (state.point()) {
    DefineParseCase(Initial)
      arguments.addLogicLabel("Pre");
      arguments.addLogicLabel("Here");
      DefineGotoCaseAndParse(Begin)
    DefineParseCase(Begin)
      { AbstractToken token = arguments.queryToken();
        absorbLoc(arguments.newTokenLocation());
        if (token.getType() == AbstractToken::TKeyword) {
          KeywordToken::Type type = ((const KeywordToken&) token).getType();
          if (type == KeywordToken::TLoop)
            DefineGotoCase(Loop)
          if (type == KeywordToken::TFor) {
            if (_behaviors)
              DefineAddError("multiple 'for' behaviors in code annotation")
            DefineGotoCase(ForId)
          }
        };
      }
      DefineAddError("expecting 'loop' or 'for' in code annotation")
      DefineGotoCaseAndParse(BeforeSemiColon)
    DefineParseCase(Loop)
      { AbstractToken token = arguments.queryToken();
        if (token.getType() == AbstractToken::TKeyword) {
          KeywordToken::Type type = ((const KeywordToken&) token).getType();
#if defined(__clang__) || defined(__GNUC__)
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wswitch"
#endif
          switch (type) {
            case KeywordToken::TInvariant:
              { TermOrPredicate* pred = new TermOrPredicate;
                state.absorbRuleResult(&pred->setPredicate());
                DefineShift(Invariant, *pred, &TermOrPredicate::readToken)
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
            case KeywordToken::TVariant:
              { TermOrPredicate* variantBody = new TermOrPredicate;
                state.absorbRuleResult(&variantBody->setTerm());
                DefineShift(Variant, *variantBody, &TermOrPredicate::readToken)
              };
          };
#if defined(__clang__) || defined(__GNUC__)
#pragma GCC diagnostic pop
#endif
        };
      }
      DefineAddError("expecting 'loop' or 'for' in code annotation")
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
          _annotResult = code_annotation_Invariant(behaviors,NORMALLOOP, pred);
          _hasUsedBehaviors = true;
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
            code_annotation annotation = code_annotation_Assigns(NULL,
                assigns_Writes(assigns.getFront()));
            arguments.extendLocationWithToken(_loc);
            _annotationList.insertContainer(statement_Code_annot(
                copy_loc(_loc), annotation));
            clear();
            DefineGotoCase(Begin)
          }
        };
      }
      DefineAddError("Expecting ';' after assigns in loop annotation")
      DefineGotoCase(BeforeSemiColon)
    DefineParseCase(Allocates)
    DefineParseCase(Frees)
      { AbstractToken token = arguments.queryToken();
        if (token.getType() == AbstractToken::TKeyword) {
          if (((const KeywordToken&) token).getType() == KeywordToken::TNothing)
          { _annotResult = code_annotation_Allocation(NULL,
                allocation_FreeAlloc(NULL, NULL));
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
            if (!allocation) {
               state.freeRuleResult();
               clear();
               DefineGotoCase(Begin)
            };
            if (ltype)
               free_logic_type(ltype);
            if (!_annotResult)
              _annotResult = code_annotation_Allocation(NULL,
                  allocation_FreeAlloc(NULL, NULL));
            /* term */ list& toAppend = (state.point() == DAfterFrees)
                ? _annotResult->cons_code_annotation
                    .Allocation.alloc->cons_allocation.FreeAlloc.fst
                : _annotResult->cons_code_annotation
                    .Allocation.alloc->cons_allocation.FreeAlloc.snd;
            while (toAppend)
              toAppend = toAppend->next;
            toAppend = cons_container(allocation, NULL);
            if (type == OperatorPunctuatorToken::TComma) {
              rule->clear();
              DefineShiftWithIncrement(0, LAfterFreeOrAllocates, *rule,
                  &TermOrPredicate::readToken);
            };
            state.freeRuleResult();
            arguments.extendLocationWithToken(_loc);
            _annotationList.insertContainer(statement_Code_annot(
                copy_loc(_loc), _annotResult));
            _annotResult = NULL;
            clear();
            DefineGotoCase(Begin)
          }
        };
      }
      DefineAddError("Expecting ';' or ',' after allocates/frees "
          "in loop annotation")
      DefineGotoCase(BeforeSemiColon)
    DefineParseCase(Variant)
      { Parser::State::RuleAccess::TCastFromRule<TermOrPredicate>
          rule(state.getRuleResult());
        term variantBody = rule->extractTerm(arguments);
        state.freeRuleResult();
        if (variantBody)
          _annotResult = code_annotation_Variant(variant_cons(variantBody,
                opt_none()));
        else
          DefineAddError("expecting a term for a variant declaration");
      }
      { AbstractToken token = arguments.queryToken();
        if (token.getType() == AbstractToken::TOperatorPunctuator) {
          if (((const OperatorPunctuatorToken&) token).getType()
              == OperatorPunctuatorToken::TSemiColon) {
            arguments.extendLocationWithToken(_loc);
            _annotationList.insertContainer(statement_Code_annot(
                copy_loc(_loc), _annotResult));
            _annotResult = NULL;
            clear();
            DefineGotoCase(Begin)
          };
        }
        else if (token.getType() == AbstractToken::TKeyword) {
          if (((const KeywordToken&) token).getType() == KeywordToken::TFor)
            DefineGotoCase(VariantFor)
        };
      }
      DefineAddError("Expecting ';' after variant in loop annotation")
      DefineGotoCase(BeforeSemiColon)
    DefineParseCase(VariantFor)
      if (arguments.queryToken().getType() == AbstractToken::TIdentifier) {
        std::string identifier = ((const IdentifierToken&)
            arguments.getContentToken()).content();
        free(_annotResult->cons_code_annotation.Variant.body->vname);
        _annotResult->cons_code_annotation.Variant.body->vname
          = opt_some_container(strdup(identifier.c_str()));
        DefineGotoCase(End)
      }
      DefineAddError("Expecting identifier after variant ... for "
          "in loop annotation")
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
              arguments.extendLocationWithToken(_loc);
              _annotationList.insertContainer(statement_Code_annot(
                  copy_loc(_loc), _annotResult));
              _annotResult = NULL;
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

