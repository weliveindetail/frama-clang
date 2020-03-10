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
//   Implementation of the ACSL global annotations.
//

#include "ACSLGlobalAnnotation.h"
#include "clang/AST/DeclTemplate.h"

namespace Acsl {

using namespace DLexer;

#if defined(__clang__) || defined(__GNUC__)
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wunused-label"
#endif

Parser::ReadResult
GlobalAnnotation::Parameters::readToken(
  Parser::State& state, Parser::Arguments& arguments) {
  enum delimiters { DBegin, DParam, DEndParam };
  ReadResult result = RRNeedChars;
  switch (state.point()) {
    DefineParseCase(Begin)
      { AbstractToken token = arguments.queryToken();
        if (token.getType() == AbstractToken::TOperatorPunctuator
             && ((const OperatorPunctuatorToken&)token).getType() ==
                 OperatorPunctuatorToken::TCloseParen) {
          // DefineReduce will clear the next token, that we in fact need
          // in the rest of the rule. 
          DefineReduceAndParse
        }
        LogicType* type = new LogicType;
        state.absorbRuleResult(type);
        DefineShiftAndParse(Param,*type,&LogicType::readToken)
      }
   DefineParseCase(Param)
     { logic_type typ;
       { Parser::State::RuleAccess::TCastFromRule<LogicType>
           node(state.getRuleResult());
         typ = node->extractType();
         if (!typ) {
           DefineAddError("Expecting a type in parameter declaration")
           DefineReduceAndParse
         }
       };
       state.freeRuleResult();
       AbstractToken token = arguments.queryToken();
       if (token.getType() == AbstractToken::TIdentifier) {
         std::string name =
           ((const IdentifierToken&)arguments.getContentToken()).content();
         logic_arg_decl arg = logic_arg_decl_cons(typ,copy_string(name));
         if (!_params)
           _params = _endParams = cons_container(arg,NULL);
         else {
           _endParams->next = cons_container(arg,NULL);
           _endParams = _endParams->next;
         }
         DefineGotoCase(EndParam)
       };
       DefineAddError(
         std::string("Unexpected '")
         .append(token.str())
         .append("'. Expected identifier after type in parameter declaration"))
       DefineReduceAndParse
     }
   DefineParseCase(EndParam)
    { AbstractToken token = arguments.queryToken();
      if (token.getType () == AbstractToken::TOperatorPunctuator) {
       switch (((const OperatorPunctuatorToken&)token).getType()) {
       case OperatorPunctuatorToken::TCloseParen: DefineReduceAndParse
       case OperatorPunctuatorToken::TComma: DefineGotoCase(Begin)
       default:
        DefineAddError(
          std::string("Unexpected '")
          .append(token.str())
          .append("'. Expected ')' or ',' after parameter declaration"))
        DefineReduceAndParse
       }
      } else {
       DefineAddError(
        std::string("Unexpected '")
        .append(token.str())
        .append("'. Expected ')' or ',' after parameter declaration"))
       DefineReduceAndParse
      }
    }
  }
  return result;
}

Parser::ReadResult GlobalAnnotation::LabelList::readToken(
 Parser::State& state, Parser::Arguments& arguments) {
  enum Delimiters { DBegin, DAfterId };
  ReadResult result = RRNeedChars;
  switch (state.point()) {
    DefineParseCase(Begin) {
      if (arguments.queryToken().getType() == AbstractToken::TIdentifier) {
        std::string label = ((const IdentifierToken&)
            arguments.getContentToken()).content();
        const clang::NamedDecl* cidentifier = arguments.isCodeName(label);
        logic_label logicLabel = NULL;
        arguments.addLogicLabel(label);
        if (cidentifier && cidentifier->getKind() == clang::Decl::Label)
          logicLabel = logic_label_StmtLabel(strdup(label.c_str()));
        else
          logicLabel = logic_label_LogicLabel(strdup(label.c_str()));
        list tail = cons_container(logicLabel, NULL);
        if(_endLabels) {
          _endLabels->next = tail;
        } else { // first element
            _labels = _endLabels = tail;
        }
        DefineGotoCase(AfterId)
      };
      CleanLogicLabels(arguments);
      DefineAddError("expecting identifier after logic label construction");
      DefineReduce;
    }
    DefineParseCase(AfterId) {
      AbstractToken token = arguments.queryToken();
      if (token.getType() == AbstractToken::TOperatorPunctuator) {
        OperatorPunctuatorToken::Type
          type = ((const OperatorPunctuatorToken&) token).getType();
        if (type == OperatorPunctuatorToken::TComma)
          DefineGotoCase(Begin)
         if (type == OperatorPunctuatorToken::TCloseBrace)
           DefineReduce
        };
        CleanLogicLabels(arguments);
        DefineAddError("expecting ',' or '}' in a logic label construction")
        DefineReduce
     }
    default:
      DefineAddError("unexpected parser state in LabelList")
      DefineReduce
  }
}

void
GlobalAnnotation::BuildLogicFunction(Parser::Arguments& context)
{ list /* params */ tparams = NULL;
  if (!_typeVarBinders.empty()) {
   std::list<std::string>::const_reverse_iterator iterEnd =
    _typeVarBinders.rend();
   for (std::list<std::string>::const_reverse_iterator iter = 
        _typeVarBinders.rbegin();
      iter != iterEnd;
      ++iter)
    tparams = cons_container(strdup(iter->c_str()), tparams);
   _typeVarBinders.clear();
  };
  logic_type vartype = _typeVar;
  _typeVar = NULL;

  /* logic_arg_decl */ list params = _params;
  _params = NULL;
  logic_type thisType = context.queryThisType();
  if (thisType) {
    logic_arg_decl prm = logic_arg_decl_cons(thisType,strdup("\\this"));
    params = cons_container(prm,params);
    _isMethod = true;
  }
  option ret_type = vartype?opt_some_container(vartype):opt_none();
  qualified_name name;
  if (!_qualificationId)
    name = context.makeLogicQualifiedName(_polyId);
  else
    name = qualified_name_cons(_qualificationId->makeQualificationList(),
        strdup(_polyId.c_str()));
  logic_body body = NULL;
  if (_term) body = logic_body_LBterm(_term);
  if (_pred) body = logic_body_LBpred(_pred);
  if (_hasReads) body = logic_body_LBreads(_reads.getFront());
  if (!body) body = logic_body_LBnone();
  _term=NULL; _pred = NULL;
  _hasReads = false;
  _reads = ForwardList();
  logic_info info =
   logic_info_cons(
    name,
    context.isExternCContext(),
    _polyIdLabels,
    tparams,
    ret_type,
    params, 
    body);
  _polyIdLabels = NULL;
  bool isMethod = _isMethod;
  _isMethod = false;
  if (!(_codeOperator
        ? context.addOverloadedLogicOperators(_polyId, _codeOperator,
              logic_info_dup(info), isMethod)
        : context.addOverloadedLogicFunctions(_polyId, logic_info_dup(info),
          isMethod))) {
    context.addErrorMessage(std::string("impossible to add logic function ")
        .append(_polyId));
    return;
  };
  _polyId = "";
  _globals.insertContainer(
   global_annotation_Dfun_or_pred(copy_loc(_loc), info));
  // if (body->tag_logic_body != LBNONE)
  //   _globals.insertContainer(
  //     global_annotation_Dfun_or_pred(copy_loc(_loc), info));
  // else
  //   free_logic_info(info);
}

void GlobalAnnotation::CleanLogicLabels(Parser::Arguments& context) {
  list l = _polyIdLabels;
  while(l) {
    logic_label lab = (logic_label)l->element.container;
    if (lab->tag_logic_label == LOGICLABEL) {
      context.removeLogicLabel(lab->cons_logic_label.LogicLabel.label);
    }
    if (lab->tag_logic_label == STMTLABEL) {
      context.removeLogicLabel(lab->cons_logic_label.StmtLabel.code_label);
    }
    l = l->next;
  }
}

void GlobalAnnotation::CleanFormals(Parser::Arguments& context) {
  list p = _params;
  while(p) {
    logic_arg_decl arg = (logic_arg_decl)p->element.container;
    context.removeLogicFormal(arg->la_name);
    p = p->next;
  }
}

void
GlobalAnnotation::clear() {
  if (_typeVar) {
   free_logic_type(_typeVar);
   _typeVar = NULL;
  };
  if (_term) {
   free_term(_term);
   _term = NULL;
  };
  if (_pred) {
   free_predicate_named(_pred);
   _pred = NULL;
  };
  list reads = _reads.getFront();
  while(reads) {
    free_term((term) reads->element.container);
    reads = reads->next;
  };
  _hasReads = false;
  _isMethod = false;
  if (!_typeVarBinders.empty())
   _typeVarBinders.clear();
  _polyId = "";
  while (_polyIdLabels) {
    free_logic_label((logic_label) _polyIdLabels->element.container);
    /* logic_label */ list temp = _polyIdLabels;
    _polyIdLabels = _polyIdLabels->next;
    free(temp);
  };
  _qualificationId = NULL;
  /* logic_arg_decl */ list params = _params;
  while (params) {
   free_logic_arg_decl((logic_arg_decl) params->element.container);
   /* logic_arg_decl */ list cell = params;
   params = params->next;
   free(cell);
  };
  _params = NULL;
  if (_typeName) {
    free_qualified_name(_typeName);
    _typeName = NULL;
  };
  _codeOperator = DLexer::OperatorPunctuatorToken::TUndefined;
}

Parser::ReadResult
GlobalAnnotation::readToken(Parser::State& state, Parser::Arguments& arguments)
{ enum Delimiters
  { DBegin, DLogic, DLogicOperator, DLogicEndOperator, DLogicQualification,
    DAfterLogicQualification, DOptPolyIdLabel, DFunctionArgs, DPolyIdLabel,
    DTypeVarBindersForPolyId, DEndTypeVarBindersForPolyId,
    DParam, DLogicDef, DLogicReads, DLogicReadsTerm, DPredicate,
    DPredicateQualification, DAfterPredicateQualification, DFunctionBody,
    DAxiomatic, DBeforeAxiomaticBody, DAfterAxiomaticBody, DLemma, DAxiom,
    DLemmaId, DAxiomId, DLabelLemma, DLabelAxiom, DEndLemma, DEndAxiom,
    DType, DClass, DAfterType, DTypeDef, DTypeInvariant, DClassInvariant,
    DTypeInvariantParameterList, DTypeInvariantParameter, 
    DTypeInvariantDefinition, DEndTypeInvariant, DInductive, DGlobal,
    DGlobalInvariant, DGlobalInvariantBody, DEndGlobalInvariant,
    DBeforeSemiColon
  };

  ReadResult result = RRNeedChars;
  switch (state.point()) {
    DefineParseCase(Begin)
      assert (_typeVarBinders.empty());
      arguments.setGlobalAnnotContext();
      { AbstractToken token = arguments.queryToken();
        if (token.getType() == AbstractToken::TKeyword) {
          KeywordToken::Type type = ((const KeywordToken&) token).getType();
          if (type == KeywordToken::TLogic) {
            LogicType* rule = new LogicType;
            state.absorbRuleResult(rule);
            // rule->setStopOnSuffix();
            DefineShift(Logic, *rule, &LogicType::readToken);
          }
          if (type == KeywordToken::TPredicate)
            DefineGotoCase(Predicate)
          if (type == KeywordToken::TLemma)
            DefineGotoCase(Lemma)
          if (type == KeywordToken::TAxiomatic)
            DefineGotoCase(Axiomatic)
          if (type == KeywordToken::TAxiom)
            DefineGotoCase(Axiom)
          if (type == KeywordToken::TType)
            DefineGotoCase(Type)
          if (type == KeywordToken::TClass)
            DefineGotoCase(Class)
          if (type == KeywordToken::TInductive)
            DefineGotoCase(Inductive)
          if (type == KeywordToken::TGlobal)
            DefineGotoCase(Global)
        };
        if (token.getType() == AbstractToken::TOperatorPunctuator) {
          if (((const OperatorPunctuatorToken&) token).getType()
              == OperatorPunctuatorToken::TCloseBrace) {
            arguments.resetAnnotContext();
            DefineReduceAndParse
          };
        }
      };
      arguments.resetAnnotContext();
      DefineAddError("expecting 'logic', 'predicate' or 'lemma' keyword")
      DefineGotoCase(Begin)
    DefineParseCase(Logic)
      { Parser::State::RuleAccess::TCastFromRule<LogicType>
          rule(state.getRuleResult());
        _typeVar = rule->extractType();
        state.freeRuleResult();
      };
      { AbstractToken token = arguments.queryToken();
        AbstractToken::Type type = token.getType();
        if (type == AbstractToken::TOperatorPunctuator) {
          if (((const OperatorPunctuatorToken&) token).getType()
             == OperatorPunctuatorToken::TLess) {
            assert(false); // handled by the LogicType rule = [TODO]
          }
        }
        if (type == AbstractToken::TKeyword) {
          if (((const KeywordToken&) token).getType()
              == KeywordToken::TOperator) {
            logic_type thisRecordType = arguments.queryThisType();
            if (thisRecordType) {
              _isMethod = true;
              arguments.addLogicFormal("\\this", thisRecordType);
            }
            DefineGotoCase(LogicOperator)
          };
        }
      };
      if (arguments.queryToken().getType() == AbstractToken::TIdentifier) {
        _polyId = ((const IdentifierToken&)
            arguments.getContentToken()).content();
        absorbLoc(arguments.newTokenLocation());
        DefineGotoCase(LogicQualification)
      };
      DefineAddError("expecting identifier after 'logic type-var'");
      DefineGotoCase(BeforeSemiColon);
    DefineParseCase(LogicOperator)
      { AbstractToken token = arguments.queryToken();
        if (token.getType() == AbstractToken::TOperatorPunctuator) {
          if (((const OperatorPunctuatorToken&) token).isOverloadable()) {
            OperatorPunctuatorToken concreteToken(
                (const OperatorPunctuatorToken&) token);
            std::ostringstream name;
            name << "operator";
            concreteToken.writeSign(name);
            OperatorPunctuatorToken::Type operatorType
              = ((const OperatorPunctuatorToken&) token).getType();
            if (operatorType == OperatorPunctuatorToken::TOpenBracket)
              name << ']';
            else if (operatorType == OperatorPunctuatorToken::TOpenParen)
              name << ')';
            _polyId = name.str();
            if (!_qualificationId) absorbLoc(arguments.newTokenLocation());
            _codeOperator = operatorType;
            if (operatorType == OperatorPunctuatorToken::TOpenBracket
                || operatorType == OperatorPunctuatorToken::TOpenParen)
              DefineGotoCase(LogicEndOperator);
            DefineGotoCase(OptPolyIdLabel)
          };
        };
      };
      CleanFormals(arguments);
      arguments.resetAnnotContext();
      DefineAddError("expecting an overloadable operator"
          " after 'logic type-var operator'");
      DefineGotoCase(BeforeSemiColon);
    DefineParseCase(LogicEndOperator)
      { AbstractToken token = arguments.queryToken();
        if (token.getType() == AbstractToken::TOperatorPunctuator) {
          OperatorPunctuatorToken::Type operatorType
            = ((const OperatorPunctuatorToken&) token).getType();
          bool endParse = false;
          if (operatorType == OperatorPunctuatorToken::TCloseBracket
              && _codeOperator == OperatorPunctuatorToken::TOpenBracket)
            endParse = true;
          if (operatorType == OperatorPunctuatorToken::TCloseParen
              && _codeOperator == OperatorPunctuatorToken::TOpenParen)
            endParse = true;
          if (endParse)
            DefineGotoCase(OptPolyIdLabel)
        };
      };
      arguments.resetAnnotContext();
      DefineAddError("expecting an overloadable operator"
          " after 'logic type-var operator'");
      DefineGotoCase(BeforeSemiColon);
    DefineParseCase(LogicQualification)
    DefineParseCase(PredicateQualification)
LQualification:
      { AbstractToken token = arguments.queryToken();
        if (token.getType() == AbstractToken::TOperatorPunctuator) {
          OperatorPunctuatorToken::Type type
            = ((const OperatorPunctuatorToken&) token).getType();
          if (type == OperatorPunctuatorToken::TColonColon) {
            GlobalContext::NestedContext* found = NULL;
            if (!_qualificationId)
              found = arguments.findLogicName(_polyId);
            else
              found = arguments.get_clang_utils()->globalAcslContext()
                .find(_polyId, _qualificationId);
            if (!found || !found->isQualification()) {
              CleanFormals(arguments);
              DefineAddError("unbound qualification for 'logic qual::id ...'")
            }
            else
              _qualificationId = (GlobalContext::Qualification*) found;
            _polyId = "";
            DefineGotoCaseWithIncrement(DAfterLogicQualification
                - DLogicQualification, LAfterQualification)
          };
          if (type == OperatorPunctuatorToken::TOpenBrace) {
            DefineGotoCaseAndParse(OptPolyIdLabel)
          }
        };
        logic_type thisRecordType = NULL;
        if (!_qualificationId)
          thisRecordType = arguments.queryThisType();
        else if (_qualificationId->hasRecordType()) {
          // we are giving an out-of-line definition for a predicate or
          // logic function declared inside a class.
          qualified_name name = _qualificationId->makeRecordName();
          thisRecordType = arguments.makeLogicType(name);
          free_qualified_name(name);
        };
        if (thisRecordType) {
          _isMethod = true;
          arguments.addLogicFormal("\\this", thisRecordType);
        }
        DefineGotoCaseAndParse(FunctionArgs)
      }
    DefineParseCase(AfterLogicQualification)
    DefineParseCase(AfterPredicateQualification)
LAfterQualification:
      { AbstractToken token = arguments.queryToken();
        AbstractToken::Type type = token.getType();
        if (type == AbstractToken::TOperatorPunctuator) {
          if (((const OperatorPunctuatorToken&) token).getType()
             == OperatorPunctuatorToken::TLess) {
            assert(false); // handled by the LogicType rule = [TODO]
          }
        }
        if (state.point() == DAfterLogicQualification
            && type == AbstractToken::TKeyword) {
          if (((const KeywordToken&) token).getType()
              == KeywordToken::TOperator) {
            assert(_qualificationId);
            logic_type thisRecordType = NULL;
            if (_qualificationId->hasRecordType()) {
              qualified_name name = _qualificationId->makeRecordName();
              thisRecordType = arguments.makeLogicType(name);
              free_qualified_name(name);
            };
            if (thisRecordType) {
              _isMethod = true;
              arguments.addLogicFormal("\\this", thisRecordType);
            }
            DefineGotoCase(LogicOperator)
          };
        }
      };
      if (arguments.queryToken().getType() == AbstractToken::TIdentifier) {
        _polyId = ((const IdentifierToken&)
            arguments.getContentToken()).content();
        DefineGotoCaseWithIncrement(
            DLogicQualification - DAfterLogicQualification, LQualification)
      };
      arguments.resetAnnotContext();
      DefineAddError("expecting identifier after 'logic qual::...'");
      DefineGotoCase(BeforeSemiColon);
    DefineParseCase(OptPolyIdLabel)
      { AbstractToken token = arguments.queryToken();
        if (token.getType() == AbstractToken::TOperatorPunctuator) {
          if (((const OperatorPunctuatorToken&) token).getType()
              == OperatorPunctuatorToken::TOpenBrace) {
            LabelList* labels = new LabelList;
            state.absorbRuleResult(labels);
            DefineShift(PolyIdLabel,*labels,&LabelList::readToken)
          }
        };
      };
      DefineGotoCaseAndParse(FunctionArgs)
    DefineParseCase(PolyIdLabel) {
        Parser::State::RuleAccess::TCastFromRule<LabelList>
          labels(state.getRuleResult());
        _polyIdLabels = labels->extractLabels();
        state.freeRuleResult();
        DefineGotoCaseAndParse(FunctionArgs)
    }
    DefineParseCase(FunctionArgs)
      { AbstractToken token = arguments.queryToken();
        if (token.getType() == AbstractToken::TOperatorPunctuator) {
          OperatorPunctuatorToken::Type type
            = ((const OperatorPunctuatorToken&) token).getType();
          if (type == OperatorPunctuatorToken::TLess) {
            if (!_typeVarBinders.empty()) {
              CleanLogicLabels(arguments);
              DefineAddError("multiple var bindings "
                  "in 'logic type-var<...><...>'")
                }
            DefineGotoCase(TypeVarBindersForPolyId)
          };
          if (type == OperatorPunctuatorToken::TOpenParen) {
            if (_params) {
              CleanLogicLabels(arguments);
              DefineAddError("multiple parameters "
                  "in 'logic type-var(...)(...)'")
            }
            Parameters* parameters = new Parameters(_loc);
            state.absorbRuleResult(parameters);
            DefineShift(Param, *parameters, &Parameters::readToken)
            // inlined version
            //  DefineGotoCase(Param)
          };
          DefineGotoCaseAndParse(FunctionBody);
        };
        arguments.lexer().assumeContentToken();
        CleanLogicLabels(arguments);
        CleanFormals(arguments);
        arguments.resetAnnotContext();
        DefineAddError(std::string("unexpected token '")
          .append(arguments.getContentToken().str())
          .append("' in logic function/predicate definition"));
        clear();
        DefineGotoCase(Begin)
      }
    DefineParseCase(FunctionBody)
      { AbstractToken token = arguments.queryToken();
        if (token.getType() == AbstractToken::TOperatorPunctuator) {
          OperatorPunctuatorToken::Type
            type = ((const OperatorPunctuatorToken&)token).getType();
          if (type == OperatorPunctuatorToken::TAssign) {
            TermOrPredicate* term = new TermOrPredicate;
            if (_typeVar)
              state.absorbRuleResult(&term->setTerm());
            else
              state.absorbRuleResult(&term->setPredicate());
            DefineShift(LogicDef, *term, &TermOrPredicate::readToken)
          }
          if (type == OperatorPunctuatorToken::TSemiColon) {
            CleanLogicLabels(arguments);
            CleanFormals(arguments);
            BuildLogicFunction(arguments);
            arguments.resetAnnotContext();
            DefineGotoCase(Begin);
          }
        }
        if (token.getType() == AbstractToken::TKeyword) {
          KeywordToken::Type type = ((const KeywordToken&) token).getType();
          if (type == KeywordToken::TReads)
            DefineGotoCase(LogicReads)
        };
        arguments.lexer().assumeContentToken();
        CleanLogicLabels(arguments);
        CleanFormals(arguments);
        arguments.resetAnnotContext();
        DefineAddError(std::string("unexpected token '")
         .append(arguments.getContentToken().str())
         .append("' in logic function/predicate definition"));
        clear();
        DefineGotoCase(Begin)
      };
    DefineParseCase(TypeVarBindersForPolyId)
      if (arguments.queryToken().getType() == AbstractToken::TIdentifier) {
        _typeVarBinders.push_back(((const IdentifierToken&)
            arguments.getContentToken()).content());
        DefineGotoCase(EndTypeVarBindersForPolyId)
      }
      CleanLogicLabels(arguments);
      DefineAddError("expecting identifier for xx in 'logic type-var<xx, ...>'")
      DefineGotoCase(EndTypeVarBindersForPolyId)
    DefineParseCase(EndTypeVarBindersForPolyId)
      { AbstractToken token = arguments.queryToken();
        if (token.getType() == AbstractToken::TOperatorPunctuator) {
          OperatorPunctuatorToken::Type type
            = ((const OperatorPunctuatorToken&) token).getType();
          if (type == OperatorPunctuatorToken::TComma)
            DefineGotoCase(TypeVarBindersForPolyId)
          if (type == OperatorPunctuatorToken::TGreater)
            DefineGotoCase(OptPolyIdLabel)
        };
        CleanLogicLabels(arguments);
        DefineAddError("expecting end of binding '>' in 'logic type-var<id >'")
        DefineGotoCase(EndTypeVarBindersForPolyId)
      };
    DefineParseCase(Param)
      { AbstractToken token = arguments.queryToken();
        if (token.getType() == AbstractToken::TOperatorPunctuator) {
          OperatorPunctuatorToken::Type
            type = ((const OperatorPunctuatorToken&) token).getType();
         if (type == OperatorPunctuatorToken::TCloseParen) {
            Parser::State::RuleAccess::TCastFromRule<Parameters>
              params(state.getRuleResult());
            _params = params->extractParams();
            state.freeRuleResult();
            list tmp_prms = _params;
            while (tmp_prms) {
              logic_arg_decl prm = (logic_arg_decl) tmp_prms->element.container;
              if (arguments.hasLogicFormal(prm->la_name)) {
                CleanLogicLabels(arguments);
                CleanFormals(arguments);
                DefineAddError(std::string("Variable ").append(prm->la_name)
                  .append(" is declared twice as formal of function ")
                  .append(_polyId).append("."));
              }
              else
                arguments.addLogicFormal(prm->la_name,prm->la_type);
              tmp_prms = tmp_prms->next;
            }
            DefineGotoCase(FunctionBody);
          };
        };
      };
      DefineAddError("expecting ')' at the end of a list of parameters");
      DefineGotoCase(Param)
    DefineParseCase(LogicDef)
      { { Parser::State::RuleAccess::TCastFromRule<TermOrPredicate>
            node(state.getRuleResult());
          if (_typeVar) {
            logic_type ltypeTerm = NULL;
            _term = node->extractTerm(arguments, ltypeTerm);
            if (_term) {
               if (_typeVar && !logic_type_equal(_typeVar, ltypeTerm))
                 _term = TermOrPredicate::implicitConversion(_typeVar, _term,
                     ltypeTerm, false, arguments);
               else
                 free_logic_type(ltypeTerm);
            };
            if (!_term) {
              CleanLogicLabels(arguments);
              CleanFormals(arguments);
              arguments.resetAnnotContext();
              DefineAddError("expecting a term as body of function");
              DefineReduceAndParse
            };
          }
          else {
            _pred = node->extractPredicate(arguments);
            if (!_pred) {
              arguments.resetAnnotContext();
              DefineAddError("expecting a predicate");
              DefineReduceAndParse
            };
          };
          extend_location_with(_loc, node->getLocation());
          state.freeRuleResult();
        };
        AbstractToken token = arguments.queryToken();
        if (token.getType() == AbstractToken::TOperatorPunctuator) {
          OperatorPunctuatorToken::Type
            type = ((const OperatorPunctuatorToken&) token).getType();
          if (type == OperatorPunctuatorToken::TSemiColon) {
            CleanLogicLabels(arguments);
            CleanFormals(arguments);
            BuildLogicFunction(arguments);
            arguments.resetAnnotContext();
            DefineGotoCase(Begin);
          }
        }
      }
      CleanLogicLabels(arguments);
      CleanFormals(arguments);
      DefineAddError("';' expected after logic function definition")
      DefineGotoCase(BeforeSemiColon)
    DefineParseCase(LogicReads)
      { AbstractToken token = arguments.queryToken();
        if (token.getType() == AbstractToken::TKeyword) {
          if (((const KeywordToken&) token).getType() == KeywordToken::TNothing)
          {
            CleanLogicLabels(arguments);
            CleanFormals(arguments);
            arguments.extendLocationWithToken(_loc);
            BuildLogicFunction(arguments);
            DefineGotoCase(BeforeSemiColon);
          }
        }
        _hasReads = true;
        TermOrPredicate* term = new TermOrPredicate;
        state.absorbRuleResult(&term->setTerm());
        DefineShiftAndParse(LogicReadsTerm, *term, &TermOrPredicate::readToken)
      }
    DefineParseCase(LogicReadsTerm)
      { Parser::State::RuleAccess::TCastFromRule<TermOrPredicate>
            termReads(state.getRuleResult());
        logic_type ltype = NULL;
        term readTerm = termReads->extractTermOrSet(arguments,ltype);
        if (readTerm)
          _reads.insertContainer(readTerm);
        extend_location_with(_loc, termReads->getLocation());
        state.freeRuleResult();
      }
      { AbstractToken token = arguments.queryToken();
        if (token.getType() == AbstractToken::TOperatorPunctuator) {
          OperatorPunctuatorToken::Type type = ((const OperatorPunctuatorToken&)
              token).getType();
          if (type == OperatorPunctuatorToken::TComma) { 
            TermOrPredicate* term = new TermOrPredicate;
            state.absorbRuleResult(&term->setTerm());
            DefineShift(LogicReadsTerm, *term, &TermOrPredicate::readToken)
          }
          if (type == OperatorPunctuatorToken::TSemiColon) {
            CleanLogicLabels(arguments);
            CleanFormals(arguments);
            BuildLogicFunction(arguments);
            arguments.resetAnnotContext();
            DefineGotoCase(Begin)
          }
        }
      }
      CleanLogicLabels(arguments);
      CleanFormals(arguments);
      arguments.resetAnnotContext();
      DefineAddError("expecting ',' or ';' after logic reads clause "
          "in function definition")
      DefineGotoCase(BeforeSemiColon);
    DefineParseCase(Predicate)
      if (arguments.queryToken().getType() == AbstractToken::TIdentifier) {
        _polyId = ((const IdentifierToken&) arguments.getContentToken())
          .content();
        absorbLoc(arguments.newTokenLocation());
        DefineGotoCase(PredicateQualification)
      };
      CleanLogicLabels(arguments);
      CleanFormals(arguments);
      arguments.resetAnnotContext();
      DefineAddError("expecting an identifier after 'predicate'");
      DefineGotoCase(BeforeSemiColon);
    DefineParseCase(Axiomatic)
      if (arguments.queryToken().getType() == AbstractToken::TIdentifier) {
        _polyId = ((const IdentifierToken&) arguments.getContentToken())
          .content();
        absorbLoc(arguments.newTokenLocation());
        DefineGotoCase(BeforeAxiomaticBody)
      };
      arguments.resetAnnotContext();
      DefineAddError("expecting an identifier after 'axiomatic id...'")
      DefineReduceAndParse
    DefineParseCase(BeforeAxiomaticBody)
      { AbstractToken token = arguments.queryToken();
        if (token.getType() == AbstractToken::TOperatorPunctuator) {
          OperatorPunctuatorToken::Type
            type = ((const OperatorPunctuatorToken&) token).getType();
          if (type == OperatorPunctuatorToken::TOpenBrace) {
            GlobalAnnotation* rule = new GlobalAnnotation(_loc);
            state.absorbRuleResult(rule);
            rule->_polyAxiomId = _polyId;
            DefineShift(AfterAxiomaticBody, *rule, &GlobalAnnotation::readToken)
          };
        };
      };
   DefineParseCase(AfterAxiomaticBody)
     { AbstractToken token = arguments.queryToken();
       if (token.getType() == AbstractToken::TOperatorPunctuator) {
          OperatorPunctuatorToken::Type
            type = ((const OperatorPunctuatorToken&) token).getType();
          if (type == OperatorPunctuatorToken::TCloseBrace) {
            Parser::State::RuleAccess::TCastFromRule<GlobalAnnotation>
              rule(state.getRuleResult());
            extend_location_with(_loc, rule->_loc);
            _globals.insertContainer(global_annotation_Daxiomatic(
                copy_loc(_loc), strdup(_polyId.c_str()), rule->_annots));
            _polyId = "";
            rule->_annots = NULL;
            state.freeRuleResult();
            clear();
            arguments.resetAnnotContext();
            DefineGotoCase(Begin)
          };
        };
      };
      DefineAddError("expecting a '}' after 'axiomatic id { ... '")
      DefineGotoCaseAndParse(BeforeSemiColon)
    DefineParseCase(Lemma)
    DefineParseCase(Axiom)
      if (arguments.queryToken().getType()
          == AbstractToken::TIdentifier) {
        _polyId = ((const IdentifierToken&) arguments.getContentToken())
          .content();
        if (state.point() == DAxiom && _polyAxiomId == "") {
          DefineAddError(std::string("axiom ").append(_polyId)
            .append(" should be declared inside an axiomatic"));
          absorbLoc(arguments.newTokenLocation());
        }
        DefineGotoCaseWithIncrement(DAxiomId - DAxiom, LAxiomId)
      };
      DefineAddError("expecting an identifier after 'axiom id...'")
      DefineGotoCaseAndParse(BeforeSemiColon)
    DefineParseCase(LemmaId)
    DefineParseCase(AxiomId)
      { AbstractToken token = arguments.queryToken();
        if (token.getType() == AbstractToken::TOperatorPunctuator) {
          OperatorPunctuatorToken::Type
            type = ((const OperatorPunctuatorToken&) token).getType();
          if (type == OperatorPunctuatorToken::TColon) {
            TermOrPredicate* rule = new TermOrPredicate;
            state.absorbRuleResult(rule);
            DefineShiftWithIncrement(DEndAxiom - DAxiomId, LEndAxiom,
                *rule, &TermOrPredicate::readToken);
          } else if (type == OperatorPunctuatorToken::TOpenBrace) {
            if (_polyIdLabels) {
              DefineAddError(
                "multiple declaration of logic labels { ... } { ... }")
            }
            LabelList* rule = new LabelList;
            state.absorbRuleResult(rule);
            DefineShiftWithIncrement(
              DLabelAxiom - DAxiomId, LLabelAxiom,*rule,&LabelList::readToken)
          };
        };
      };
      DefineAddError("expecting ':' after \"axiom id...\"")
      { TermOrPredicate* rule = new TermOrPredicate;
        state.absorbRuleResult(rule);
        DefineShiftWithIncrement(DEndAxiom - DAxiomId, LEndAxiom,
            *rule, &TermOrPredicate::readToken);
      };
    DefineParseCase(LabelLemma)
    DefineParseCase(LabelAxiom)
      {
        Parser::State::RuleAccess::TCastFromRule<LabelList>
          labels(state.getRuleResult());
        _polyIdLabels = labels->extractLabels();
        state.freeRuleResult();
        DefineGotoCaseAndParseWithIncrement(DAxiomId-DLabelAxiom,LAxiomId)
      }
    DefineParseCase(EndLemma)
    DefineParseCase(EndAxiom)
      { AbstractToken token = arguments.queryToken();
        if (token.getType() == AbstractToken::TOperatorPunctuator) {
          OperatorPunctuatorToken::Type type
            = ((const OperatorPunctuatorToken&) token).getType();
          if (type == OperatorPunctuatorToken::TSemiColon) {
            Parser::State::RuleAccess::TCastFromRule<TermOrPredicate>
                axiom(state.getRuleResult());
            predicate_named pred = axiom->extractPredicate(arguments);
            if (pred) {
              _globals.insertContainer(global_annotation_Dlemma(
                copy_loc(_loc),
                strdup(_polyId.c_str()),
                state.point() == DEndAxiom,
                _polyIdLabels,
                NULL /* ids */,
                pred));
              CleanLogicLabels(arguments);
              _polyIdLabels = NULL;
            }
            state.freeRuleResult();
            _polyId = "";
            CleanFormals(arguments);
            arguments.resetAnnotContext();
            DefineGotoCase(Begin)
          };
        };
      };
      DefineGotoCase(EndAxiom)
    DefineParseCase(Type)
      { AbstractToken token = arguments.queryToken();
        if (token.getType() == AbstractToken::TIdentifier) {
          _polyId = ((const IdentifierToken&) arguments.getContentToken())
            .content();
          absorbLoc(arguments.newTokenLocation());
          DefineGotoCase(AfterType)
        }
        else if (token.getType() == AbstractToken::TKeyword) {
          if (((const KeywordToken&) token).getType()
              == KeywordToken::TInvariant)
          DefineGotoCase(TypeInvariant)
        };
      };
      DefineAddError("expecting identifier or 'invariant' after keyword 'type'")
      DefineGotoCase(BeforeSemiColon)
    DefineParseCase(Class)
      { AbstractToken token = arguments.queryToken();
        if (token.getType() == AbstractToken::TKeyword) {
          if (((const KeywordToken&) token).getType()
              == KeywordToken::TInvariant)
            DefineGotoCase(ClassInvariant)
        };
      };
      DefineAddError("expecting identifier or 'invariant' after keyword 'type'")
      DefineGotoCase(BeforeSemiColon)
    DefineParseCase(AfterType)
      { AbstractToken token = arguments.queryToken();
        if (token.getType() == AbstractToken::TOperatorPunctuator) {
          OperatorPunctuatorToken::Type
            type = ((const OperatorPunctuatorToken&) token).getType();
          if (type == OperatorPunctuatorToken::TLess) {
            if (!_typeVarBinders.empty())
              DefineAddError("multiple var bindings "
                  "in 'logic type-var<...><...>'")
            DefineGotoCase(TypeVarBindersForPolyId)
          };
          if (type == OperatorPunctuatorToken::TAssign) {
            assert(!_typeName);
            _typeName = arguments.makeLogicQualifiedName(_polyId);
            LogicType* rule = new LogicType(_typeName);
            state.absorbRuleResult(rule);
            DefineShift(TypeDef, *rule, &LogicType::readToken)
          };
          if (type == OperatorPunctuatorToken::TSemiColon) {
            qualified_name typeName = arguments.makeLogicQualifiedName(_polyId);
            bool extern_c = arguments.isExternCContext();
            logic_type_info info =
              logic_type_info_cons(
                qualified_name_dup(typeName), extern_c, NULL, opt_none());
            arguments.addLogicType(_polyId, logic_type_info_dup(info));
            _globals.insertContainer(global_annotation_Dtype(copy_loc(_loc),
                  info));
            _polyId = "";
            arguments.resetAnnotContext();
            DefineGotoCase(Begin);
          }
        };
        DefineAddError("expecting assignment '=' after 'logic type-var'")
      };
    DefineParseCase(TypeDef)
      { Parser::State::RuleAccess::TCastFromRule<LogicType>
          definition(state.getRuleResult());
        /* string */ list params = NULL;
        if (!_typeVarBinders.empty()) {
          std::list<std::string>::const_iterator
            paramIterEnd = _typeVarBinders.end();
          std::list<std::string>::const_iterator
            paramIter = _typeVarBinders.begin();
          list endParams = params = cons_container(strdup(paramIter->c_str()),
              NULL);
          for (++paramIter; paramIter != paramIterEnd; ++paramIter) {
            endParams->next = cons_container(strdup(paramIter->c_str()), NULL);
            endParams = endParams->next;
          };
        };
        bool extern_c = arguments.isExternCContext();
        logic_type_info info =
          logic_type_info_cons(
            _typeName, extern_c, params,
            opt_some_container(definition->extractTypeDef()));
        arguments.addLogicType(_typeName->decl_name, logic_type_info_dup(info));
        _globals.insertContainer(global_annotation_Dtype(copy_loc(_loc), info));
        state.freeRuleResult();
        _typeVarBinders.clear();
        _typeName = NULL;
        _params = NULL;
        clear();
        arguments.resetAnnotContext();
        DefineGotoCase(Begin)
      }
    DefineParseCase(TypeInvariant)
      { AbstractToken token = arguments.queryToken();
        if (token.getType() == AbstractToken::TIdentifier) {
          _polyId = ((const IdentifierToken&) arguments.getContentToken())
            .content();
          absorbLoc(arguments.newTokenLocation());
          DefineGotoCase(TypeInvariantParameterList)
        }
      };
      arguments.resetAnnotContext();
      DefineAddError("expecting an identifier "
          "after the construction 'type invariant'")
      DefineGotoCase(BeforeSemiColon)
    DefineParseCase(ClassInvariant)
      { AbstractToken token = arguments.queryToken();
        if (token.getType() == AbstractToken::TIdentifier) {
          _polyId = ((const IdentifierToken&) arguments.getContentToken())
            .content();
          absorbLoc(arguments.newTokenLocation());
          logic_type thisRecordType = arguments.queryThisType();
          if (thisRecordType) {
            _isMethod = true;
            arguments.addLogicFormal("\\this", thisRecordType);
            assert (!_params);
            _params =
              cons_container(
                logic_arg_decl_cons(logic_type_dup(thisRecordType),"\\this"),
                NULL);
          } else {
            DefineAddError("class invariant outside of a class");
          }
          DefineGotoCase(TypeInvariantDefinition)
        }
      };
      arguments.resetAnnotContext();
      DefineAddError("expecting an identifier "
          "after the construction 'class invariant'")
      DefineGotoCase(BeforeSemiColon)
    DefineParseCase(TypeInvariantParameterList)
      { AbstractToken token = arguments.queryToken();
        if (token.getType() == AbstractToken::TOperatorPunctuator) {
          if (((const OperatorPunctuatorToken&) token).getType()
              == OperatorPunctuatorToken::TOpenParen) {
            if (_params) {
              DefineAddError("multiple parameters "
                  "in 'type invariant type-var(...)(...)'")
                }
            Parameters* parameters = new Parameters(_loc);
            state.absorbRuleResult(parameters);
            DefineShift(TypeInvariantParameter, *parameters,
                &Parameters::readToken)
          };
        };
      }
      arguments.resetAnnotContext();
      DefineAddError("':' expected after the construction "
          "'global invariant id'")
      DefineGotoCase(BeforeSemiColon)
    DefineParseCase(TypeInvariantParameter)
      { AbstractToken token = arguments.queryToken();
        if (token.getType() == AbstractToken::TOperatorPunctuator) {
          if (((const OperatorPunctuatorToken&) token).getType()
              == OperatorPunctuatorToken::TCloseParen) {
            Parser::State::RuleAccess::TCastFromRule<Parameters>
              params(state.getRuleResult());
            _params = params->extractParams();
            if (_params != NULL) {
              /* logic_arg_decl */ list iter = _params;
              while (iter) {
                logic_arg_decl prm = (logic_arg_decl) iter->element.container;
                if (arguments.hasLogicFormal(prm->la_name)) {
                  DefineAddError(std::string("Variable ").append(prm->la_name)
                    .append(" is declared twice as formal of type ")
                    .append(_polyId).append("."));
                }
                else
                  arguments.addLogicFormal(prm->la_name,prm->la_type);
                iter = iter->next;
              };
            };
            state.freeRuleResult();
            if (!_params || _params->next) {
              DefineAddError("only one parameter is allowed "
                  "in a type parameter definition");
            }
            DefineGotoCase(TypeInvariantDefinition) 
          };
        };
      };
      arguments.resetAnnotContext();
      DefineAddErrorAndParse("expecting a ')' at the end "
          "of a type parameter definition");
    DefineParseCase(TypeInvariantDefinition)
      { AbstractToken token = arguments.queryToken();
        if (token.getType() == AbstractToken::TOperatorPunctuator) {
          if (((const OperatorPunctuatorToken&) token).getType()
              == OperatorPunctuatorToken::TAssign) {
            TermOrPredicate* def = new TermOrPredicate;
            state.absorbRuleResult(def);
            def->setPredicate();
            DefineShift(EndTypeInvariant, *def, &TermOrPredicate::readToken);
          };
        };
      };
      CleanFormals(arguments);
      arguments.resetAnnotContext();
      DefineAddError("'=' expected in a type or class invariant definition");
      DefineGotoCase(BeforeSemiColon)
    DefineParseCase(EndTypeInvariant)
      { AbstractToken token = arguments.queryToken();
        if (token.getType() == AbstractToken::TOperatorPunctuator) {
          if (((const OperatorPunctuatorToken&) token).getType()
              == OperatorPunctuatorToken::TSemiColon) {
            Parser::State::RuleAccess::TCastFromRule<TermOrPredicate>
                def(state.getRuleResult());
            extend_location_with(_loc, def->getLocation());
            predicate_named subdef = def->extractPredicate(arguments);
            if (!subdef) {
              CleanFormals(arguments);
              arguments.resetAnnotContext();
              DefineAddError("expecting a predicate");
              DefineReduceAndParse
            };
            logic_info info =
              logic_info_cons(
                arguments.makeLogicQualifiedName(_polyId),
                arguments.isExternCContext(),
                NULL, NULL /* string list tparams */,
                opt_none() /* logic_type option returned_type */,
                _params /* logic_arg_decl list profile */,
                logic_body_LBpred(subdef));
            CleanFormals(arguments);
            _params = NULL;
            arguments.addOverloadedLogicFunctions(_polyId,
                logic_info_dup(info), _isMethod);
            _globals.insertContainer(
              global_annotation_Dtype_annot(copy_loc(_loc), info));
            state.freeRuleResult();
            _polyId = "";
            clear();
            arguments.resetAnnotContext();
            DefineGotoCase(Begin)
          };
        };
      };
      DefineAddError("';' expected after a type invariant definition")
      DefineGotoCase(EndTypeInvariant)
    DefineParseCase(Inductive)
      DefineAddError("unimplemented case")

    DefineParseCase(Global)
      { AbstractToken token = arguments.queryToken();
        if (token.getType() == AbstractToken::TKeyword) {
          if (((const KeywordToken&) token).getType()
              == KeywordToken::TInvariant)
          DefineGotoCase(GlobalInvariant)
        };
      };
      arguments.resetAnnotContext();
      DefineAddError("expecting 'invariant' after keyword 'global'")
      DefineGotoCase(BeforeSemiColon)
    DefineParseCase(GlobalInvariant)
      { AbstractToken token = arguments.queryToken();
        if (token.getType() == AbstractToken::TIdentifier) {
          _polyId = ((const IdentifierToken&)
              arguments.getContentToken()).content();
          absorbLoc(arguments.newTokenLocation());
          DefineGotoCase(GlobalInvariantBody)
        }
      };
      arguments.resetAnnotContext();
      DefineAddError("expecting an identifier after the construction "
          "'global invariant'")
      DefineGotoCase(BeforeSemiColon)
    DefineParseCase(GlobalInvariantBody)
      { AbstractToken token = arguments.queryToken();
        if (token.getType() == AbstractToken::TOperatorPunctuator) {
          if (((const OperatorPunctuatorToken&) token).getType()
              == OperatorPunctuatorToken::TColon) {
            TermOrPredicate* rule = new TermOrPredicate;
            state.absorbRuleResult(rule);
            rule->setPredicate();
            DefineShift(EndGlobalInvariant, *rule, &TermOrPredicate::readToken);
          };
        };
      }
      arguments.resetAnnotContext();
      DefineAddError("':' expected after the construction "
          "'global invariant id'")
      DefineGotoCase(BeforeSemiColon)
    DefineParseCase(EndGlobalInvariant)
      { AbstractToken token = arguments.queryToken();
        if (token.getType() == AbstractToken::TOperatorPunctuator) {
          if (((const OperatorPunctuatorToken&) token).getType()
              == OperatorPunctuatorToken::TSemiColon) {
            Parser::State::RuleAccess::TCastFromRule<TermOrPredicate>
              definition(state.getRuleResult());
            extend_location_with(_loc, definition->getLocation());
            predicate_named subdef = definition->extractPredicate(arguments);
            if (!subdef) {
              arguments.resetAnnotContext();
              DefineAddError("expecting a predicate");
              DefineReduceAndParse
            };
            logic_info info = logic_info_cons(
                arguments.makeLogicQualifiedName(_polyId),
                arguments.isExternCContext(),
                cons_container(logic_label_LogicLabel(strdup("here")), NULL),
                NULL /* string list tparams */,
                opt_none() /* logic_type option returned_type */,
                NULL /* logic_arg_decl list profile */,
                logic_body_LBpred(subdef));
            arguments.addOverloadedLogicFunctions(_polyId,
                logic_info_dup(info), _isMethod);
            _globals.insertContainer(global_annotation_Dinvariant(
                copy_loc(_loc), info));
            state.freeRuleResult();
            clear();
            DefineGotoCase(Begin)
          };
        };
      }
      arguments.resetAnnotContext();
      DefineAddError("':' expected after the construction "
          "'global invariant id'")
      DefineGotoCase(BeforeSemiColon)
    DefineParseCase(BeforeSemiColon)
      { AbstractToken token = arguments.queryToken();
        if (token.getType() == AbstractToken::TOperatorPunctuator) {
          if (((const OperatorPunctuatorToken&) token).getType()
              == OperatorPunctuatorToken::TSemiColon) {
            clear();
            arguments.resetAnnotContext();
            DefineGotoCase(Begin);
          }
        };
      };
      DefineGotoCase(BeforeSemiColon)
  };
  return result;
}

#if defined(__clang__) || defined(__GNUC__)
#pragma GCC diagnostic pop
#endif

} // end of namespace Acsl

