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
//   Definition of the ACSL global annotations.
//

#ifndef ACSL_GlobalAnnotationH
#define ACSL_GlobalAnnotationH

#include "ACSLParser.h"
// #include "DescentParse.h"

extern "C" {
#include "intermediate_format.h"
} // end of extern "C"

#include "ACSLLogicType.h"
#include "ACSLTermOrPredicate.h"

namespace Acsl {

/*! @class GlobalAnnotation
 *  @brief Component that parses a global annotation with a state machine.
 *
 *  The state is defined by the Parser::State::point() method and has
 *    additional information within the fields typeVar, _term, _pred,
 *    _params, _typeVarBinders, _polyId, _polyIdLabels, _typeName
 */
class GlobalAnnotation : public ::Parser::Base::RuleResult,
    public ::Parser::Base {
private:
  list _annots;
  ForwardReferenceList _globals;
  location _loc;
  logic_type _typeVar;
  term _term;
  predicate_named _pred;
  bool _hasReads;
  bool _isMethod;
  ForwardList _reads;
  /* logic_arg_decl */ list _params;
  std::list<std::string> _typeVarBinders;
  GlobalContext::Qualification* _qualificationId;
  std::string _polyId;
  std::string _polyAxiomId;
  /* logic_label */ list _polyIdLabels;
  DLexer::OperatorPunctuatorToken::Type _codeOperator;
  qualified_name _typeName;
 
  void BuildLogicFunction(Parser::Arguments& context);

  void absorbLoc(location l) { if (_loc) free_location(_loc); _loc = l; }

  /*! clean up environment after parsing an annotation */
  void CleanFormals(Parser::Arguments& context);

  void CleanLogicLabels(Parser::Arguments& context);

  class LabelList: public ::Parser::Base::RuleResult {
  private:
    /* logic_label */ list _labels, _endLabels;
  public:
    LabelList(): 
    _labels(NULL), _endLabels(NULL) { }
    ~LabelList() {
      while(_labels) {
        free(_labels->element.container);
        list temp = _labels->next;
        free(_labels);
        _labels = temp;
      }
      _endLabels = NULL;
    }
    
    ReadResult readToken(Parser::State& state, Parser::Arguments& argument);
    
    void CleanLogicLabels(Parser::Arguments& argument) {
      list l = _labels;
      while (l) {
        logic_label lab = (logic_label)l->element.container;
        if (lab->tag_logic_label == LOGICLABEL) {
          argument.removeLogicLabel(lab->cons_logic_label.LogicLabel.label);
        }
        if (lab->tag_logic_label == STMTLABEL) {
          argument.removeLogicLabel(lab->cons_logic_label.StmtLabel.code_label);
        }
        l = l->next;
      }
    }

    list extractLabels() {
      list result = _labels;
      _labels = _endLabels = NULL;
      return result;
    }

  };

  class Parameters : public ::Parser::Base::RuleResult {
  private:
    /* logic_arg_decl */ list _params, _endParams;
    location _loc;
  public:
    Parameters(location loc)
      : _params(NULL), _endParams(NULL), _loc(copy_loc(loc)) { }
    ~Parameters()
      { if(_loc) { free(_loc); _loc = NULL; }
        while (_params) {
          free_logic_arg_decl((logic_arg_decl) _params->element.container);
          list temp = _params->next;
          free(_params);
          _params = temp;
        };
        _endParams = NULL;
      }

    ReadResult readToken(Parser::State& state, Parser::Arguments& argument);
      
    list extractParams()
      { list result = _params;
        _params = _endParams = NULL;
        return result; 
      }
  };

public:
  GlobalAnnotation(location loc)
    : _annots(NULL), _globals(_annots), _loc(copy_loc(loc)), _typeVar(NULL),
      _term(NULL), _pred(NULL), _hasReads(false), _isMethod(false),
      _reads(), _params(NULL), _qualificationId(NULL), _polyIdLabels(NULL),
      _codeOperator(DLexer::OperatorPunctuatorToken::TUndefined),
      _typeName(NULL) {}
  ~GlobalAnnotation()
    { if (_loc) { free(_loc); _loc = NULL; };
      clear();
    }
  ReadResult readToken(Parser::State& state, Parser::Arguments& arguments);

  list getAnnot() const { return _annots; }
  void clear();
};

} // end of namespace Acsl

#endif // ACSL_GlobalAnnotationH

