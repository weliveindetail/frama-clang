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
//   Definition of the ACSL statement annotations.
//

#ifndef ACSL_StatementAnnotationH
#define ACSL_StatementAnnotationH

#include "ACSLParser.h"
// #include "DescentParse.h"

extern "C" {
#include "intermediate_format.h"
} // end of extern "C"

#include "ACSLLogicType.h"
#include "ACSLTermOrPredicate.h"

namespace Acsl {

class StatementAnnotation : public ::Parser::Base {
private:
  /* statement */ ForwardReferenceList& _codeContainer;
  code_annotation _annotResult;
  location _loc;
  location _subloc; // NULL if and only if _functionContractBehaviors is NULL
  /* string */ list _behaviors; 
  bool _hasUsedBehaviors;
  ForwardReferenceList _behaviorAdder;
  /* behavior */ list _functionContractBehaviors;
    // NULL if and only if _subloc is NULL
  ForwardReferenceList _functionContractBehaviorsAdder;
  void absorbLoc(location l) { if (_loc) free_location(l); _loc = l; }
 
public:
  StatementAnnotation(ForwardReferenceList& codeContainer)
    : _codeContainer(codeContainer), _annotResult(NULL), _loc(NULL),
      _subloc(NULL), _behaviors(NULL), _hasUsedBehaviors(false),
      _behaviorAdder(_behaviors), _functionContractBehaviors(NULL),
      _functionContractBehaviorsAdder(_functionContractBehaviors) {}
  ~StatementAnnotation()
    { clear();
      if (!_hasUsedBehaviors) {
        while (_behaviors) {
          free((char*) _behaviors->element.container);
          list temp = _behaviors;
          _behaviors = _behaviors->next;
          free(temp);
        };
      };
      if (_loc) { free_location(_loc); _loc = NULL; }
      if (_subloc) { free_location(_subloc); _subloc = NULL; }
    }
  ReadResult readToken(Parser::State& state, Parser::Arguments& arguments);

  void clear()
    { if (_functionContractBehaviors) {
        _codeContainer.insertContainer(statement_Code_annot(copy_loc(_loc),
            code_annotation_StmtSpec(_behaviors, function_contract_cons(
              _functionContractBehaviors, /* variant */ opt_none(),
              /* terminates */ opt_none(), /* complete_behaviors */ NULL,
              /* disjoint_behaviors */ NULL))));
        _functionContractBehaviors = NULL;
        _behaviors = NULL;
      };
      if (_annotResult) {
        free_code_annotation(_annotResult);
        _annotResult = NULL;
      };
    }
};

} // end of namespace Acsl

#endif // ACSL_StatementAnnotationH

