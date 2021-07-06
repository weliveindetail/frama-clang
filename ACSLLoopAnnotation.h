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
//   Definition of the ACSL loop annotations.
//

#ifndef ACSL_LoopAnnotationH
#define ACSL_LoopAnnotationH

#include "ACSLParser.h"
// #include "DescentParse.h"

extern "C" {
#include "intermediate_format.h"
} // end of extern "C"

#include "ACSLLogicType.h"
#include "ACSLTermOrPredicate.h"

namespace Acsl {

class LoopAnnotation : public ::Parser::Base {
private:
  /* statement */ ForwardList _annotationList;
  code_annotation _annotResult;
  /* string */ list _behaviors;
  bool _hasUsedBehaviors;
  ForwardReferenceList _behaviorAdder;
  location _loc;
  void absorbLoc(location l) { if(_loc) free_location(_loc); _loc = l; }
 
public:
  LoopAnnotation(location loc)
    : _annotResult(NULL), _behaviors(NULL), _hasUsedBehaviors(false),
      _behaviorAdder(_behaviors), _loc(loc)
    {}
  ~LoopAnnotation();
  ReadResult readToken(Parser::State& state, Parser::Arguments& arguments);
  /* statement */ list extractResult()
    { /* statement */ list result = _annotationList.getFront();
      _annotationList = ForwardList();
      return result;
    }
  void clear()
    { if (_annotResult) {
        free_code_annotation(_annotResult);
        _annotResult = NULL;
      };
    }
};

} // end of namespace Acsl

#endif // ACSL_LoopAnnotationH

