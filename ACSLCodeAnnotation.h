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
//   Definition of the ACSL code annotations, like an assert.
//

#ifndef ACSL_CodeAnnotationH
#define ACSL_CodeAnnotationH

#include "ACSLParser.h"
// #include "DescentParse.h"

extern "C" {
#include "intermediate_format.h"
} // end of extern "C"

#include "ACSLLogicType.h"
#include "ACSLTermOrPredicate.h"

namespace Acsl {

/*! @class CodeAnnotation
 *  @brief Component that parses an annotation in the code, like an assert.
 *
 *  The state is defined by the Parser::State::point() method and with
 *    the _behaviors field.
 */
class CodeAnnotation : public ::Parser::Base {
private:
  code_annotation _annotResult;
  /* string */ list _behaviors;
  ForwardReferenceList _behaviorAdder;
  location _loc;
 
public:
  CodeAnnotation(location loc)
    : _annotResult(NULL), _behaviors(NULL), _behaviorAdder(_behaviors),
      _loc(loc) {}
  ~CodeAnnotation() { if (_loc) { free_location(_loc); _loc = NULL; } }
  ReadResult readToken(Parser::State& state, Parser::Arguments& arguments);

  code_annotation extractAnnot()
    { code_annotation result = _annotResult;
      _annotResult = NULL;
      return result;
    }
  location extractLocation()
    { location result = _loc; _loc = NULL; return result; }
};

} // end of namespace Acsl

#endif // ACSL_CodeAnnotationH

