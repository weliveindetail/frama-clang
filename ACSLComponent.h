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
//   Definition of the ACSL++ components.
//

#ifndef ACSL_ComponentH
#define ACSL_ComponentH

#include "ACSLParser.h"
// #include "DescentParse.h"

extern "C" {
#include "intermediate_format.h"
} // end of extern "C"

#include "ACSLLogicType.h"
#include "ACSLTermOrPredicate.h"
#include "ACSLLoopAnnotation.h"
#include "ACSLStatementAnnotation.h"
#include "ACSLGlobalAnnotation.h"
#include "ACSLCodeAnnotation.h"
#include "ACSLFunctionContract.h"

namespace Acsl {

/*! @class Locations
 *  @brief Component that parses a list of locations
 * Takes care of special case \nothing
 */
class Locations:
   public ::Parser::Base::RuleResult, public ::Parser::Base {
 private:
   ForwardList _locations;
   location _loc;
 public:
   ForwardList getResult() { return _locations; }
   Locations(location loc): _locations(), _loc(loc) { }
   ~Locations() { if(_loc) { free(_loc); _loc=NULL; } }
   ReadResult readToken(Parser::State& state, Parser::Arguments& arguments);
 };

/*! @class AssignsClause
 *  @brief Component that parses an assigns clause.
 *
 *  The state is defined by the Parser::State::point() method and has
 *    additional information within the fields _modified, _dependencies
 */
class AssignsClause : public ::Parser::Base::RuleResult, public ::Parser::Base {
private:
  ForwardList _clause;
  location _loc;
  ForwardList _modified;
  ForwardList _dependencies;
  bool _isNothingDependency;
public:
  ForwardList getResult() { return _clause; }
  AssignsClause(location loc)
    : _clause(), _loc(loc), _modified(), _dependencies(),
      _isNothingDependency(false) {}
 ~AssignsClause() { if (_loc) { free(_loc); _loc=NULL;} }
 ReadResult readToken(Parser::State& state, Parser::Arguments& arguments);
};

/*! @class AllocFreeClause
 *  @brief Component that parses an allocates or frees clause.
 *
 * An allocates or frees clause is simply a comma separated list of locations
 * (including \nothing). The only difference is that terms introduced by frees
 * are evaluated in the pre-state, while terms introduced by allocates are
 * evaluated in the post-state. This must be taken care of by the
 * callers of the clause.
 */
 class AllocFreeClause:
   public ::Parser::Base::RuleResult, public ::Parser::Base {
 private:
   ForwardList _clause;
   location _loc;
 public:
   ForwardList getResult() { return _clause; }
   AllocFreeClause(location loc): _clause(), _loc(loc) { }
   ~AllocFreeClause() { if(_loc) { free(_loc); _loc=NULL; } }
   ReadResult readToken(Parser::State& state, Parser::Arguments& arguments);
 };

} // end of namespace Acsl

#endif // ACSL_ComponentH

