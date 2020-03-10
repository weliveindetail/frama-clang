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
//   Definition of the ACSL function contracts.
//

#ifndef ACSL_FunctionContractH
#define ACSL_FunctionContractH

#include "ACSLParser.h"
// #include "DescentParse.h"

extern "C" {
#include "intermediate_format.h"
} // end of extern "C"

#include "ACSLLogicType.h"
#include "ACSLTermOrPredicate.h"

namespace Acsl {

/*! @class FunctionContract
 *  @brief Component that parses a function contract.
 *
 *  The state is defined by the Parser::State::point() method and has
 *    additional information within the fields _state.
 */
class FunctionContract: public ::Parser::Base {
private:
  function_contract _spec;
  ForwardReferenceList _currentBehavior;
  ForwardReferenceList _currentRequires;
  ForwardReferenceList _currentAssumes;
  ForwardReferenceList _currentPostCond;
  ForwardList _currentAssigns;
  ForwardList _currentFrees;
  ForwardList _currentAllocates;
  ForwardReferenceList _complete;
  ForwardReferenceList _disjoint;
  ForwardReferenceList _currentSetOfBehaviors;
  termination_kind _postCondKind;
  enum { ALLOCATES, FREES } _allocClauseKind;
  bool _isStatementContract;
  enum { START, TERMINATES, BHV, ASSUMES, REQUIRES, POST_COND, 
         VARIANT, COMPLETE } _state;
  std::string _behaviorName;
  std::string _additionalMsg;

  ReadResult error_empty_behavior(Parser::Arguments& arguments);
  ReadResult check_bhv_position (Parser::Arguments& arguments);
  ReadResult check_terminates_position(Parser::Arguments& arguments);
  ReadResult check_assumes_position(Parser::Arguments& arguments);
  ReadResult check_requires_position(Parser::Arguments& arguments);
  ReadResult check_post_cond_position(Parser::Arguments& arguments);
  ReadResult check_variant_position(Parser::Arguments& arguments);
  ReadResult check_complete_position(Parser::Arguments& arguments);
  ReadResult parseSemiColumn(Parser::Arguments&, const std::string& );

  void add_behavior(const std::string&);

public:
  location _loc;

public:
  FunctionContract(location loc)
    : _spec(function_contract_cons(NULL,opt_none(),opt_none(),NULL,NULL)),
      _currentBehavior(_spec->behavior), _complete(_spec->complete_behaviors),
      _disjoint(_spec->disjoint_behaviors), _loc(loc)
    { _isStatementContract = false;
      _state = START;
    }

  ~FunctionContract() { if (_loc) { free(_loc); _loc=NULL; }; }

  void setStatementContract() { _isStatementContract = true; }

  ReadResult readToken(Parser::State& state, Parser::Arguments& arguments);
  function_contract getAnnot() const { return _spec; }

};

} // end of namespace Acsl

#endif // ACSL_FunctionContractH

