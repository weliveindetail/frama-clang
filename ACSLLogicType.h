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
//   Definition of the ACSL logic types.
//

#ifndef ACSL_LogicTypeH
#define ACSL_LogicTypeH

#include "ACSLParser.h"
// #include "DescentParse.h"
#include "Clang_utils.h"

extern "C" {
#include "intermediate_format.h"
} // end of extern "C"

namespace Acsl {

// true if v2 is compatible with v1, i.e. is a subtype of v1
// note that we don't use inheritance relation here to check for
// compatibility.
bool logic_type_compatible(
  logic_type v1, logic_type v2, Parser::Arguments& context);

bool equivalent_int_kind(ikind i1, ikind i2, Parser::Arguments& context);
bool compatible_int_kind(ikind i1, ikind i2, Parser::Arguments& context);
bool compatible_float_kind(fkind f1, fkind f2);
inline bool isFloating(typ source) { return source->tag_typ == FLOAT; }
bool is_type_synonym(logic_type_info info);
logic_type extract_synonym_def(logic_type_info info);

/*!
builds a logic type from a C/C++ type definition.
@param type must be the declaration of a C/C++ type name
*/
logic_type from_c_named_type(
  clang::NamedDecl const* type, const Clang_utils* utils);

/*! returns the type of the sets of elements of <base_type>.
  <base_type> is not duplicated. It must thus not be accessed directly
  by the caller afterwards.
 */
logic_type make_set_type(logic_type base_type);
/*! returns the type of elements of <set_type>, which must be a type of
    sets of elements.
*/
logic_type remove_set_type(logic_type set_type);

std::string str(logic_type typ);
//#define strlist(C) { list cc = C; stsd::ostringstream s; while (cc) s << str(((logic_arg_decl)cc->element.container)->la_type) << " "; cc = cc->next; }
std::string str(list typs);

/*! @class LogicType
 *  @brief Component that parses a logic_type with a state machine.
 *
 *  The state is defined by the Parser::State::point() method and has
 *    additional information within the fields _qualification, _declContext,
 *    _sumIdentifier. \n \n
 *  Depending on the constructor used, the local parsing method readToken
 *    builds a logic_type within the _typeResult field or a logic_type_def
 *    within the _typedefResult field. The constructor
 *    LogicType(qualified_name superTypeName) is used to build sum types
 *    and it is the one that produces the logic_type_def result.
 */
class LogicType : public ::Parser::Base::RuleResult, public ::Parser::Base {
private:
  qualified_name _superTypeName; //!< If defined, name of the sum type.
  logic_type _typeResult;
    //!< Expected result with a component defined by the default constructor.
  logic_type_def _typedefResult;
    //!< Expected result with a component built with LogicType(qualified_name).
  GlobalContext::NestedContext* _qualification; //!< Logic parsed qualification
  const clang::DeclContext* _declContext; //!< C++ parsed qualification
  bool _seenInt; //<! true when we have seen an explicit 'int' specifier
  bool _seenSigned; //<! true when we have seen an explicit 'signed' specifier
  bool _doesStopSuffix;
    //!< Does stop the parsing as son as a logic_type is parsed.
  location _loc; //!< Location of the type, used to extend the caller location.
  void absorbLoc(location l) { if (_loc) free_location(_loc); _loc = l; }
  std::string _sumIdentifier; //!< Identifier parsed after a '|' token.

  bool unspecifiedKind() {
    return
      !_seenInt && _typeResult &&
      _typeResult->tag_logic_type == LINT &&
      (_typeResult->cons_logic_type.Lint.kind == IINT ||
       _typeResult->cons_logic_type.Lint.kind == IUINT);
  }

public:
  LogicType()
    : _superTypeName(NULL), _typeResult(NULL), _typedefResult(NULL),
      _qualification(NULL), _declContext(NULL), _seenInt(false),
      _seenSigned(false), _doesStopSuffix(false),
      _loc(NULL) {}
  LogicType(qualified_name superTypeName)
    : _superTypeName(superTypeName), _typeResult(NULL), _typedefResult(NULL),
      _qualification(NULL), _declContext(NULL), _seenInt(false),
      _seenSigned(false), _doesStopSuffix(false),
      _loc(NULL) {}
  ~LogicType()
    { if (_typeResult) free_logic_type(_typeResult);
      if (_typedefResult) free_logic_type_def(_typedefResult);
      if (_loc) free_location(_loc);
    }

  ReadResult readToken(Parser::State& state, Parser::Arguments& argument);
  void setType(logic_type typeResult, location loc)
    { assert(!_typeResult && !_loc);
      _typeResult = typeResult;
      _loc = copy_loc(loc);
    }
  void setStopOnSuffix() { _doesStopSuffix = true; }
  location extractLocation()
    { location result = _loc; _loc = NULL; return result; }
  logic_type extractType()
    { assert(!_typedefResult);
      logic_type result = _typeResult;
      _typeResult = NULL;
      return result;
    }
  logic_type_def extractTypeDef()
    { logic_type_def result;
      if (_typedefResult) {
        result = _typedefResult;
        _typedefResult = NULL;
      }
      else {
        assert(_typeResult);
        result = logic_type_def_LTsyn(_typeResult);
        _typeResult = NULL;
      };
      return result;
    }
};

} // end of namespace Acsl

#endif // ACSL_LogicTypeH

