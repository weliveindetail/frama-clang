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
//   Implementation of ACSL++ tokens.
//

#include "ACSLToken.h"

namespace Acsl { namespace DLexer {

void
AbstractToken::_write(std::ostream& out, PersistentFormat& format) const {
  if (!format.isPretty()) {
    unsigned int params = queryParams();
    out.write((const char*) &params, sizeof(unsigned));
  }
  else {
    out << type_text();
  };
}

std::string AbstractToken::type_text() const {
  std::string t;
  switch (queryTypeField()) {
    case TUndefined: t = "undefined"; break;
    case TIdentifier: t = "identifier"; break;
    case TKeyword: t = "keyword"; break;
    case TLiteral: t = "string_literal"; break;
    case TOperatorPunctuator: t = "operator"; break;
    case TComment: t = "comment"; break;
    default: t = "?"; break;
  };
  return t;
}

std::string Token::type_text() const {
  std::string t;
  switch (_type) {
    case AbstractToken::TUndefined: t = "undefined"; break;
    case AbstractToken::TIdentifier: t = "identifier"; break;
    case AbstractToken::TKeyword: t = "keyword"; break;
    case AbstractToken::TLiteral: t = "string_literal"; break;
    case AbstractToken::TOperatorPunctuator: t = "operator"; break;
    case AbstractToken::TComment: t = "comment"; break;
    default: t = "?"; break;
  };
  return t;
}

std::string AbstractToken::text() const
  { // WIP: Needs improvement
    return "???";
  }

std::string AbstractToken::str() const
  { std::ostringstream out;
    this->_write(out,PersistentFormat().setPretty());
    return out.str();
  }

void
CommentToken::_write(std::ostream& out, PersistentFormat& format) const {
  inherited::_write(out, format);
  if (!format.isPretty()) {
    unsigned size = _content.length();
    out.write((const char*) &size, sizeof(unsigned));
    out.write(_content.c_str(), size);
  }
  else
    out << " -> " << _content;
}

void
IdentifierToken::_write(std::ostream& out, PersistentFormat& format) const {
  inherited::_write(out, format);
  if (!format.isPretty()) {
    unsigned size = _content.length();
    out.write((const char*) &size, sizeof(unsigned));
    out.write(_content.c_str(), size);
  }
  else
    out << " -> " << _content;
}

//!< Returns a pretty printed token: type and content
std::string Token::str() {
  if (getType() == AbstractToken::TIdentifier) {
    return getContent().str();
  } else {
    assumeContent(); // Changes the token
    std::string t = getFullToken().str();
    return getContent().str();
  }
}

//!< Returns just the source text for this token
std::string Token::text() const {
  if (hasContent()) {
    return getContent().text();
  } else  {
    return "???";
  }
}

std::pair<std::string, KeywordToken::Type>
KeywordToken::mapUnicode[] = {
    std::make_pair(utf8_convert(0x2124), TInteger),
    std::make_pair(utf8_convert(0x211D), TReal),
    std::make_pair(utf8_convert(0x1D539), TBoolean),
    std::make_pair(utf8_convert(0x2208), TSubset),
    std::make_pair(utf8_convert(0x2203), TExists),
    std::make_pair(utf8_convert(0x2200), TForall),

};

std::tr1::unordered_map<std::string, KeywordToken::Type>
KeywordToken::_unicodeKeywords(
    mapUnicode,
    mapUnicode + sizeof(mapUnicode) / sizeof(mapUnicode[0]));


OperatorPunctuatorToken::Connection
OperatorPunctuatorToken::mapUnicode[] = {
    std::make_pair(utf8_convert(0x22BB), TLogicalXor),
    std::make_pair(utf8_convert(0x00AC), TNot),
    std::make_pair(utf8_convert(0x2228), TLogicalOr),
    std::make_pair(utf8_convert(0x2227), TLogicalAnd),
    std::make_pair(utf8_convert(0x21D2), TImplies),
    std::make_pair(utf8_convert(0x21D4), TEquiv),
    std::make_pair(utf8_convert(0x2212), TMinus),
    std::make_pair(utf8_convert(0x2265), TGreaterOrEqual),
    std::make_pair(utf8_convert(0x2264), TLessOrEqual),
    std::make_pair(utf8_convert(0x2262), TDifferent),
    std::make_pair(utf8_convert(0x2261), TEqual),

};

OperatorPunctuatorToken::Map
OperatorPunctuatorToken::_unicodePunctuators(
    mapUnicode,
    mapUnicode + sizeof(mapUnicode) / sizeof(mapUnicode[0]));



std::pair<std::string, KeywordToken::Type>
KeywordToken::mapUnprotected[] = {
  std::make_pair("auto", TAuto),
  std::make_pair("bool", TBool),
  std::make_pair("case", TCase),
  std::make_pair("char", TChar),
  std::make_pair("char16_t", TChar16),
  std::make_pair("char32_t", TChar32),
  std::make_pair("class", TClass),
  std::make_pair("const", TConst),
  std::make_pair("const_cast", TConstCast),
  std::make_pair("double", TDouble),
  std::make_pair("dynamic_cast", TDynamicCast),
  std::make_pair("else", TElse),
  std::make_pair("enum", TEnum),
  std::make_pair("false", TFalse),
  std::make_pair("float", TFloat),
  std::make_pair("for", TFor),
  std::make_pair("ghost", TGhost),
  std::make_pair("global", TGlobal),
  std::make_pair("if", TIf),
  std::make_pair("int", TInt),
  std::make_pair("long", TLong),
  std::make_pair("loop", TLoop),
  std::make_pair("operator", TOperator),
  std::make_pair("reinterpret_cast", TReinterpretCast),
  std::make_pair("short", TShort),
  std::make_pair("signed", TSigned),
  std::make_pair("sizeof", TSizeof),
  std::make_pair("static", TStatic),
  std::make_pair("static_cast", TStaticCast),
  std::make_pair("struct", TStruct),
  std::make_pair("true", TTrue),
  std::make_pair("typeId", TTypeId),
  std::make_pair("typename", TTypename),
  std::make_pair("union", TUnion),
  std::make_pair("unsigned", TUnsigned),
  std::make_pair("virtual", TVirtual),
  std::make_pair("void", TVoid),
  std::make_pair("volatile", TVolatile),
  std::make_pair("wchar_t", TWcharT),
  std::make_pair("while", TWhile),
  std::make_pair("integer", TInteger),
  std::make_pair("invariant", TInvariant),
  std::make_pair("real", TReal),
  std::make_pair("boolean", TBoolean),
  std::make_pair("logic", TLogic),
  std::make_pair("predicate", TPredicate),
  std::make_pair("lemma", TLemma),
  std::make_pair("axiomatic", TAxiomatic),
  std::make_pair("axiom", TAxiom),
  std::make_pair("ensures", TEnsures),
  std::make_pair("assumes", TAssumes),
  std::make_pair("requires", TRequires),
  std::make_pair("terminates", TTerminates),
  std::make_pair("decreases", TDecreases),
  std::make_pair("assert", TAssert),
  std::make_pair("assigns", TAssigns),
  std::make_pair("reads", TReads),
  std::make_pair("writes", TWrites),
  std::make_pair("behavior", TBehavior),
  std::make_pair("complete", TComplete),
  std::make_pair("disjoint", TDisjoint),
  std::make_pair("behaviors", TBehaviors),
  std::make_pair("type", TType),
  std::make_pair("inductive", TInductive),
  std::make_pair("exits", TExits),
  std::make_pair("breaks", TBreaks),
  std::make_pair("continues", TContinues),
  std::make_pair("returns", TReturns),
  std::make_pair("variant", TVariant),
  std::make_pair("frees", TFrees),
  std::make_pair("allocates", TAllocates)
};

std::tr1::unordered_map<std::string, KeywordToken::Type>
KeywordToken::_unprotectedKeywords(
  mapUnprotected,
  mapUnprotected + sizeof(mapUnprotected) / sizeof(mapUnprotected[0]));

std::pair<std::string, KeywordToken::Type>
KeywordToken::mapProtected[] = {
  std::make_pair("forall", TForall),
  std::make_pair("exists", TExists),
  std::make_pair("true", TTrue),
  std::make_pair("false", TFalse),
  std::make_pair("let", TLet),
  std::make_pair("nothing", TNothing),
  std::make_pair("at", TAt),
  std::make_pair("old", TOld),
  std::make_pair("result", TResult),
  std::make_pair("match", TMatch),
  std::make_pair("lambda", TLambda),
  std::make_pair("sum", TSum),
  std::make_pair("product", TProduct),
  std::make_pair("length", TLength),
  std::make_pair("block_length", TBlockLength),
  std::make_pair("offset", TOffset),
  std::make_pair("t_iso", TTIso),
  std::make_pair("origin", TOrigin),
  std::make_pair("object", TObject),
  std::make_pair("null", TNull),
  std::make_pair("base_addr", TBaseAddr),
  std::make_pair("allocation", TAllocation),
  std::make_pair("allocable", TAllocable),
  std::make_pair("freeable", TFreeable),
  std::make_pair("fresh", TFresh),
  std::make_pair("separated", TSeparated),
  std::make_pair("frees", TFrees),
  std::make_pair("allocates", TAllocates),
  std::make_pair("allocation_status", TAllocationStatus),
  std::make_pair("static", TLStatic),
  std::make_pair("register", TLRegister),
  std::make_pair("automatic", TLAutomatic),
  std::make_pair("dynamic", TLDynamic),
  std::make_pair("unallocated", TLUnallocated),
  std::make_pair("initialized", TInitialized),
  std::make_pair("dangling", TDangling),
  std::make_pair("specified", TSpecified),
  std::make_pair("with", TWith),
  std::make_pair("num_of", TNumOf),
  std::make_pair("union", TLUnion),
  std::make_pair("inter", TLInter),
  std::make_pair("subset", TSubset),
  std::make_pair("empty", TEmpty),
  std::make_pair("valid", TValid),
  std::make_pair("valid_read", TValidRead),
  std::make_pair("valid_index", TValidIndex),
  std::make_pair("valid_range", TValidRange),
  std::make_pair("valid_function", TValidFunction),
  std::make_pair("set", TSet),
  std::make_pair("exit_status", TExitStatus),
  std::make_pair("from", TFrom),
  std::make_pair("weak", TWeak),
  std::make_pair("strong", TStrong),
  // \this is parsed as an identifier, not a keyword
  //  std::make_pair("up", TUp),
  //std::make_pair("down", TDown),
  //std::make_pair("nearest_away", TNearestAway),
  //std::make_pair("nearest_even", TNearestEven),
  //std::make_pair("round_float", TRoundFloat),
  //std::make_pair("round_double", TRoundDouble),
  //std::make_pair("is_finite", TIsFinite),
  //std::make_pair("is_NaN", TIsNaN),
  //std::make_pair("min", TMin),
  //std::make_pair("max", TMax),
  //std::make_pair("abs", TAbs),
  //std::make_pair("sqrt", TSqrt),
  //std::make_pair("pow", TPow),
  //std::make_pair("ceil", TCeil),
  //std::make_pair("floor", TFloor),
  //std::make_pair("exp", TExp),
  //std::make_pair("log", TLog),
  //std::make_pair("log10", TLog10),
  //std::make_pair("cos", TCos),
  //std::make_pair("sin", TSin),
  //std::make_pair("tan", TTan),
  //std::make_pair("cosh", TCosh),
  //std::make_pair("sinh", TSinh),
  //std::make_pair("tanh", TTanh),
  //std::make_pair("acos", TAcos),
  //std::make_pair("asin", TAsin),
  //std::make_pair("atan", TAtan),
  //std::make_pair("atan2", TAtan2),
  //std::make_pair("hypot", THypot),
  //std::make_pair("exact", TExact),
  //std::make_pair("round_error", TRoundError),
};

/* =
  { { "asm", TAsm },
    { "auto", TAuto },
    { "bool", TBool },
    { "break", TBreak },
    { "case", TCase },
    { "catch", TCatch },
    { "class", TClass },
    { "char", TChar },
    { "class", TClass },
    { "const", TConst },
    { "const_cast", TConstCast },
    { "continue", TContinue },
    { "default", TDefault },
    { "delete", TDelete },
    { "do", TDo },
    { "double", TDouble },
    { "dynamic_cast", TDynamicCast },
    { "else", TElse },
    { "enum", TEnum },
    { "explicit", TExplicit },
    { "export", TExport },
    { "extern", TExtern },
    { "false", TFalse },
    { "float", TFloat },
    { "for", TFor },
    { "friend", TFriend },
    { "global", TGlobal },
    { "goto", TGoto },
    { "if", TIf },
    { "inline", TInline },
    { "int", TInt },
    { "invariant", TInvariant },
    { "long", TLong },
    { "mutable", TMutable },
    { "namespace", TNamespace },
    { "new", TNew },
    { "operator", TOperator },
    { "private", TPrivate },
    { "protected", TProtected },
    { "public", TPublic },
    { "register", TRegister },
    { "reinterpret_cast", TReinterpretCast },
    { "return", TReturn },
    { "short", TShort },
    { "signed", TSigned },
    { "sizeof", TSizeof },
    { "static", TStatic },
    { "staticCast", TStaticCast },
    { "struct", TStruct },
    { "switch", TSwitch },
    { "template", TTemplate },
    { "throw", TThrow },
    { "true", TTrue },
    { "try", TTry },
    { "typedef", TTypedef },
    { "typeId", TTypeId },
    { "typename", TTypename },
    { "union", TUnion },
    { "unsigned", TUnsigned },
    { "using", TUsing },
    { "variant", TVariant },
    { "virtual", TVirtual },
    { "void", TVoid },
    { "volatile", TVolatile },
    { "wchar_t", TWcharT },
    { "while", TWhile },
    { "integer", TInteger },
    { "real", TReal },
    { "boolean", TBoolean },
    { "logic", TLogic },
    { "predicate", TPredicate },
    { "lemma", TLemma },
    { "axiom", TAxiom },
    { "axiomatic", TAxiomatic },
    { "ensures", TEnsures },
    { "assumes", TAssumes },
    { "requires", TRequires },
    { "terminates", TTerminates },
    { "decreases", TDecreases },
    { "assert", TAssert },
    { "assigns", TAssigns },
    { "reads", TReads },
    { "writes", TWrites },
    { "behavior", TBehavior },
    { "complete", TComplete },
    { "disjoint", TDisjoint },
    { "behaviors", TBehaviors },
    { "type", TType },
    { "inductive", TInductive },
    { "exists", TExists },
    { "breaks", TBreaks },
    { "continues", TContinues },
    { "returns", TReturns },
  };
*/

std::tr1::unordered_map<std::string, KeywordToken::Type>
KeywordToken::_protectedKeywords(
  mapProtected,
  mapProtected + sizeof(mapProtected) / sizeof(mapProtected[0]));

/*
std::tr1::unordered_map<std::string, KeywordToken::Type>
KeywordToken::_protectedKeywords =
  { { "forall", TForall },
    { "exists", TLExists },
    { "true", TTrue },
    { "false", TFalse },
    { "let", TLet },
    { "nothing", TNothing },
    { "at", TAt },
    { "old", TOld },
    { "result", TResult },
    { "match", TMatch },
    { "lambda", TLambda },
    { "sum", TSum },
    { "product", TProduct },
    { "length", TLength },
    { "block_length", TBlockLength },
    { "offset", TOffset },
    { "t_iso", TTIso },
    { "origin", TOrigin },
    { "object", TObject },
    { "null", TNull },
    { "baseAddr", TBaseAddr },
    { "allocation", TAllocation },
    { "allocable", TAllocable },
    { "freeable", TFreeable },
    { "fresh", TFresh },
    { "separated", TSeparated },
    { "frees", TFrees },
    { "allocates", TAllocates },
    { "allocation_status", TAllocationStatus },
    { "static", TLStatic },
    { "register", TLRegister },
    { "automatic", TLAutomatic },
    { "dynamic", TLDynamic },
    { "unallocated", TLUnallocated },
    { "initialized", TInitialized },
    { "specified", TSpecified },
    { "with", TWith },
    { "numOf", TNumOf },
    { "union", TLUnion },
    { "inter", TLInter },
    { "subset", TSubset },
    { "empty", TEmpty },
    { "valid", TValid },
    { "valid_read", TValidRead },
    { "valid_index", TValidIndex },
    { "valid_range", TValidRange },
    { "loop", TLoop },
    { "set", TSet },
    { "exitStatus", TExitStatus },
    { "from", TFrom },
    { "weak", TWeak },
    { "strong", TStrong },
    { "ghost", TGhost },
    { "up", TUp },
    { "down", TDown },
    { "nearest_away", TNearestAway },
    { "nearest_even", TNearestEven },
    { "round_float", TRoundFloat },
    { "round_double", TRoundDouble },
    { "is_finite", TIsFinite },
    { "is_NaN", TIsNaN },
    { "min", TMin },
    { "max", TMax },
    { "abs", TAbs },
    { "sqrt", TSqrt },
    { "pow", TPow },
    { "ceil", TCeil },
    { "floor", TFloor },
    { "exp", TExp },
    { "log", TLog },
    { "log10", TLog10 },
    { "cos", TCos },
    { "sin", TSin },
    { "tan", TTan },
    { "cosh", TCosh },
    { "sinh", TSinh },
    { "tanh", TTanh },
    { "acos", TAcos },
    { "asin", TAsin },
    { "atan", TAtan },
    { "atan2", TAtan2 },
    { "hypot", THypot },
    { "exact", TExact },
    { "round_error", TRoundError },
  };
*/

void
KeywordToken::_write(std::ostream& out, PersistentFormat& format) const {
  inherited::_write(out, format);
  if (format.isPretty()) {
    out << " -> " << text();
    };
}

std::string
KeywordToken::text() const {
  std::string t("<keyword?>");
    switch (queryOwnField()) { // FIXME - should not replicate the text here - keyword tokens should contain their own text
    case TAuto: t = "auto"; break;
    case TBool: t = "bool"; break;
    case TCase: t = "case"; break;
    case TChar: t = "char"; break;
    case TClass: t = "class"; break;
    case TConst: t = "const"; break;
    case TConstCast: t = "const_cast"; break;
    case TDouble: t = "double"; break;
    case TDynamicCast: t = "dynamic_cast"; break;
    case TElse: t = "else"; break;
    case TEnum: t = "enum"; break;
    case TFalse: t = "false"; break;
    case TFloat: t = "float"; break;
    case TFor: t = "for"; break;
    case TIf: t = "if"; break;
    case TInt: t = "int"; break;
    case TLong: t = "long"; break;
    case TOperator: t = "operator"; break;
    case TReinterpretCast: t = "reinterpret_cast"; break;
    case TShort: t = "short"; break;
    case TSigned: t = "signed"; break;
    case TSizeof: t = "sizeof"; break;
    case TStaticCast: t = "static_cast"; break;
    case TStruct: t = "struct"; break;
    case TTrue: t = "true"; break;
    case TTypeId: t = "typeid"; break;
    case TTypename: t = "typename"; break;
    case TUnion: t = "union"; break;
    case TUnsigned: t = "unsigned"; break;
    case TVirtual: t = "virtual"; break;
    case TVoid: t = "void"; break;
    case TVolatile: t = "volatile"; break;
    case TWcharT: t = "wchar_t"; break;
    case TWhile: t = "while"; break;

    case TForall: t = "\\forall"; break;
    case TExists: t = "\\exists"; break;
    case TInteger: t = "integer"; break;
    case TReal: t = "real"; break;
    case TBoolean: t = "boolean"; break;
    case TLTrue: t = "\\true"; break;
    case TLFalse: t = "\\false"; break;
    case TLet: t = "\\let"; break;
    case TLogic: t = "logic"; break;
    case TPredicate: t = "predicate"; break;
    case TLemma: t = "lemma"; break;
    case TAxiomatic: t = "axiomatic"; break;
    case TAxiom: t = "axiom"; break;
    case TEnsures: t = "ensures"; break;
    case TAssumes: t = "assumes"; break;
    case TRequires: t = "requires"; break;
    case TTerminates: t = "terminates"; break;
    case TDecreases: t = "decreases"; break;
    case TAssert: t = "assert"; break;
    case TAssigns: t = "assigns"; break;
    case TReads: t = "reads"; break;
    case TWrites: t = "writes"; break;
    case TNothing: t = "\\nothing"; break;
    case TBehavior: t = "behavior"; break;
    case TComplete: t = "complete"; break;
    case TDisjoint: t = "disjoint"; break;
    case TBehaviors: t = "behaviors"; break;
    case TAt: t = "\\at"; break;
    case TOld: t = "\\old"; break;
    case TResult: t = "\\result"; break;
    case TType: t = "type"; break;
    case TMatch: t = "\\match"; break;
    case TLambda: t = "\\lambda"; break;
    case TSum: t = "\\sum"; break;
    case TProduct: t = "\\product"; break;
    case TLength: t = "\\length"; break;
    case TBlockLength: t = "\\block_length"; break;
    case TOffset: t = "\\offset"; break;
    case TTIso: t = "\\t_iso"; break;
    case TOrigin: t = "\\origin"; break;
    case TObject: t = "\\object"; break;
    case TNull: t = "\\null"; break;
    case TBaseAddr: t = "\\base_addr"; break;
    case TAllocation: t = "\\allocation"; break;
    case TAllocable: t = "\\allocable"; break;
    case TFreeable: t = "\\freeable"; break;
    case TFresh: t = "\\fresh"; break;
    case TSeparated: t = "\\separated"; break;
    case TFrees: t = "frees"; break;
    case TAllocates: t = "allocates"; break;
    case TAllocationStatus: t = "\\allocation_status"; break;
    case TLStatic: t = "\\static"; break;
    case TLRegister: t = "\\register"; break;
    case TLAutomatic: t = "\\automatic"; break;
    case TLDynamic: t = "\\dynamic"; break;
    case TLUnallocated: t = "\\unallocated"; break;
    case TInitialized: t = "\\initialized"; break;
    case TDangling: t = "\\dangling"; break;
    case TSpecified: t = "\\specified"; break;
    case TWith: t = "\\with"; break;
    case TNumOf: t = "\\numof"; break;
    case TLUnion: t = "\\union"; break;
    case TLInter: t = "\\inter"; break;
    case TSubset: t = "\\subset"; break;
    case TEmpty: t = "\\empty"; break;
    case TValid: t = "\\valid"; break;
    case TValidRead: t = "\\valid_read"; break;
    case TValidIndex: t = "\\valid_index"; break;
    case TValidRange: t = "\\valid_range"; break;
    case TValidFunction: t = "\\valid_function"; break;
    case TInductive: t = "inductive"; break;
    case TLoop: t = "loop"; break;
    case TVariant: t = "variant"; break;
    case TInvariant: t = "invariant"; break;
    case TSet: t = "\\set"; break;
    case TExits: t = "exits"; break;
    case TBreaks: t = "breaks"; break;
    case TContinues: t = "continues"; break;
    case TReturns: t = "returns"; break;
    case TExitStatus: t = "\\exit_status"; break;
    case TFrom: t = "\\from"; break;
    case TGlobal: t = "global"; break;
    case TWeak: t = "\\weak"; break;
    case TStrong: t = "\\strong"; break;
    case TGhost: t = "ghost"; break;
      //      case TUp: t = "\\Up"; break;
      //      case TDown: t = "\\Down"; break;
      //      case TNearestAway: t = "\\NearestAway"; break;
      //      case TNearestEven: t = "\\NearestEven"; break;
      //      case TRoundFloat: t = "\\round_float"; break;
      //      case TRoundDouble: t = "\\round_double"; break;
      //      case TIsFinite: t = "\\is_finite"; break;
      //      case TIsNaN: t = "\\is_NaN"; break;
      //      case TMin: t = "\\min"; break;
      //      case TMax: t = "\\max"; break;
      //      case TAbs: t = "\\abs"; break;
      //      case TSqrt: t = "\\sqrt"; break;
      //      case TPow: t = "\\pow"; break;
      //      case TCeil: t = "\\ceil"; break;
      //      case TFloor: t = "\\floor"; break;
      //      case TExp: t = "\\exp"; break;
      //      case TLog: t = "\\log"; break;
      //      case TLog10: t = "\\log10"; break;
      //      case TCos: t = "\\cos"; break;
      //      case TSin: t = "\\sin"; break;
      //      case TTan: t = "\\tan"; break;
      //      case TCosh: t = "\\cosh"; break;
      //      case TSinh: t = "\\sinh"; break;
      //      case TTanh: t = "\\tanh"; break;
      //      case TAcos: t = "\\acos"; break;
      //      case TAsin: t = "\\asin"; break;
      //      case TAtan: t = "\\atan"; break;
      //      case TAtan2: t = "\\atan2"; break;
      //      case THypot: t = "\\hypot"; break;
      //      case TExact: t = "\\exact"; break;
      //      case TRoundError: t = "\\round_error"; break;
  }
  return t;
}

void
LiteralToken::_write(std::ostream& out, PersistentFormat& format) const {
  inherited::_write(out, format);
  if (format.isPretty()) {
    out << " -> ";
    switch (queryOwnField()) {
      case TInteger: out << "int"; break;
      case TCharacter: out << "char"; break;
      case TFloating: out << "double"; break;
      case TString: out << "string"; break;
    };
  };
}

void
IntegerLiteralToken::_write(std::ostream& out, PersistentFormat& format) const {
  inherited::_write(out, format);
  if (!format.isPretty()) { out << _value; }
  else out << " -> " << _value;
}

void
CharacterLiteralToken::_write(std::ostream& out, PersistentFormat& format)
    const {
  inherited::_write(out, format);
  switch (queryOwnField()) {
    case TChar:
      { if (!format.isPretty())
          out.put(_value.ch);
        else
          out << " -> " << _value.ch;
      };
      break;
    case TWideChar:
      { if (!format.isPretty())
          out.write((const char*) &_value.wch, sizeof(wchar_t));
        else
          out << " -> " << _value.wch;
      };
      break;
  };
}

void
FloatingLiteralToken::_write(std::ostream& out, PersistentFormat& format) const
{ inherited::_write(out, format);
  if (!format.isPretty()) out << _real;
  else out << " -> " << _real;
}

void
StringLiteralToken::_write(std::ostream& out, PersistentFormat& format) const {
  inherited::_write(out, format);
  if (!format.isPretty()) {
    unsigned size = _content.length();
    out.write((const char*) &size, sizeof(unsigned));
    out.write(_content.c_str(), size);
  }
  else
    out << " -> " << _content;
}

std::string
OperatorPunctuatorToken::text() const {
  std::string t("<??unknown>");
  switch (queryOwnField()) {
    case TOpenBrace: t = '{'; break;
    case TCloseBrace: t = '}'; break;
    case TOpenBracket: t = '['; break;
    case TCloseBracket: t = ']'; break;
    case TOpenParen: t = '('; break;
    case TCloseParen: t = ')'; break;
    case TSemiColon: t = ';'; break;
    case TColon: t = ':'; break;
    case TEllipsis: t = "..."; break;
    case TQuery: t = '?'; break;
    case TColonColon: t = "::"; break;
    case TPunct: t = '.'; break;
    case TPunctStar: t = ".*"; break;
    case TPlus: t = '+'; break;
    case TMinus: t = '-'; break;
    case TStar: t = '*'; break;
    case TDivide: t = '/'; break;
    case TProcent: t = '%'; break;
    case TBitXor: t = '^'; break;
    case TAmpersand: t = '&'; break;
    case TBitOr: t = '|'; break;
    case TTilda: t = '~'; break;
    case TNot: t = '!'; break;
    case TAssign: t = '='; break;
    case TLess: t = '<'; break;
    case TGreater: t = '>'; break;
    case TPlusAssign: t = "+="; break;
    case TMinusAssign: t = "-="; break;
    case TMultAssign: t = "*="; break;
    case TDivideAssign: t = "/="; break;
    case TModuloAssign: t = "%="; break;
    case TBitXorAssign: t = "^="; break;
    case TBitAndAssign: t = "&="; break;
    case TBitOrAssign: t = "|="; break;
    case TLeftShift: t = "<<"; break;
    case TRightShift: t = ">>"; break;
    case TLeftShiftAssign: t = "<<="; break;
    case TRightShiftAssign: t = ">>="; break;
    case TEqual: t = "=="; break;
    case TDifferent: t = "!="; break;
    case TLessOrEqual: t = "<="; break;
    case TGreaterOrEqual: t = ">="; break;
    case TLogicalAnd: t = "&&"; break;
    case TLogicalOr: t = "||"; break;
    case TPlusPlus: t = "++"; break;
    case TMinusMinus: t = "--"; break;
    case TComma: t = ','; break;
    case THash: t = '#'; break;
    case TArrowStar: t = "->*"; break;
    case TArrow: t = "->"; break;
    case TImplies: t = "==>"; break;
    case TEquiv: t = "<==>"; break;
    case TLogicalXor: t = "^^"; break;
    case TBitImplies: t = "-->"; break;
    case TBitEquiv: t = "<-->"; break;
    case TColonGT: t = ":>"; break;
    case TLTColon: t = "<:"; break;
    case TRange: t = ".."; break;
  };
  return t;
}

void
OperatorPunctuatorToken::writeSign(std::ostream& out) const {
  out << text();
}

void
OperatorPunctuatorToken::_write(std::ostream& out, PersistentFormat& format)
    const {
  inherited::_write(out, format);
  if (format.isPretty()) {
    out << " -> " << text();
  };
}

void
Token::assumeContent()
{ assert(_type != 0);
  if (!_content.get()) {
    AbstractToken basic(_type);
    basic.clearFullField();
    switch (basic.getType()) {
      case AbstractToken::TKeyword:
        _content.reset(new KeywordToken((const KeywordToken&) basic));
        break;
      case AbstractToken::TOperatorPunctuator:
        _content.reset(new OperatorPunctuatorToken(
              (const OperatorPunctuatorToken&) basic));
        break;
      default:
        _content.reset(new AbstractToken(basic));
    };
  };
}

std::string AbstractToken::utf8_convert(unsigned c) {
  if (c<0x80) { return std::string(1,c); }
  unsigned length = 0;
  unsigned i = c>>1;
  while (i!=0) { length++; i>>=5; }
  char first = (((1 << length) -1) << (8-length)) | (c>>(6*(length-1)));
  std::string res(length,first);
  for (i=1; i<length; i++) res[i] = (((c>>((length - 1 -i)*6)) & 0x3f) | 0x80);
  return res;
}



}} // end of namespace Acsl::DLexer

