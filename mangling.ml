(**************************************************************************)
(*                                                                        *)
(*  This file is part of Frama-Clang                                      *)
(*                                                                        *)
(*  Copyright (C) 2012-2021                                               *)
(*    CEA (Commissariat à l'énergie atomique et aux énergies              *)
(*         alternatives)                                                  *)
(*                                                                        *)
(*  you can redistribute it and/or modify it under the terms of the GNU   *)
(*  Lesser General Public License as published by the Free Software       *)
(*  Foundation, version 2.1.                                              *)
(*                                                                        *)
(*  It is distributed in the hope that it will be useful,                 *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the         *)
(*  GNU Lesser General Public License for more details.                   *)
(*                                                                        *)
(*  See the GNU Lesser General Public License version 2.1                 *)
(*  for more details (enclosed in the file LICENSE).                      *)
(*                                                                        *)
(**************************************************************************)

(* see http://refspecs.linuxfoundation.org/cxxabi-1.86.html#mangling *)

open Intermediate_format

let is_main_name qname = qname.decl_name = "main"

let _is_main_args = function
    [ { plain_type = Void } ]
  | { plain_type = Int IInt } ::
      { plain_type =
          Array
            { subtype =
                { plain_type = 
                    Pointer
                      (PDataPointer
                         { plain_type = 
                             Int (IChar | IChar_s | IChar_u) }) }}} :: _
    -> true
  | _ -> false

(* Mangling ABI imposes that only a main function with appropriate signature
   is kept unmangled. We relax it a bit in order to easily define main wrappers
   for use in analysis.
 *)
let is_main_func name args =
  match args with
    | None -> is_main_name name
    | Some (_,_s) -> is_main_name name (* && is_main_args s.parameter *)

let prefix = "_Z"

let qual_prefix = "N"

let qual_suffix = "E"

let mangle_int i =
  if Int64.compare i Int64.zero < 0 then "n" ^ Int64.to_string (Int64.neg i)
  else Int64.to_string i

let add_cv_qual cv =
  let s1 = if List.mem Volatile cv then "V" else "" in
  let s2 = if List.mem Const cv then "K" else "" in
  s1 ^ s2

let mangle_op_name = function
  | "new" -> "nw"
  | "new[]" -> "na"
  | "delete" -> "dl"
  | "delete[]" -> "da"
  | "+(unary)" -> "ps"
  | "-(unary)" -> "ng"
  | "&(unary)" -> "ad"
  | "*(unary)" -> "de"
  | "~" -> "co"
  | "+" -> "pl"
  | "-" -> "mi"
  | "*" -> "ml"
  | "/" -> "dv"
  | "%" -> "rm"
  | "&" -> "an"
  | "|" -> "or"
  | "^" -> "eo"
  | "=" -> "aS"
  | "+=" -> "pL"
  | "-=" -> "mI"
  | "*=" -> "mL"
  | "/=" -> "dV"
  | "%=" -> "rM"
  | "&=" -> "aN"
  | "|=" -> "oR"
  | "^=" -> "eO"
  | "<<" -> "ls"
  | ">>" -> "rs"
  | "<<=" -> "lS"
  | ">>=" -> "rS"
  | "==" -> "eq"
  | "!=" -> "ne"
  | "<" -> "lt"
  | ">" -> "gt"
  | "<=" -> "le"
  | ">=" -> "ge"
  | "!" -> "nt"
  | "&&" -> "aa"
  | "||" -> "oo"
  | "++" -> "pp"
  | "--" -> "mm"
  | "," -> "cm"
  | "->*" -> "pm"
  | "->" -> "pt"
  | "()" -> "cl"
  | "[]" -> "ix"
  | "?" -> "qu"
  | "sizeof-type" -> "st"
  | "sizeof-expr" -> "sz"
  | s -> Printf.sprintf "v9%d%s" (String.length s) s

let is_builtin_name s =
  let prefix = "__builtin_" in
  let prelen = String.length prefix in
  String.length s > prelen &&
    String.sub s 0 (String.length prefix) = prefix

let is_builtin_qname n = is_builtin_name n.decl_name

let mangle_plain_var s =
  let l = String.length s in
    if l = 0 then "0" (* should rarely occur *)
    else if s.[0] = '~' then "D1" (*should be more specific in certain cases*)
    else if s = "constructor-special" then "C1" (* id. *)
    else if Str.string_match (Str.regexp "operator *\\(.*\\)") s 0 then
      mangle_op_name (Str.matched_group 1 s)
    else Printf.sprintf "%d%s" l s

let mangle_ikind = function
  | IChar | IChar_s | IChar_u -> "c"
  | IUChar -> "h"
  | ISChar -> "a"
  | IChar16 -> "Ds"
  | IChar32 -> "Di"
  | IBool -> "b"
  | IInt -> "i"
  | IUInt -> "j"
  | ILong -> "l"
  | IULong -> "m"
  | ILongLong -> "x"
  | IULongLong -> "y"
  (* not translated yet 
    | ST_LONG_LONG -> "x"
     | ST_UNSIGNED_LONG_LONG -> "y" *)
  | IShort -> "s"
  | IUShort -> "t"
  | IWChar | IWChar_s | IWChar_u -> "w"
  | IWUChar -> "u6WUChar"
  | IWSChar -> "u6WSChar"

let mangle_fkind = function
  | FFloat -> "f"
  | FDouble -> "d"
  | FLongDouble -> "e"
(* Not translated yet
  | ST_FLOAT_COMPLEX -> "Cf"
  | ST_DOUBLE_COMPLEX -> "Cd"
  | ST_LONG_DOUBLE_COMPLEX -> "Ce"
  | ST_FLOAT_IMAGINARY -> "Gf"
  | ST_DOUBLE_IMAGINARY -> "Gd"
  | ST_LONG_DOUBLE_IMAGINARY -> "Ge"
*)

(* Not translated yet
  | ST_ELLIPSIS -> "z"
  | ST_CDTOR -> ""
  | ST_INTEGER -> "u7integer"
  | ST_REAL -> "u4real"
  | _ -> "u3baz"
*)

(* NB: this supposes that the float representation is in hexadecimal form. *)
let mangle_float v = v

let rec mangle_cc_type = function
  | Void -> "v"
  | Int ik -> mangle_ikind ik
  | Enum e -> mangle_name_optt e.body TStandard
  | Float fk -> mangle_fkind fk
  | Pointer t -> mangle_pkind "P" t
  | LVReference t -> mangle_pkind "R" t
  | RVReference t -> mangle_pkind "O" t
  (* Not translated yet 
  | FunctionType ((_,rt,args)) ->
      mangle_cc_type rt ^ "F" ^
        (String.concat "" (List.map mangle_cc_type args)) ^ "E" *)
  | Array t ->
     let dim = match t.dimension with
       | Some { econtent=Constant (IntCst (_,_,i)); _ } -> Int64.to_string i
       | Some _ -> "<expr>"
       | None -> ""
     in
     "A" ^ dim ^ "_" ^ mangle_cc_qual_type t.subtype
  | Struct (name, tc) -> mangle_name_optt name tc
  | Union (name,tc) -> mangle_name_optt name tc
  | Named (name,is_extern_c_name) ->
    if is_extern_c_name then name.decl_name
    else mangle_name_optt name TStandard
  | Lambda (protos,cap) ->
    (* NB: we depart from standard mangling rules here, in order to have
       a contextless mangling, whereas Itanium ABI mangles according to
       the number of lambda classes found in each function. *)
    let proto = (match protos with
      | p :: _ -> p
      | [] -> Frama_Clang_option.not_yet_implemented
          "Initializer list without Compound initialization") in
    "Ul" ^ mangle_parameter proto.parameter ^ "EUc" ^ mangle_captures cap ^ "E_"
  (* not translated yet
     | ArrayType(t,(DYN_SIZE | NO_SIZE)) ->
      "A_" ^ mangle_cc_type t *)
(* Not translated yet
  | PointerToMemberType (t,cv,mt) ->
      "M" ^ mangle_cc_atomic_type t ^ add_cv_qual cv ^ mangle_cc_type mt
*)
and mangle_pkind kw = function
  | PDataPointer t -> kw ^ mangle_cc_qual_type t
  | PFunctionPointer s ->
      kw ^ mangle_cc_qual_type s.result ^ "F"
      ^ mangle_parameter s.parameter ^ "E"
  | PStandardMethodPointer _ ->
      Frama_Clang_option.not_yet_implemented "Mangling of pointer to member"
  | PVirtualMethodPointer _ ->
      Frama_Clang_option.not_yet_implemented "Mangling of pointer to member"

and mangle_parameter l = String.concat "" (List.map mangle_cc_qual_type l)

and mangle_captures l = String.concat "" (List.map mangle_capture l)

and mangle_capture = function
  | Cap_id (s,typ,is_ref) ->
    mangle_plain_var s ^ (if is_ref then "R" else "") ^ mangle_cc_qual_type typ
  | Cap_this is_ref -> "4this" ^ (if is_ref then "R" else "") ^ "v"
    (* TODO: better reprensentation for this, but this will probably prevent
       any context-free mangling. *)

and mangle_cc_qual_type t =
  add_cv_qual t.qualifier ^ mangle_cc_type t.plain_type

and mangle_template_arg = function
  | TPStructOrClass name -> mangle_name name
  | TPTypename typ -> mangle_cc_qual_type typ
  | TPConstant (IntCst (k,_,v)) ->
      "L" ^ mangle_ikind k ^ mangle_int v ^ "E"
  | TPConstant (EnumCst(_,e,v)) ->
    "L" ^ mangle_name e.body ^ mangle_int v ^ "E"
  | TPConstant(TypeCst(TCCSizeOf,typ)) ->
    "st" ^ mangle_cc_type typ
  | TPConstant(TypeCst(TCCAlignOf,typ)) ->
    "v13aot" ^ mangle_cc_type typ
  | TPConstant(FloatCst(k,v)) ->
      "L" ^ mangle_fkind k ^ mangle_float v ^ "E"
  | TPDeclaration name -> mangle_name_optt name TStandard
(* not translated yet 
and encode_overload_op = function
  |  OP_NOT -> "nt"
  |  OP_BITNOT -> "co"
  |  OP_PLUSPLUS -> "pp"
  |  OP_MINUSMINUS -> "mm"
  |  OP_PLUS -> "pl"
  |  OP_MINUS -> "mi"
  |  OP_STAR -> "ml"
  |  OP_AMPERSAND -> "an"
  |  OP_DIV -> "dv"
  |  OP_MOD -> "rm"
  |  OP_LSHIFT -> "ls"
  |  OP_RSHIFT -> "rs"
  |  OP_BITXOR -> "eo"
  |  OP_BITOR  -> "or"
  |  OP_ASSIGN -> "aS"
  |  OP_PLUSEQ -> "pL"
  |  OP_MINUSEQ -> "mI"
  |  OP_MULTEQ  -> "mL"
  |  OP_DIVEQ   -> "dV"
  |  OP_MODEQ   -> "rM"
  |  OP_LSHIFTEQ -> "lS"
  |  OP_RSHIFTEQ -> "rS"
  |  OP_BITANDEQ -> "aN"
  |  OP_BITXOREQ -> "eO"
  |  OP_BITOREQ  -> "oR"
  |  OP_EQUAL    -> "eq"
  |  OP_NOTEQUAL -> "ne"
  |  OP_LESS     -> "lt"
  |  OP_GREATER  -> "gt"
  |  OP_LESSEQ   -> "le"
  |  OP_GREATEREQ-> "ge"
  |  OP_AND      -> "aa"
  |  OP_OR       -> "oo"
  |  OP_ARROW    -> "pt"
  |  OP_ARROW_STAR -> "pm"
  |  OP_BRACKETS   -> "ix"
  |  OP_PARENS     -> "cl"
  |  OP_COMMA      -> "cm"
  |  OP_QUESTION   -> "qu"
  |  OP_MINIMUM    -> "v03min"
  |  OP_MAXIMUM    -> "v13max"
  |  OP_MINIMUMEQ  -> "v23miN"
  |  OP_MAXIMUMEQ  -> "v33maX"

and encode_operator = function
    ON_newDel (false,false) -> "dl"
  | ON_newDel (false,true)  -> "da"
  | ON_newDel (true,false)  -> "nw"
  | ON_newDel (true,true)   -> "na"
  | ON_operator op          -> encode_overload_op op
  | ON_conversion typ       -> "cv" ^ mangle_arg typ
*)
(*NB: mangling of ctors and dtors is not correct wrt IA-64 spec. *)
and mangle_qualifier = function
  | QNamespace name -> string_of_int (String.length name) ^ name
  | QStructOrClass name -> string_of_int (String.length name) ^ name
  | QTemplateInstance(name,args) ->
      string_of_int (String.length name) ^ name ^ "I" ^
        (String.concat "" (List.map mangle_template_arg args)) ^ "E"

(* not translated yet 
    PQ_variable (_,var) ->
      mangle_plain_var var.v_name
  | PQ_qualifier (_,None,_,name,_) -> mangle_qualified_name name
  | PQ_qualifier (_,Some qual,args,PQ_name (_,name),_) when qual = name ->
      let l = String.length qual in
      let args = List.map mangle_template_arg args in
      let args = String.concat "" args in
      let args = if args = "" then args else "I" ^ args ^ "E" in
        Printf.sprintf "%d%s%sC1" l qual args
  | PQ_qualifier (_,Some qual,args,PQ_name (_,name),_)
      when "~" ^ qual = name ->
      let l = String.length qual in
      let args = List.map mangle_template_arg args in
      let args = String.concat "" args in
      let args = if args = "" then args else "I" ^ args ^ "E" in
        Printf.sprintf "%d%s%sD1" l qual args
  | PQ_qualifier (_,Some qual, [],name,_) ->
      let l = String.length qual in
      let name = mangle_qualified_name name in
        Printf.sprintf "%d%s%s" l qual name
  | PQ_qualifier (_,Some qual,args,name,_) ->
      let l = String.length qual in
      let args = List.map mangle_template_arg args in
      let args = String.concat "" args in
      let name = mangle_qualified_name name in
        Printf.sprintf "%d%sI%sE%s" l qual args name
  | PQ_name (_,name) ->
      mangle_plain_var name
  | PQ_operator (_,op,_) -> encode_operator op
  | PQ_template (_,qual,args) ->
      let l = String.length qual in
      let args = List.map mangle_template_arg args in
      let args = String.concat "" args in
        Printf.sprintf "%d%sI%sE" l qual args
*)

and mangle_qualification ?cv name =
  let qualifier =
    List.fold_left (fun acc n -> acc ^ mangle_qualifier n) "" 
      name.prequalification
  in
  match qualifier, cv with
    | "", None -> qualifier
    | s, None -> qual_prefix ^ s ^ qual_suffix
    | _, Some cv ->
      qual_prefix ^ (add_cv_qual cv) ^ qualifier ^ qual_suffix

and mangle_name name =
  let qualifier = mangle_qualification name in
  qualifier ^ (mangle_plain_var name.decl_name)

and mangle_template_instance =
  function
  | TStandard -> ""
    | TTemplateInstance targs ->
    "I" ^ String.concat "" (List.map mangle_template_arg targs) ^ "E"

and mangle_name_optt name template_instance =
  mangle_name name ^ mangle_template_instance template_instance

let mangle_name_kind kind name template_instance =
  match kind with
    | FKFunction -> mangle_name_optt name template_instance
    | FKMethod cv ->
      mangle_qualification ~cv name ^
      mangle_plain_var name.decl_name ^
      mangle_template_instance template_instance
    | FKCastMethodOperator (cv, ct) ->
      mangle_qualification ~cv name ^ "cv"  ^ mangle_cc_qual_type ct
    | FKConstructor true -> mangle_qualification name ^ "C1"
    | FKConstructor false -> mangle_qualification name ^ "C2"
    | FKDestructor true -> mangle_qualification name ^ "D1"
    | FKDestructor false -> mangle_qualification name ^ "D2"

let is_template_member prequalification =
  List.exists 
    (function
      | QNamespace _ | QStructOrClass _ -> false | QTemplateInstance _ -> true)
    prequalification

let mangle name template_instance_params signature =
  if is_main_func name signature then "main"
  else if is_builtin_qname name then name.decl_name
  else begin
    match signature with
    | None -> prefix ^ (mangle_name_optt name template_instance_params)
        | Some (kind,s) ->
      let mangled =
        prefix ^ mangle_name_kind kind name template_instance_params
      in
          let mangled =
            if is_template_member name.prequalification then
              mangled ^ (mangle_cc_qual_type s.result)
            else mangled
          in
          List.fold_left
            (fun s arg -> s ^ (mangle_cc_qual_type arg)) mangled s.parameter
  end

let dkey = Frama_Clang_option.register_category "mangling:entry-point"

let has_prefix s = String.length s > 2 && s.[0] = '_' && s.[1] = 'Z'

let is_mangling_prefix prefix name =
  let l = String.length prefix in
  if String.length name < l then false
  else prefix = (String.sub name 0 l)
    

let mangle_cmdline_name s =
  try
    let (name, proto) = Cxx_utils.analyse_entrypoint s in
    Frama_Clang_option.debug ~dkey "parameter string: %s" s;
    Frama_Clang_option.debug ~dkey "qualified name  : %a"
      Fclang_datatype.Qualified_name.pretty (name, TStandard);
    match proto with
      | None ->
        let prefix = mangle name TStandard None in
        Frama_Clang_option.debug ~dkey "mangling prefix is %s" prefix;
        let should_add kf acc =
          let name = Kernel_function.get_name kf in
          if is_mangling_prefix prefix name then
            Kernel_function.Set.add kf acc
          else begin
            Frama_Clang_option.debug
              ~dkey "%s is not a prefix of %s" prefix name;
            acc
          end
        in
        if has_prefix prefix then
          Globals.Functions.fold should_add Kernel_function.Set.empty
        else (* Function has not been mangled: just ignore it *)
          Kernel_function.Set.empty
      | Some _ ->
        let name = mangle name TStandard proto in
        Frama_Clang_option.debug ~dkey "mangled name is %s" name;
        (try
          Kernel_function.Set.singleton (Globals.Functions.find_by_name name)
        with Not_found ->
          (* non-existing C++ name. Maybe someone else can find a matching
             function. *)
          Kernel_function.Set.empty)
  with Cxx_utils.NoCxxName ->
    (* not a C++ name, let someone else handle the case *)
    Kernel_function.Set.empty

let () =
  Parameter_customize.add_function_name_transformation mangle_cmdline_name

(* unmangling. To be polished, especially for templates. *)
(* NB: all operations below may raise an exception,
   that is catched by unmangle: an non well-formatted name is considered
   as not mangled. *)

let get_operator_name = function
    "dl" -> "delete"
  | "da" -> "delete[]"
  | "nw" -> "new"
  | "na" -> "new[]"
  | "nt" -> "operator!"
  | "co" -> "operator~"
  | "pp" -> "operator++"
  | "mm" -> "operator--"
  | "pl" -> "operator+"
  | "mi" -> "operator-"
  | "ml" -> "operator*"
  | "an" -> "operator&"
  | "dv" -> "operator/"
  | "rm" -> "operator%"
  | "ls" -> "operator<<"
  | "rs" -> "operator>>"
  | "eo" -> "operator^"
  | "or" -> "operator|"
  | "aS" -> "operator="
  | "pL" -> "operator+="
  | "mI" -> "operator-="
  | "mL" -> "operator*="
  | "dV" -> "operator/="
  | "rM" -> "operator%="
  | "lS" -> "operator<<="
  | "rS" -> "operator>>="
  | "aN" -> "operator&="
  | "eO" -> "operator^="
  | "oR" -> "operator|="
  | "eq" -> "operator=="
  | "ne" -> "operator!="
  | "lt" -> "operator<"
  | "gt" -> "operator>"
  | "le" -> "operator<="
  | "ge" -> "operator>="
  | "aa" -> "operator&&"
  | "oo" -> "operator||"
  | "pt" -> "operator->"
  | "pm" -> "operator->*"
  | "ix" -> "operator[]"
  | "cl" -> "operator()"
  | "cm" -> "operator,"
  | "qu" -> "operator?"
    (* return the unknown char for debugging purposes. *)
  | s ->    "operator#unknown(" ^ s ^")"

let rec get_name s =
  if s = "" then "",""
  else begin
  match s.[0] with
    | '0' .. '9' ->
        let i = ref 1 in
          while (Char.code s.[!i] <= Char.code '9' &&
                   Char.code s.[!i] >= Char.code '0') do incr i done;
          let length = String.sub s 0 !i in
          let length = int_of_string length in
            (String.sub s !i length, Str.string_after s (!i+length))
    | 'v' -> get_name (Str.string_after s 2)
    | 'c' when String.length s >= 2 && s.[1] = 'v' ->
        (* not very accurate *)
        let t,remain = unmangle_type (Str.string_after s 2) in
        "conversion(" ^ t ^ ")", remain
    | 'C' -> "Ctor", (Str.string_after s 2)
    | 'D' -> "Dtor", (Str.string_after s 2)
(*  | "N3" -> ...
    | "dE" -> ...
    | "E4" -> ...
    | "E4" -> ...
    | "st" -> ...
    | "E1" -> ...
    | "E9" -> ...
    | "E8" -> ...
    | "E2" -> ... *)
    | _ -> get_operator_name (String.sub s 0 2), (Str.string_after s 2)
  end
(* just counts the final 'E's to see what remains after an unsupported
   mangled param.
*)
and unmangle_abstract s =
  let rec aux s =
    let c = ref s in
    while !c.[0] <> 'E' do
      let remain = match !c.[0] with
        | 'L' | 'I' | 'N' | 'Z' | 'F' -> aux (Str.string_after !c 1)
        | _ -> (Str.string_after !c 1)
      in c := remain
    done;
    (Str.string_after !c 1)
  in "<abst>", aux s

and unmangle_primary_expression s =
  let i = String.index s 'E' in
  let arg = String.sub s 0 i in
  let remain = String.sub s (i+1) ((String.length s) - i - 1) in
  let arg = 
    if has_prefix arg then unmangle arg
    else begin
      let _, value = unmangle_type arg in
      if value.[0] = 'n' then "-" ^ Str.string_after value 1
      else value
    end
  in
  arg, remain

(* very incomplete.*)
and unmangle_expression s =
  match s.[0] with
      'L' ->
        let arg, remain = unmangle_primary_expression s in
        arg, Str.string_after remain 1 (*don't forget to swallow the 2nd 'E' *)
    | _ -> unmangle_abstract s

and unmangle_template_name s =
  let name, remain = get_name s in
  if remain <> "" then begin
  match remain.[0] with
  | 'I' ->
    let args, remain = unmangle_template (Str.string_after remain 1) in
    let template_name = name ^ "<" ^ args ^ ">" in
    template_name, remain
    | '_' -> name ^ remain, ""
    (* suffix generated by FC's kernel during renaming operation. *)
  | _ -> name, remain
  end else name, remain

and unmangle_qualified_name s =
  let last_name qual remain =
    let name, remain = get_name (Str.string_after remain 1) in
    let name = qual ^ "::" ^ name in
    if remain = "" then name, remain
    else begin
      match remain.[0] with
       | 'I' ->
         let args, remain = unmangle_template (Str.string_after remain 1) in
         name ^ "<" ^ args ^ ">", remain
       | '_' -> name ^ remain, ""
      (* suffix generated by FC's kernel during renaming operation. *)
       | _ -> name, remain
    end
  in
  let name,remain = unmangle_template_name s in
  if remain <> "" then begin
   match remain.[0] with
    | 'E' -> last_name name remain
    | 'I' ->
      let args, remain = unmangle_template (Str.string_after remain 1) in
      let template_name = name ^ "<" ^ args ^ ">" in
      if remain <> "" then begin
        match remain.[0] with
        | 'E' -> last_name template_name remain
        | _ ->
          let name, remain = unmangle_qualified_name remain in
          template_name ^ "::" ^ name, remain
      end else template_name, remain
    | _ ->
      let rest, remain = unmangle_qualified_name remain in
      name ^ "::" ^ rest, remain
  end else name, remain

and unmangle_template s = (* far from complete, but we don't really handle
                             templates yet *)
  let rec aux args remain =
    if remain = "" then
      raise (Invalid_argument ("unfinished template instantiation for " ^ s))
    else begin
      match remain.[0] with
      | 'E' -> List.rev args, Str.string_after remain 1
      | 'X' ->
        let arg, remain = unmangle_expression (Str.string_after remain 1) in
        aux (arg :: args) remain
      | 'L' ->
    let arg, remain =
          unmangle_primary_expression (Str.string_after remain 1)
    in
        aux (arg :: args) remain
      | _ ->
        let arg, remain = unmangle_type remain in
        aux (arg :: args) remain
    end
  in
  let args, remain = aux [] s in
  String.concat "," args, remain

and unmangle_type s =
  match s.[0] with
    | 'P' ->
        let typ, remain = unmangle_type (Str.string_after s 1) in
        typ ^ "*", remain (* should take care of priorities. *)
    | 'R' ->
        let typ, remain = unmangle_type (Str.string_after s 1) in
        typ ^ "&", remain (* should take care of priorities. *)
    | 'O' ->
        let typ, remain = unmangle_type (Str.string_after s 1) in
        typ ^ "&&", remain (* should take care of priorities. *)
    | 'r' | 'V' | 'K' ->
        unmangle_type (Str.string_after s 1)
          (* I'm afraid that adding the CV qualifier might clutter the
             output. *)
    | 'C' -> unmangle_type (Str.string_after s 1)
    | 'G' -> unmangle_type (Str.string_after s 1)
    | 'U' ->
        let _ , remain = get_name  (Str.string_after s 1)
        in unmangle_type remain
        (* don't clutter output with vendor-specific stuff *)
    (* now for builtin types *)
    | 'D' when String.length s > 1 && (s.[1] = 'i' || s.[1] = 's') ->
        let t = if s.[1] = 'i' then "char32_t" else "char16_t" in
        t, (Str.string_after s 2)
    | 'v' -> "void", (Str.string_after s 1)
    | 'w' -> "wchar_t", (Str.string_after s 1)
    | 'b' -> "bool",  (Str.string_after s 1)
    | 'c' -> "char",  (Str.string_after s 1)
    | 'a' -> "signed char",  (Str.string_after s 1)
    | 'h' -> "unsigned char",  (Str.string_after s 1)
    | 's' -> "short", (Str.string_after s 1)
    | 't' -> "unsigned short", (Str.string_after s 1)
    | 'i' -> "int", (Str.string_after s 1)
    | 'j' -> "unsigned int", (Str.string_after s 1)
    | 'l' -> "long", (Str.string_after s 1)
    | 'm' -> "unsigned long", (Str.string_after s 1)
    | 'x' -> "long long", (Str.string_after s 1)
    | 'y' -> "unsigned long long", (Str.string_after s 1)
    | 'n' -> "__int128", (Str.string_after s 1)
    | 'o' -> "unsigned __int128", (Str.string_after s 1)
    | 'f' -> "float", (Str.string_after s 1)
    | 'd' -> "double", (Str.string_after s 1)
    | 'e' -> "long double", (Str.string_after s 1)
    | 'g' -> "__float128", (Str.string_after s 1)
    | 'z' -> "ellipsis", (Str.string_after s 1)
    | 'u' -> get_name (Str.string_after s 1)
    | 'F' -> unmangle_abstract (Str.string_after s 1)
    | 'A' ->
        let i = String.index s '_' in
        let typ,remain = unmangle_type
          (String.sub s (i+1) (String.length s - i - 1))
        in
        typ ^"[]", remain (* don't consider the length *)
    | 'M' ->
        let name, remain = get_name (String.sub s 1 (String.length s - 1)) in
        let typ, remain = unmangle_type remain in
        Printf.sprintf "(%s)->*%s" name typ, remain
    | 'N' ->
      let name, remain =
        unmangle_complete_name (String.sub s 1 (String.length s - 1))
      in
      name, remain
    | _ -> unmangle_template_name s

and unmangle_complete_name s =
  if s = "" then "", ""
  else begin
  match s.[0] with
    | '0'..'9' -> unmangle_qualified_name s
      (* get rid of CV qualifier in method name *)
    | 'r' | 'V' | 'K' -> unmangle_complete_name (Str.string_after s 1)
    | _ -> raise (Invalid_argument "Not a properly mangled name")
  end

and unmangle name =
  try
  Printexc.record_backtrace true;
    if has_prefix name then begin
      let s = Str.string_after name 2 in
        if s.[0] = 'N'  then begin
      let name, _remain =
        unmangle_complete_name (Str.string_after s 1)
      in
      name
        end else begin
          let (name, remainder) = get_name s in
          if remainder <> "" then begin
            match remainder.[0] with
            | 'I' ->
              let args = Str.string_after remainder 1 in
              let args,_ = unmangle_template args in
              name ^ "<" ^ args ^ ">"
            | '_' -> (* suffix added by renaming operation in FC's kernel. *)
              name ^ remainder
            | _ -> name
          end else name
        end
    end else name
  with Invalid_argument s ->
    Printf.eprintf "could not demangle a name: %s (%s)\n" name s; name

let skip_template name =
  let len = String.length name in
  let rec aux idx nb_open =
    if idx = 0 || nb_open = 0 then idx
    else begin
      match name.[idx] with
      | '>' -> aux (idx - 1) (nb_open + 1)
      | '<' -> aux (idx - 1) (nb_open - 1)
      | _ -> aux (idx - 1) nb_open
    end
  in
  if len = 0 then 0
  else begin
    match name.[len - 1] with
    | '>' -> aux (len -2) 1
    | _ -> len - 1
  end

let basename name =
  let s = unmangle name in
  try
    let idx = skip_template s in
    let i = String.rindex_from s idx ':' in
    String.sub s (i+1) ((String.length s) - i - 1)
  with Not_found -> s

let short_name name =
  let s = unmangle name in
  let res = basename name in
  if res = "Ctor" || res = "Dtor"
     || res = "new" || res = "new[]"
     || res = "delete" || res = "delete[]"
  then
    try
      let idx =
        skip_template (String.sub s 0 (String.length s - String.length res - 2))
      in
      let i = String.rindex_from s idx ':' in
      String.sub s (i+1) ((String.length s) - i - 1)
    with Not_found -> s
  else res

let is_constructor_name name = basename name = "Ctor"

let () =
  Frama_Clang_option.Unmangling.register_mangling_func "short" short_name;
  Frama_Clang_option.Unmangling.register_mangling_func "full" unmangle;
  Frama_Clang_option.Unmangling.set "short"
