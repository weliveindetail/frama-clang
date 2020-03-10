(**************************************************************************)
(*                                                                        *)
(*  This file is part of Frama-Clang                                      *)
(*                                                                        *)
(*  Copyright (C) 2012-2020                                               *)
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

open Intermediate_format
open Genlex

let dkey = Frama_Clang_option.register_category "parse_ident"

let builtin_types = [ "__builtin_va_list" ]

let is_builtin_type t = List.mem t builtin_types

let is_builtin_qual_type n = List.mem n.decl_name builtin_types

let is_const_type t = List.mem Const t.qualifier

let add_qualifier typ qual =
  if List.mem qual typ.qualifier then typ else
    { typ with qualifier = qual :: typ.qualifier }

let add_qualifiers quals typ = List.fold_left add_qualifier typ quals

let lexer = Genlex.make_lexer
  [ "("; ")"; "::"; "<"; ">"; ","; "*"; "&"; "&&"; "~";
    "bool"; "char"; "const"; "float"; "double"; "int"; "long"; "short";
    "static"; "unsigned"; "void"; "volatile"; "wchar_t";
  ]

let rec wait_for l s =
  match Stream.peek s with
  | Some l' -> Stream.junk s; if l <> l' then wait_for l s
  | None -> ()

let identify_u_long b s =
  match Stream.peek s with
  | Some (Kwd "int") ->
    Stream.junk s;
    if b then raise (Stream.Error "illegal type specification")
    else Intermediate_format.Int IULong
  | _ -> Intermediate_format.Int IULong

let identify_u_short b s =
  match Stream.peek s with
  | Some (Kwd "int") ->
    Stream.junk s;
    if b then raise (Stream.Error "illegal type specification")
    else Intermediate_format.Int IUShort
  | _ -> Intermediate_format.Int IUShort

let identify_s_long b s =
  match Stream.peek s with
  | Some (Kwd "int") ->
    Stream.junk s;
    if b then raise (Stream.Error "illegal type specification")
    else Intermediate_format.Int ILong
  | _ -> Intermediate_format.Int ILong

let identify_s_short b s =
  match Stream.peek s with
  | Some (Kwd "int") ->
    Stream.junk s;
    if b then raise (Stream.Error "illegal type specification")
    else Intermediate_format.Int IShort
  | _ -> Intermediate_format.Int IShort

let rec identify_unsigned b s =
  match Stream.peek s with
  | Some (Kwd "long") -> Stream.junk s; identify_u_long b s
  | Some (Kwd "short") -> Stream.junk s; identify_u_short b s
  | Some (Kwd "int") ->
    Stream.junk s;
    if b then raise (Stream.Error "illegal type specification")
    else identify_unsigned true s
  | Some (Kwd "char") ->
    Stream.junk s;
    if b then raise (Stream.Error "illegal type specification")
    else Intermediate_format.Int IUChar
  | _ -> Intermediate_format.Int IUInt

let rec identify_signed b s =
  match Stream.peek s with
  | Some (Kwd "long") -> Stream.junk s; identify_s_long b s
  | Some (Kwd "short") -> Stream.junk s; identify_s_short b s
  | Some (Kwd "int") ->
    Stream.junk s;
    if b then raise (Stream.Error "illegal type specification")
    else identify_signed true s
  | Some (Kwd "char") ->
    Stream.junk s;
    if b then raise (Stream.Error "illegal type specification")
    else Intermediate_format.Int ISChar
  | _ -> Intermediate_format.Int IInt

let identify_long_double _ = Intermediate_format.Float FLongDouble

let identify_float _ = Intermediate_format.Float FFloat

let rec identify_long b s =
  match Stream.peek s with
  | Some (Kwd "int") ->
    Stream.junk s;
    if b then raise (Stream.Error "illegal type specification")
    else identify_long true s
  | Some (Kwd "signed") -> Stream.junk s; identify_s_long b s
  | Some (Kwd "unsigned") -> Stream.junk s; identify_u_long b s
  | Some (Kwd "double") ->
    Stream.junk s;
    if b then raise (Stream.Error "illegal type specification")
    else identify_long_double s
  | _ -> Intermediate_format.Int ILong

let rec identify_short b s =
  match Stream.peek s with
  | Some (Kwd "int") ->
    Stream.junk s;
    if b then raise (Stream.Error "illegal type specification")
    else identify_short true s
  | Some (Kwd "signed") -> Stream.junk s; identify_s_short b s
  | Some (Kwd "unsigned") -> Stream.junk s; identify_u_short b s
  | _ -> Intermediate_format.Int IShort

let identify_double s =
  match Stream.peek s with
  | Some (Kwd "long") -> Stream.junk s; identify_long_double s
  | _ -> Intermediate_format.Float FDouble

let identify_char s =
  match Stream.peek s with
  | Some (Kwd "signed") -> Stream.junk s; Intermediate_format.Int ISChar
  | Some (Kwd "unsigned") -> Stream.junk s; Intermediate_format.Int IUChar
  | _ -> Intermediate_format.Int IChar

let identify_int s =
  match Stream.peek s with
  | Some (Kwd "unsigned") -> Stream.junk s; identify_unsigned true s
  | Some (Kwd "long") -> Stream.junk s; identify_long true s
  | Some (Kwd "short") -> Stream.junk s; identify_short true s
  | Some (Kwd "signed") -> Stream.junk s; identify_signed true s
  | _ -> Intermediate_format.Int IInt

let decl_flag s =
  match Stream.peek s with
  | Some (Kwd "const") -> Stream.junk s; Some Const
  | Some (Kwd "volatile") -> Stream.junk s; Some Volatile
  | Some (Kwd "restrict") -> Stream.junk s; Some Restrict
  | Some (Kwd "static") -> Stream.junk s; Some Static
  | _ -> None

let opt_dimension s =
  match Stream.peek s with
  | Some (Int i) ->
    Stream.junk s;
    Some { eloc=(Lexing.dummy_pos, Lexing.dummy_pos);
           econtent=Constant (IntCst (IInt, ICLiteral, Int64.of_int i)) }
  | _ -> wait_for (Kwd "]") s; None

let rec parse_simple_type s =
  match ident s with
  | Some s -> Some (Struct (s,TStandard))
  | None ->
    begin match Stream.peek s with
      | Some (Kwd "bool") -> Stream.junk s; Some (Intermediate_format.Int IBool)
      | Some (Kwd "void") -> Stream.junk s; Some Void
      | Some (Kwd "int") -> Stream.junk s; Some (identify_int s)
      | Some (Kwd "char") -> Stream.junk s; Some (identify_char s)
      | Some (Kwd "unsigned") -> Stream.junk s; Some (identify_unsigned false s)
      | Some (Kwd "long") -> Stream.junk s; Some (identify_long false s)
      | Some (Kwd "short") -> Stream.junk s; Some (identify_short false s)
      | Some (Kwd "signed") -> Stream.junk s; Some (identify_signed false s)
      | Some (Kwd "float") -> Stream.junk s; Some (identify_float s)
      | Some (Kwd "double") -> Stream.junk s; Some (identify_double s)
      | _ -> None
    end
(* Not really accurate (should take priorities and parentheses into account). *)
and modifier typ s =
  match Stream.peek s with
  | Some (Kwd "*") ->
    Stream.junk s;
    modifier (Pointer (PDataPointer { qualifier = []; plain_type = typ})) s
  | Some (Kwd "&") ->
    Stream.junk s;
    modifier (LVReference (PDataPointer {qualifier=[];plain_type=typ})) s
  | Some (Kwd "&&") ->
    Stream.junk s;
    modifier (RVReference (PDataPointer {qualifier=[];plain_type=typ})) s
  | Some (Kwd "[") ->
    begin
      Stream.junk s;
      let dim = opt_dimension s in
      modifier
        (Array { subtype = {qualifier=[];plain_type=typ}; dimension = dim }) s
    end
  | _ -> typ

and template_args s =
  let t = template_arg s in
  let l = try_next_template_arg s in
  t :: l

and try_next_template_arg s =
  match Stream.peek s with
  | Some (Kwd ",") -> Stream.junk s; template_args s
  | _ -> []

(* Very incomplete *)
and template_arg s =
  match Stream.peek s with
  | Some (Int i) ->
    Stream.junk s; TPConstant (IntCst(IInt, ICLiteral, Int64.of_int i))
  | _ ->
    begin match ident s with
      | Some id -> TPStructOrClass id
      | None -> TPTypename (parse_type s)
      (* NB: we don't distinguish anymore between STA_TYPE and STA_ATOMIC*)
    end

and template t s =
  match Stream.peek s with
  | Some (Kwd "<") ->
    Stream.junk s;
    let l = template_args s in
    Stream.junk s; (* TODO: check that it is Kwd ">" *)
    maybe_qual (QTemplateInstance (t,l)) s
  | _ -> maybe_qual (QNamespace t) s

and ident s =
  match Stream.npeek 2 s with
   | Ident id :: _ ->
      Frama_Clang_option.debug ~dkey "IDENT(%s)" id;
      Stream.junk s;
      Some (template id s)
   | Kwd "~" :: Ident id :: _ ->
      Frama_Clang_option.debug ~dkey "DESTR(%s)" id;
      Some { prequalification = []; decl_name = "~" ^ id }
   | _ -> None

and maybe_qual prefix s =
  match Stream.peek s with
  | Some Kwd "::" ->
    Frama_Clang_option.debug ~dkey "QUAL";
    Stream.junk s;
    (match ident s with
     | Some id ->
       { id with prequalification = prefix :: id.prequalification }
     | None -> raise (Stream.Error "unsupported qualifier sequence"))
  | _ ->
    match prefix with
    | QNamespace s | QStructOrClass s ->
      { prequalification = []; decl_name = s }
    | QTemplateInstance (s,_) ->
      Frama_Clang_option.warning
        "Dropping template arguments during parsing of identifier";
      { prequalification = []; decl_name = s }

and parse_type_aux t s =
  match decl_flag s with
  | Some q -> parse_type_aux (add_qualifier t q) s
  | None ->
    (match parse_simple_type s with
     | Some st ->
       let typ = modifier st s in
       { t with plain_type = typ }
     | None -> t)

and parse_type s =
  parse_type_aux { qualifier = []; plain_type = Void } s

let rec parse_args s =
  let a = parse_type s in
  let l = maybe_args s in
  a :: l
and maybe_args s =
  match Stream.peek s with
  | Some (Ident _) -> Stream.junk s; next_args s
  | _ -> next_args s
and next_args s =
  match Stream.peek s with
  | Some (Kwd ",") -> Stream.junk s; parse_args s
  | Some (Kwd ")") -> Stream.junk s; []
  | _ -> raise (Stream.Error "Unfinished argument list")

let parse_formals s =
  match Stream.peek s with
  | Some (Kwd "(") ->
    Stream.junk s; Frama_Clang_option.debug ~dkey "IS_SIG"; Some (parse_args s)
  | _ -> None

let plain_ident_or_func id s =
  match ident s with
  | Some f ->
    (match parse_formals s with
     | Some args ->
       f,
       Some 
         (FKFunction, 
          { result =
              { qualifier = [];
                plain_type = Struct (id, TStandard);
              };
            parameter = args;
            variadic = false;
          })
     | None -> id, None)
  | None ->
    (match parse_formals s with
     | Some args ->
       let kind =
         if String.length id.decl_name > 0 && id.decl_name.[0] = '~' then
           FKDestructor true
         else begin
           match id.prequalification with
           | [] -> FKFunction
           | l ->
             match Extlib.last l with
             | QNamespace s | QStructOrClass s | QTemplateInstance (s,_)
               when s = id.decl_name ->
               FKConstructor true
             | QNamespace _ | QStructOrClass _ | QTemplateInstance _ ->
               FKFunction
         end
       in
       (id,
        Some (kind, 
              { result = { qualifier = []; plain_type = Struct (id, TStandard)};
                parameter = args;
                variadic = false;
              }))
     | None -> id, None)

let parse_signature s =
  match Stream.peek s with
  | Some (Kwd "::") ->
    Stream.junk s;
    (match ident s with
     | Some i -> plain_ident_or_func i s
     | None -> raise (Stream.Error "ill-formed C++ full qualification"))
  | _ ->
    (match ident s with
     | Some i -> plain_ident_or_func i s
     | None ->
       let rt = parse_type s in
       (match ident s with
        | Some f ->
          (match parse_formals s with
           | Some args ->
             f,
             Some (FKFunction,
                   { result = rt; parameter = args; variadic = false })
           | None -> raise (Stream.Error "unexpected format for C++ signature"))
        | None -> raise (Stream.Error "unexpected format for C++ signature")))

exception NoCxxName

let analyse_entrypoint s =
  try
    let input = Stream.of_string s in
    let input = lexer input in
    parse_signature input
  with
    | Stream.Error e -> 
      Frama_Clang_option.debug ~dkey
        "Unable to parse symbol %s as C++ function (%s). \
         Considering it as standard C identifier" s e;
      raise NoCxxName

let empty_qual s = { prequalification = []; decl_name = s }

let meth_name class_name tkind decl_name =
  let last_elt =
    match tkind with
      | TStandard -> QStructOrClass class_name.decl_name
      | TTemplateInstance i -> QTemplateInstance (class_name.decl_name, i)
  in
  let prequalification= List.append class_name.prequalification [last_elt] in
  { prequalification; decl_name }

let unqual_type t = { qualifier = []; plain_type = t }

let const_type t = { qualifier = [ Const ]; plain_type = t }

let const_qual_type t =
  if List.mem Const t.qualifier then t
  else { t with qualifier = Const :: t.qualifier }

let force_ptr_to_const p =
  match p with
  | { plain_type = Pointer (PDataPointer t) } ->
    let t = const_qual_type t in
    { p with plain_type = Pointer (PDataPointer t) }
  | _ -> p

let make_lambda_type result args closure =
  let parameter = List.map (fun x -> x.arg_type) args in
  Lambda ({ result; parameter; variadic = false }, closure)

let plain_obj_ptr t = Pointer (PDataPointer t)

let plain_obj_lvref t = LVReference (PDataPointer t)

let plain_obj_rvref t = RVReference (PDataPointer t)

let obj_ptr t = unqual_type (plain_obj_ptr t)

let obj_lvref t = unqual_type (plain_obj_lvref t)

let obj_rvref t = unqual_type (plain_obj_rvref t)

let plain_class_ptr (n,t) = plain_obj_ptr (unqual_type (Struct (n,t)))

let plain_class_lvref (n,t) = plain_obj_lvref (unqual_type (Struct (n,t)))

let plain_class_rvref (n,t) = plain_obj_rvref (unqual_type (Struct (n,t)))

let class_ptr (n,t) = unqual_type (plain_class_ptr (n,t))

let class_lvref (n,t) = unqual_type (plain_class_lvref (n,t))

let class_rvref (n,t) = unqual_type (plain_class_rvref (n,t))
