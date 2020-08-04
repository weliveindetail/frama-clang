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

let _compare_list cmp l1 l2 =
  let rec aux l1 l2 =
    match l1, l2 with
      | [], [] -> 0
      | [], _ -> -1
      | _,[] -> 1
      | x1::l1, x2::l2 -> let c = cmp x1 x2 in if c <> 0 then c else aux l1 l2
  in aux l1 l2

let _hash_list hash l =
  let rec aux depth h l =
    match l with
      | [] -> h
      | _ when depth = 0 -> h
      | x::l ->
          let h = hash x lxor h in aux (depth - 1) h l
  in aux 10 32578 l

let rec pretty_qualified_name fmt (n, t) =
  match t with
  | TStandard ->
    Format.fprintf fmt "%a::%s"
      (Pretty_utils.pp_list ~sep:"::" pretty_qualification) n.prequalification
      n.decl_name
  | TTemplateInstance t ->
    Format.fprintf fmt "%a::%s<%a>"
      (Pretty_utils.pp_list ~sep:"::" pretty_qualification) n.prequalification
      n.decl_name (Pretty_utils.pp_list ~sep:"," pretty_parameters) t
and pretty_qualification fmt q =
  match q with
  | QNamespace n | QStructOrClass n -> Format.pp_print_string fmt n
  | QTemplateInstance (n,params) -> Format.fprintf fmt "%s<%a>" n
      (Pretty_utils.pp_list ~sep:"," pretty_parameters) params
and pretty_parameters fmt tp =
  match tp with
  | TPStructOrClass n -> pretty_qualified_name fmt (n, TStandard)
  | TPTypename typ -> pretty_qual_type fmt typ
      (* Format.pp_print_string fmt "..." *)
  | TPConstant ccst ->
    begin
      match ccst with 
      | IntCst (_, _, v) -> Format.pp_print_string fmt (Int64.to_string v)
      | FloatCst(_,v) -> Format.pp_print_string fmt v
      | EnumCst(n,_,_) -> pretty_qualified_name fmt (n,TStandard)
      | TypeCst (_, _) -> Format.fprintf fmt "..."
    end
  | TPDeclaration name -> pretty_qualified_name fmt (name, TStandard)
and pretty_type fmt typ =
  match typ with
  | Void -> Format.pp_print_string fmt "void"
  | Int kind -> begin
      match kind with
        | IBool -> Format.pp_print_string fmt "bool"
        | IChar_u
        | IChar_s -> Format.pp_print_string fmt "char"
        | IUChar -> Format.pp_print_string fmt "unsigned char"
        | ISChar -> Format.pp_print_string fmt "signed char"
        | IChar16 -> Format.pp_print_string fmt "char16_t"
        | IChar32 -> Format.pp_print_string fmt "char32_t"
        | IWChar_u
        | IWChar_s -> Format.pp_print_string fmt "wchar_t"
        | IWUChar -> Format.pp_print_string fmt "unsigned wchar_t"
        | IWSChar -> Format.pp_print_string fmt "signed wchar_t"
        | IChar -> Format.pp_print_string fmt "char"
        | IWChar -> Format.pp_print_string fmt "wchar_t"
        | IShort -> Format.pp_print_string fmt "short"
        | IUShort -> Format.pp_print_string fmt "unsigned short"
        | IInt -> Format.pp_print_string fmt "int"
        | IUInt -> Format.pp_print_string fmt "unsigned int"
        | ILong -> Format.pp_print_string fmt "long"
        | IULong -> Format.pp_print_string fmt "unsigned long"
        | ILongLong -> Format.pp_print_string fmt "long long"
        | IULongLong -> Format.pp_print_string fmt "unsigned long long"
      end
  | Enum { body = name } -> pretty_qualified_name fmt (name, TStandard)
  | Float FFloat -> Format.pp_print_string fmt "float"
  | Float FDouble -> Format.pp_print_string fmt "double"
  | Float FLongDouble -> Format.pp_print_string fmt "long double"
  | Pointer (PDataPointer qtyp)
      -> Format.fprintf fmt "%a*" pretty_qual_type qtyp
  | Pointer (PFunctionPointer { result=qresult; parameter=args; variadic=b})
      -> (if (b)
          then Format.fprintf fmt "%a (*)(%a,...)"
          else Format.fprintf fmt "%a (*)(%a)")
         pretty_qual_type qresult
         (Pretty_utils.pp_list ~sep:" " pretty_qual_type) args
  | Pointer (PStandardMethodPointer
    ({ result=qresult; parameter=args; variadic=b}, shift))
      -> (if (b)
          then Format.fprintf fmt "%a ((shift=%s)::*)(%a,...)"
          else Format.fprintf fmt "%a ((shift=%s)::*)(%a)")
         pretty_qual_type qresult
         (Int64.to_string shift)
         (Pretty_utils.pp_list ~sep:" " pretty_qual_type) args
  | Pointer (PVirtualMethodPointer
     ({ result=qresult; parameter=args; variadic=b}, index, shift))
      -> (if (b)
          then Format.fprintf fmt "%a ((index=%s,shift=%s)::*)(%a,...)"
          else Format.fprintf fmt "%a ((index=%s,shift=%s)::*)(%a)")
         pretty_qual_type qresult
         (Int64.to_string index)
         (Int64.to_string shift)
         (Pretty_utils.pp_list ~sep:" " pretty_qual_type) args
  | LVReference (PDataPointer qtyp) ->
      Format.fprintf fmt "%a&" pretty_qual_type qtyp
  | RVReference (PDataPointer qtyp) ->
      Format.fprintf fmt "%a&&" pretty_qual_type qtyp
  | LVReference (PFunctionPointer { result=qresult; parameter=args; variadic=b})
      -> (if (b)
          then Format.fprintf fmt "%a (&)(%a,...)"
          else Format.fprintf fmt "%a (&)(%a)")
         pretty_qual_type qresult
         (Pretty_utils.pp_list ~sep:" " pretty_qual_type) args
  | RVReference (PFunctionPointer { result = qresult; parameter=args; variadic = b }) ->
      Format.fprintf fmt "%a (&&)(%a%s)"
        pretty_qual_type qresult
        (Pretty_utils.pp_list ~sep:" " pretty_qual_type) args
        (if b then ",..." else "")
  | LVReference (PStandardMethodPointer
     ({ result=qresult; parameter=args; variadic=b}, shift))
      -> (if (b)
          then Format.fprintf fmt "%a ((shift=%s)::&)(%a,...)"
          else Format.fprintf fmt "%a ((shift=%s)::&)(%a)")
         pretty_qual_type qresult
         (Int64.to_string shift)
         (Pretty_utils.pp_list ~sep:" " pretty_qual_type) args
  | RVReference
      (PStandardMethodPointer ({ result=qresult; parameter=args; variadic=b}, shift)) ->
          Format.fprintf fmt "%a ((shift=%s)::&)(%a%s)"
            pretty_qual_type qresult
            (Int64.to_string shift)
            (Pretty_utils.pp_list ~sep:" " pretty_qual_type) args
            (if b then ",..." else "")
  | LVReference (PVirtualMethodPointer
     ({ result=qresult; parameter=args; variadic=b}, index, shift))
      -> (if (b)
          then Format.fprintf fmt "%a ((index=%s,shift=%s)::&)(%a,...)"
          else Format.fprintf fmt "%a ((index=%s,shift=%s)::&&)(%a)")
         pretty_qual_type qresult
         (Int64.to_string index)
         (Int64.to_string shift)
         (Pretty_utils.pp_list ~sep:" " pretty_qual_type) args
  | RVReference
      (PVirtualMethodPointer
         ({ result=qresult; parameter=args; variadic=b}, index, shift)) ->
      Format.fprintf fmt "%a ((index=%s,shift=%s)::&&)(%a%s)"
        pretty_qual_type qresult (Int64.to_string index) (Int64.to_string shift)
        (Pretty_utils.pp_list ~sep:" " pretty_qual_type) args
        (if b then ",..." else "")
  | Array { subtype = qtyp; dimension = None }
      -> Format.fprintf fmt "%a[]" pretty_qual_type qtyp
  | Array { subtype = qtyp; dimension = Some _ }
      -> Format.fprintf fmt "%a[EXPR]" pretty_qual_type qtyp
  (* Using EXPR instead of the real VLA seems good *)
  | Struct (name, tc)
      -> Format.fprintf fmt "class %a"
         pretty_qualified_name (name, tc)
  | Union (name, tc)
      -> Format.fprintf fmt "union %a"
         pretty_qualified_name (name, tc)
  | Named (qname, _) -> pretty_qualified_name fmt (qname, TStandard)
  | Lambda (proto, cap) ->
    let pp_sep fmt () = Format.pp_print_string fmt ", " in
    Format.fprintf fmt "lambda %a [%a]-> %a"
      (Format.pp_print_list ~pp_sep pretty_qual_type)
      proto.parameter
      (Format.pp_print_list ~pp_sep pretty_capture) cap
      pretty_qual_type proto.result

and pretty_capture fmt cap =
  match cap with
  | Cap_id (s,typ,is_ref) ->
    Format.fprintf fmt "%a %s%s"
      pretty_qual_type typ (if is_ref then "&" else "=") s
  | Cap_this is_ref -> Format.fprintf fmt "%sthis" (if is_ref then "&" else "=")

and pretty_specifier fmt spec =
  match spec with
  | Const -> Format.pp_print_string fmt "const"
  | Volatile -> Format.pp_print_string fmt "volatile"
  | Restrict -> Format.pp_print_string fmt "restrict"
  | Static -> Format.pp_print_string fmt "static"
and pretty_qual_type fmt { qualifier = specs; plain_type = typ} =
  Format.fprintf fmt "%a (%a)"
    (Pretty_utils.pp_list ~sep:" " pretty_specifier) specs
    pretty_type typ

module Template_parameter =
  Datatype.Make_with_collections(
    struct
      include Datatype.Serializable_undefined
      type t = template_parameter
      let name = "Fclang_datatype.Template_parameter"
      let reprs = [TPConstant (IntCst (IInt,ICLiteral,Int64.of_int 0))]
      let compare = Stdlib.compare
      let equal = Datatype.from_compare
      let copy = Datatype.identity
      let hash = Hashtbl.hash
    end)

module Qualified_name =
  Datatype.Make_with_collections(
    struct
      include Datatype.Serializable_undefined
      type t = qualified_name * tkind
      let reprs = [({prequalification = [QNamespace "foo"]; decl_name = "bar"},
                    TStandard)]
      let name = "Fclang_datatype.Qualified_name"
      let compare = Stdlib.compare
      let equal = Datatype.from_compare
      let copy = Datatype.identity
      let hash = Hashtbl.hash
      let pretty = pretty_qualified_name
    end)

module Access_kind =
  Datatype.Make(
    struct
      include Datatype.Serializable_undefined
      type t = access_kind
      let reprs = [ Public; Private; Protected ]
      let name = "Fclang_datatype.Access_kind"
      let copy = Datatype.identity
    end)

module Vkind =
  Datatype.Make(
    struct
      include Datatype.Serializable_undefined
      type t = vkind
      let reprs = [ VVirtual; VStandard ]
      let name = "Fclang_datatype.Vkind"
      let copy = Datatype.identity
    end)

module Qual_type =
  Datatype.Make_with_collections(
    struct
      include Datatype.Serializable_undefined
      type t = qual_type
      let reprs = [ { qualifier = [Const]; plain_type = Int IInt } ]
      let name = "Fclang_datatype.Qual_type"
      let copy = Datatype.identity
      let compare = Stdlib.compare
      let equal = Datatype.from_compare
      let hash = Hashtbl.hash
      let pretty = pretty_qual_type
    end)
