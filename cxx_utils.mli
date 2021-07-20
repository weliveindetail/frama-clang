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

open Intermediate_format

(** Various utilities function for manipulating intermediate_format ASTs *)

(** raised when a string can't be converted in an existing C++ identifier. *)
exception NoCxxName

(** given a string representing a C++ name and optionally a full function
    signature, returns the corresponding qualified name, with signature.
    @raise NoCxxName if the string does not correspond to a C++ name or
    signature.
*)
val analyse_entrypoint:
  string -> 
  qualified_name * (funkind * signature) option

(** [true] if the given string is the name of a builtin type. *)
val is_builtin_type: string -> bool

val is_builtin_qual_type: qualified_name -> bool

(** [true] iff the type is const-qualified. *)
val is_const_type: qual_type -> bool

(** merge the given specifiers with the ones the type already has. *)
val add_qualifiers: specifier list -> qual_type -> qual_type

(** {2 AST constructors. } *)

(** {3 names } *)

val empty_qual: string -> qualified_name

(** given a (potentially templated) class and a method name, 
    returns the fully-qualified method name. *)
val meth_name: qualified_name -> tkind -> string -> qualified_name

(** {3 Types}. *)

(** returns the unqualified version of the given typ. *)
val unqual_type: typ -> qual_type

(** const-qualified version of the given typ. *)
val const_type: typ -> qual_type

(** ensures that the given type is const-qualified. *)
val const_qual_type: qual_type -> qual_type

(** ensures that the given object pointer type points to a constant type.
    Does nothing if the original type is not a pointer to an object.
 *)
val force_ptr_to_const: qual_type -> qual_type

(** given an object type, returns an unqualified pointer type to the object. *)
val obj_ptr: qual_type -> qual_type

(** given an object type, returns an unqualified lvreference type to the object*)
val obj_lvref: qual_type -> qual_type

(** given an object type, returns an unqualified rvreference type to the object*)
val obj_rvref: qual_type -> qual_type

val plain_obj_ptr: qual_type -> typ

val plain_obj_lvref: qual_type -> typ

val plain_obj_rvref: qual_type -> typ

val plain_class_ptr: Fclang_datatype.Qualified_name.t -> typ

val plain_class_lvref: Fclang_datatype.Qualified_name.t -> typ

val plain_class_rvref: Fclang_datatype.Qualified_name.t -> typ

val class_ptr: Fclang_datatype.Qualified_name.t -> qual_type

val class_lvref: Fclang_datatype.Qualified_name.t -> qual_type

val class_rvref: Fclang_datatype.Qualified_name.t -> qual_type
