(**************************************************************************)
(*                                                                        *)
(*  This file is part of Frama-Clang                                      *)
(*                                                                        *)
(*  Copyright (C) 2012-2018                                               *)
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

(** Name mangling. Follows more or less IA-64 C++ ABI and thus gcc mangling.*)

open Intermediate_format

(** compute the mangled name. For functions, the second argument is their
    signature. It is None for any other identifier. *)

val mangle:
  qualified_name -> tkind -> (funkind * signature) option -> string

(** transforms a mangled name into a more readable string. *)
val unmangle: string -> string

(** computes an unqualified name from a mangled name. *)
val short_name: string -> string

(** [true] if the given mangled name is the name of a constructor
    (as obtained by {!mangle} *)
val is_constructor_name: string -> bool

val mangle_cc_type: typ -> string
