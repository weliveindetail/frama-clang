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

(** Elements of specification generated from the C++ conversion itself. *)

open Intermediate_format

(** adds contract elements to the default behavior of the given spec 
    related to the corresponding signature elements.
*)
val add_contract:
  env: Convert_env.env -> kind:funkind -> return_type:qual_type -> 
  args: arg_decl list -> variadic: bool -> implicit: bool -> extern_c:bool ->
  (Logic_ptree.spec * Cabs.cabsloc) option -> 
  (Logic_ptree.spec * Cabs.cabsloc) option
