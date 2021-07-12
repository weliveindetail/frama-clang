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

(** attribute decorating member functions that are implicitly defined
    by Frama-Clang. *)
val fc_implicit_attr: string

(** attribute decorating templated member functions that are never defined
    (i.e. fully instantiated). Their presence in the AST tends to be
    dependent on the clang version used for type-checking.
*)
val fc_pure_template_decl_attr: string

(** creates the name of the field corresponding to a direct base class. *)
val create_base_field_name: Convert_env.env -> qualified_name -> tkind -> string

val convert_ast: Intermediate_format.file -> Cabs.file

(** remove unneeded definitions and declarations. Notably:
    - unused implicit definitions
    - templated member functions that are not defined and never used.
*)
val remove_unneeded: Cil_types.file -> unit
