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

(** Information related to class: inheritance diagram, virtual meths, ... *)

open Intermediate_format
open Fclang_datatype

(* all the Qualified_name.t should avoid typedefs except builtin ones *)
val inheritance_graph_state: State.t

(** [add_inheritance_relation b a] indicates that [b] inherits from [a]. *)
val add_inheritance_relation: Qualified_name.t -> inheritance -> unit
val add_class: Qualified_name.t -> unit

(** [get_bases_list b] returns all a such that [b] inherits from [a]. *)
val get_bases_list: Qualified_name.t -> inheritance list

(** [has_virtual_base_class b] returns true iff b has a virtual base class
    or if [has_virtual_base_class a] for a such that [b] inherits from [a]. *)
val has_virtual_base_class : Qualified_name.t -> bool

(** [get_virtual_base_classes b] returns the list of the virtual base classes
    of b. The list is unordered and built recursively on the base classes *)
val get_virtual_base_classes : Qualified_name.t -> Qualified_name.t list

(** returns all the classes derived (directly or indirectly) from the one
    given as argument. *)
val subtypes: Qualified_name.t -> Qualified_name.Set.t

(** retrieve the C++ name of a class from an mangled identifier, or [None] if
    no such class exist in the inheritance graph. *)
val class_of_mangled: string -> Qualified_name.t option

(** [has_unambiguous_path b a] is [true]
    if [b] unambiguously inherits from a. *)
val has_unambiguous_path: Qualified_name.t -> Qualified_name.t -> bool

(** [has_public_path b a] is [true] if [a] is a base class of [b] following
    a public inheritance path only. *)
val has_public_path: Qualified_name.t -> Qualified_name.t -> bool

exception No_path

(** [inheritance_path derived base] returns an inheritance path from
    [derived] to [base]. In case of ambiguity, the selected path is not
    specified.
    @raise No_path if [derived] is not derived from [base] *)
val inheritance_path: Qualified_name.t -> Qualified_name.t ->
  ((Qualified_name.t * (access_kind * vkind) * Qualified_name.t) list)
