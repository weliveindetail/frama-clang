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

include Plugin.S

(** -clang-command option *)
module Clang_command: Parameter_sig.String

module Clang_extra_args: Parameter_sig.String_list

(** state of the demangling options. *)
module Unmangling:
sig
  val set: string -> unit
  val get_val: unit -> (string -> string)
  val register_mangling_func: string -> (string->string) -> unit
end

(** -cxx-cstdlib-path option *)
module C_std_headers: Parameter_sig.String

(** -cxx-c++stdlib-path option *)
module Cxx_std_headers: Parameter_sig.String

(** -cxx-stdinc option *)
module Std_include: Parameter_sig.Bool

(** -cxx-vbmc option *)
module Cxx_virtual_bare_methods_in_clang: Parameter_sig.Bool

val dkey_reorder: category
