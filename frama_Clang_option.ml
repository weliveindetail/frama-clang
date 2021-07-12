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

include
  Plugin.Register(
    struct
      let name = "Frama_Clang"
      let shortname = "fclang"
      let help = "Use clang as C++ front-end for Frama-C"
    end)


module Clang_command =
  String(
    struct
      let option_name = "-cxx-clang-command"
      let default = "framaCIRGen"
      let help = 
        "use <cmd> as the parsing command. Defaults to " ^ default
      let arg_name = "cmd"
    end)

let () = Parameter_customize.no_category ()
module Clang_extra_args =
  String_list(
      struct
        let option_name = "-fclang-cpp-extra-args"
        let help =
          "pass additional options to clang. If not set, the content of \
           -cpp-extra-args (if any) is used instead"
        let arg_name = "opt"
      end)

module Unmangling:
sig
  val set: string -> unit
  val get: unit -> string
  val clear: unit -> unit
  val get_val: unit -> (string -> string)
  val register_mangling_func: string -> (string->string) -> unit
end
=
  struct
    module Rep =
      State_builder.Ref(Datatype.String)
        (struct let dependencies = []
                let name = "Unmangling"
                let default () = "short"
         end)
    let available_opt = Hashtbl.create 7
    let set s = if Hashtbl.mem available_opt s then Rep.set s
    let clear () = Rep.clear ()
    let get () = Rep.get ()
    let get_val () = Hashtbl.find available_opt (Rep.get ())
    let register_mangling_func s f = Hashtbl.add available_opt s f
    let () =
      register_mangling_func "id" (fun s -> s);
      set "short"
  end

module UnmanglingFull =
  Bool(struct
             let default = false
             let option_name = "-cxx-demangling-full"
             let help= "displays identifiers with their full C++ name"
        end)

let () = Parameter_customize.set_negative_option_name ""

module UnmanglingShort =
  Bool(struct
             let default = false
             let option_name = "-cxx-demangling-short"
             let help=
               "displays identifiers with their C++ short name \
                (without qualifiers)"
        end)

let () = Parameter_customize.set_negative_option_name ""

module UnmanglingNo =
  Bool(struct
             let default = false
             let option_name= "-cxx-keep-mangling"
             let help= "displays identifiers with their mangled name"
           end)

let add_unmangling_option s _ new_flag =
  if new_flag then Unmangling.set s
  else if Unmangling.get () = s then Unmangling.clear ()

let () =
  UnmanglingFull.add_set_hook (add_unmangling_option "full");
  UnmanglingShort.add_set_hook (add_unmangling_option "short");
  UnmanglingNo.add_set_hook (add_unmangling_option "id");

module C_std_headers = 
  String(
    struct
      let default = (Fc_config.datadir:>string) ^ "/libc"
      let option_name = "-cxx-cstdlib-path"
      let help = "<path> where to look for C standard headers \
                  (default: Frama-C libc in " ^ default ^ ")"
      let arg_name = "path"
    end)

module Cxx_std_headers = 
  String(
    struct
      let default = (Fc_config.datadir:>string) ^ "/frama-clang/libc++"
      let option_name = "-cxx-c++stdlib-path"
      let help = "<path> where to look for C++ standard headers \
                  (default: FClang libc++ in " ^ default ^ ")"
      let arg_name = "path"
    end)

module Cxx_virtual_bare_methods_in_clang =
  Bool(struct
             let default = false
             let option_name= "-cxx-vbmc"
             let help= "Asks clang to generate bare constructors and \
                        destructors in case of virtual inheritance"
           end)

let () = Parameter_customize.set_negative_option_name "-cxx-nostdinc"
module Std_include =
  Bool(
    struct
      let default = true
      let option_name = "-cxx-stdinc"
      let help = "Adds Frama-C standard headers for C and C++ \
                  in include path (default)."
    end)

let dkey_reorder = register_category "reorder"
