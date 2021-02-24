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

let dkey = Frama_Clang_option.register_category "cabs"

let clang_key = Frama_Clang_option.register_category "clang"

let targets =
  [ 
    "x86_32", "i386-unknown-linux-gnu";
    "gcc_x86_32", "i386-unknown-linux-gnu";
    "x86_64", "x86_64-unknown-linux-gnu";
    "gcc_x86_64", "x86_64-unknown-linux-gnu";
    "ppc_32", "powerpc-unknown-linux-gnu";
  ]

let target_of_machdep s =
  let default = "i386-pc-linux-gnu" in
  let machine =
    try
      List.assoc s targets
    with Not_found ->
      Frama_Clang_option.warning 
        "Unknown or unsupported machdep %s. \
         Using default target %s for clang" s default;
      default
  in
  "-target " ^ machine

let regexp_match r s =
  try ignore (Str.search_forward r s 0); true with Not_found -> false

let target_regex = Str.regexp "-target[ ]+[^ ]+"
let machdep_regex = Str.regexp "-D[ ]*__FC_MACHDEP"
let std_regex = Str.regexp "-std="

let run_clang debug input output =
  let use_own_headers = Frama_Clang_option.Std_include.get() in
  let machine = Kernel.Machdep.get () in
  let clang_command = Frama_Clang_option.Clang_command.get () in
  let extra_args =
    if Frama_Clang_option.Clang_extra_args.is_set () then
      Frama_Clang_option.Clang_extra_args.get ()
    else Kernel.CppExtraArgs.get ()
  in
  let extra_args = String.concat " " extra_args in
  let clang_machine =
    if regexp_match target_regex extra_args || not use_own_headers 
    (* when using system headers, user is on their own to ensure coherence
       between C and OCaml vision of the architecture.
    *)
    then ""
    else target_of_machdep machine 
  in
  let machdep_macro =
    if regexp_match machdep_regex extra_args || not use_own_headers
    then "" 
    else  " -D" ^ File.machdep_macro machine
  in
  let std_opt =
    if regexp_match std_regex extra_args then " -x c++"
    else
      match machine with
      | "gcc_x86_32" | "gcc_x86_64" -> " -std=gnu++11"
      | _ -> " -std=c++11"
  in
  let default_args = clang_machine ^ machdep_macro ^ std_opt in
  let include_path =
    if use_own_headers then begin
      Printf.sprintf "-nostdinc -I %s -I %s"
        (Frama_Clang_option.Cxx_std_headers.get())
        (Frama_Clang_option.C_std_headers.get())
    end else ""
  in
  let does_generate_bare_methods_in_clang =
    if Frama_Clang_option.Cxx_virtual_bare_methods_in_clang.get ()
    then "-b" else ""
  in
  let treat_annot =
    match Kernel.get_warn_status Kernel.wkey_annot_error with
      | Log.Winactive | Log.Wactive | Log.Wonce
        | Log.Wfeedback | Log.Wfeedback_once -> ""
      | Log.Wabort | Log.Werror | Log.Werror_once -> "--stop-annot-error"
  in
  let full_command =
    Printf.sprintf
      "%s %s %s %s %s %s %s %s -o %s"
      clang_command extra_args default_args include_path treat_annot
      (if debug then "-v" else "") does_generate_bare_methods_in_clang
      input output
  in
  Frama_Clang_option.feedback
    ~dkey:clang_key "Clang command is %s" full_command;
  let res = Sys.command(full_command) in
  if res <> 0 then
    Kernel.abort
      "Failed to parse C++ file. See Clang messages for more information"

module Cxx_printer(M: Printer.PrinterClass): Printer.PrinterClass =
struct
  class printer = object
    inherit M.printer
    method! varname fmt name =
      Format.pp_print_string fmt (Frama_Clang_option.Unmangling.get_val() name)
  end
end

(* we avoid any side effect on the kernel unless we are parsing explicitly
   a C++ file. *)

let is_initialized = ref false

let init_cxx_normalization () =
  if not !is_initialized then begin
      is_initialized:=true;
      Cil_printer.register_shallow_attribute Convert.fc_implicit_attr;
      Printer.update_printer (module Cxx_printer);
      (* enable exception removal unless it has explicitely been set to false
         on the command line.
       *)
      if not (Kernel.RemoveExn.is_set ()) then Kernel.RemoveExn.on ();
      Convert_link.register_transformation ();
      (* Current implementation of VMT is not compatible with this warning. *)
      Kernel.set_warn_status Kernel.wkey_incompatible_types_call Log.Winactive ;
      (* C++ allows this *)
      Cil.set_acceptEmptyCompinfo ()
    end
      
let parse_cxx file =
  init_cxx_normalization ();
  Frama_Clang_option.feedback
    ~level:2 "Parsing C++ file %S" file;
  let debug = Frama_Clang_option.is_debug_key_enabled clang_key in
  let clang_result = Extlib.temp_file_cleanup_at_exit ~debug "clang_ast" "ast"
  in
  run_clang debug file clang_result;
  Frama_Clang_option.feedback ~level:2 "Parsing Clang result";
  let ast_chan = open_in clang_result in
  let ast_tree = 
    try Intermediate_format_parser.make_tree ast_chan
    with Failure msg ->
      Frama_Clang_option.fatal "Cannot build intermediate tree: %s" msg
  in
  Frama_Clang_option.debug ~level:2 
    "uninterpreted intermediate tree:@\n%a"
    Intermediate_format_parser.print_tree ast_tree;
  close_in ast_chan;
  Frama_Clang_option.feedback ~level:2 "Creating intermediate tree";
  let ast = 
    try Intermediate_format_parser.parse_file ast_tree 
    with Intermediate_format_parser.Parse_error msg ->
      Frama_Clang_option.fatal "Cannot understand intermediate AST: %s" msg
  in
  Frama_Clang_option.feedback ~level:2 "Converting into Cabs";
  let cabs = Convert.convert_ast ast in
  Frama_Clang_option.feedback ~dkey "Generated Cabs code:@\n%a"
    Cprint.printFile cabs;
  let cil = Cabs2cil.convFile cabs in
  Convert.remove_implicit cil;
  (cil, cabs)

let cxx_suffixes = [ ".cpp"; ".C"; ".cxx"; ".c++"; ".cc"; ".ii" ]

let remove_wp_assigns_warning () =
  Wp.Wp_parameters.set_warn_status Wp.AssignsCompleteness.wkey_pedantic Log.Winactive

let () =
  remove_wp_assigns_warning () ;
  List.iter
    (fun suf -> File.new_file_type suf parse_cxx) cxx_suffixes
