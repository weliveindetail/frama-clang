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

open Logic_ptree
open Intermediate_format

let toplevel_pred tp_statement = { tp_kind = Assert; tp_statement }

let const_valid lexpr_loc pkind t =
  let lexpr_node =
    match pkind with
    | PDataPointer { qualifier = q } ->
      if List.mem Const q then PLvalid_read(None, t) else PLvalid(None,t)
    | PFunctionPointer _ | PStandardMethodPointer _ | PVirtualMethodPointer _
      -> PLvalid_function(t)
  in
  toplevel_pred { lexpr_node; lexpr_loc }

let add_valid_result env typ =
  let loc = Convert_env.get_loc env in
  let rec aux = function
    | LVReference kind | RVReference kind ->
        [Cil_types.Normal,
         const_valid loc kind { lexpr_node = PLresult; lexpr_loc = loc}]
    | Named (name,_) when Cxx_utils.is_builtin_qual_type name -> []
    | Named (name,_) -> aux (Convert_env.get_typedef env name).plain_type
    | _ -> []
  in aux typ.plain_type

let add_valid_reference env acc arg =
  let lexpr_loc = Cil_datatype.Location.of_lexing_loc arg.arg_loc in
  let rec aux =
    function
      | LVReference kind | RVReference kind ->
        const_valid lexpr_loc kind
          { lexpr_node = PLvar(arg.arg_name); lexpr_loc }
        :: acc
      | Named (name,_) when Cxx_utils.is_builtin_qual_type name -> acc
      | Named (name,_) -> aux (Convert_env.get_typedef env name).plain_type
      | _ -> acc
  in aux arg.arg_type.plain_type

let add_valid_references env l = List.fold_left (add_valid_reference env) [] l

let add_valid_this env kind =
  let lexpr_loc = Convert_env.get_loc env in
  let this = { lexpr_node = PLvar "this"; lexpr_loc } in
  let valid_read =
    toplevel_pred { lexpr_node = PLvalid_read (None, this); lexpr_loc }
  in
  let valid = toplevel_pred { lexpr_node = PLvalid(None, this); lexpr_loc } in
  match kind with
  | FKCastMethodOperator (cv,_) when List.mem Const cv -> [ valid_read ]
  | FKMethod cv when List.mem Const cv -> [ valid_read ]
  | FKConstructor _ | FKDestructor _ -> [ valid_read ]
  | FKMethod _ | FKCastMethodOperator _ -> [ valid ]
  | FKFunction -> []

let add_separated_arg env acc arg =
  let rec check_class typ =
    match typ, Convert_env.current_struct_or_union env with
      | (Struct (name,ts), (CClass | CStruct)) | Union (name,ts), CUnion
        when Fclang_datatype.Qualified_name.equal
            (name,ts) (Option.get (Convert_env.get_current_class env))
        ->
        let lexpr_loc = Cil_datatype.Location.of_lexing_loc arg.arg_loc in
        let p =
          { lexpr_node =
              PLseparated(
                [ { lexpr_node = PLvar "this"; lexpr_loc };
                  { lexpr_node = PLvar arg.arg_name; lexpr_loc } ]);
            lexpr_loc }
        in
        let pred = toplevel_pred p in
        pred :: acc
      | Named (name,_), _ when Cxx_utils.is_builtin_qual_type name -> acc
      | Named (name,_), _
        -> check_class (Convert_env.get_typedef env name).plain_type
      | _ -> acc
  in
  let rec aux = function
    | LVReference (PDataPointer t)
    | RVReference (PDataPointer t)
    | Pointer (PDataPointer t) ->
      check_class t.plain_type
    | Named (name,_) when Cxx_utils.is_builtin_qual_type name -> acc
    | Named (name,_) -> aux (Convert_env.get_typedef env name).plain_type
    | _ -> acc
  in aux arg.arg_type.plain_type

let add_separated_constructor env args =
  function
    | FKConstructor _ ->
      List.fold_left (add_separated_arg env) [] args
    | FKDestructor _ | FKMethod _ | FKCastMethodOperator _
    | FKFunction -> []

let add_contract
    ~env ~kind ~return_type ~args ~variadic ~implicit ~extern_c spec
    =
  (* not used yet *)
  let () = ignore (variadic,implicit,extern_c) in
  let requires = add_valid_references env args in
  let post_cond = add_valid_result env return_type in
  let requires = add_valid_this env kind @ requires in
  let requires = add_separated_constructor env args kind @ requires in
  if requires <> [] || post_cond <> [] then begin
    match spec with
      | Some (s,_) ->
        (try
           let default =
             List.find (fun b -> b.b_name = Cil.default_behavior_name)
               s.spec_behavior
           in
           default.b_requires <- requires @ default.b_requires;
           default.b_post_cond <- post_cond @ default.b_post_cond;
           spec
         with Not_found ->
           s.spec_behavior <-
             Cabshelper.mk_behavior ~requires ~post_cond () :: s.spec_behavior;
           spec)
      | None ->
        Some
          ({ spec_behavior = [ Cabshelper.mk_behavior ~requires ~post_cond () ];
             spec_variant = None;
             spec_terminates = None;
             spec_complete_behaviors = [];
             spec_disjoint_behaviors = [] },
           Convert_env.get_loc env)
  end else spec
