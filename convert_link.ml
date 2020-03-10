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

open Cil
open Cil_types

let transform_category =
  File.register_code_transformation_category "C++ cleanup"

let exn_dkey = Frama_Clang_option.register_category "exn:inherit"

let find_comp name =
  try 
    (match Globals.Types.find_type Logic_typing.Struct name with
      | TComp(c,_,_) -> c
      | _ ->
        Frama_Clang_option.fatal "unexpected type returned for struct %s" name)
  with Not_found ->
    Frama_Clang_option.fatal
      "Did not find struct for mangled class name %s" name

let rec coerce lv comp path =
  match path with
    | [] -> lv
    | (_,_,direct_base) :: path ->
      let cname = Extlib.uncurry Mangling.mangle direct_base None in
      let fname =
        Extlib.uncurry 
          (Convert.create_base_field_name Convert_env.empty_env) direct_base
      in
      let field = Cil.getCompField comp fname in
      let new_lv = Cil.addOffsetLval (Field (field, NoOffset)) lv in
      let new_comp = find_comp cname in
      coerce new_lv new_comp path

(* all the names in catch should avoid typedefs except builtin ones *)
let add_subtypes kf = function
  | Catch_all -> Catch_all
  | Catch_exn(vi,l) as bind ->
    let loc = vi.vdecl in
    (match (Cil.unrollType vi.vtype) with
      | TComp({ corig_name = base },_,_) as base_struct ->
        let qualified_base = Class.class_of_mangled base in
        (match qualified_base with
          | Some qualified_base ->
            let derived = Class.subtypes qualified_base in
            (* if there is no derived class, we can keep a plain clause. *)
            if Fclang_datatype.Qualified_name.Set.is_empty derived then bind
            else begin
                (* add all inherited classes as auxiliary catch binders.
                   Do not forget to also add the base class itself. *)
              let f = Kernel_function.get_definition kf in
              File.must_recompute_cfg f;
              Ast.mark_as_grown ();
              let base_block = Cil.mkBlock [] in
              let base_vi =
                Cil.makeTempVar
                  f ~insert:false ~name:(vi.vname ^ "_0") base_struct
              in
              f.slocals <- base_vi :: f.slocals;
              (* TODO: use the appropriate copy constructor instead *)
              let copy =
                Cil.mkStmtOneInstr
                  ~valid_sid:true
                  (Set ((Var vi, NoOffset),Cil.evar ~loc base_vi, loc))
              in
              base_block.bstmts <- [copy];
              let binders = (base_vi, base_block) :: l in
              let treat_one_derived c (i, binders as acc) =
                if Class.has_unambiguous_path c qualified_base
                  && Class.has_public_path c qualified_base
                then begin
                  Frama_Clang_option.debug ~dkey:exn_dkey
                    "Adding derived catch clause for %a from %a"
                    Fclang_datatype.Qualified_name.pretty c
                    Fclang_datatype.Qualified_name.pretty qualified_base;
                  let path = Class.inheritance_path c qualified_base in
                  let block = Cil.mkBlock [] in
                  let mangled = Extlib.uncurry Mangling.mangle c None in
                  let struct_info = find_comp mangled in
                  let my_vi =
                    Cil.makeTempVar f
                      ~insert:false
                      ~name:(vi.vname ^ "_" ^ (string_of_int i))
                      (TComp (struct_info, { scache = Not_Computed }, []))
                  in
                  f.slocals <- my_vi :: f.slocals;
                  let lv = coerce (Cil.var my_vi) struct_info path in
                  let e = Cil.new_exp ~loc (Lval lv) in
                  let copy =
                    Cil.mkStmtOneInstr (Set ((Var vi,NoOffset),e,loc)) in
                  block.bstmts <- [copy];
                  (i+1,(my_vi, block) :: binders)
                end else acc
              in
              let _,binders =
                Fclang_datatype.Qualified_name.Set.fold 
                  treat_one_derived derived (1,binders)
              in
              Catch_exn(vi,binders)
            end
          | None -> bind)
      | _ -> bind)

class clean =
  object(self)
    inherit Visitor.frama_c_inplace

    method! vstmt_aux s =
      match s.skind with
        | TryCatch(t,c,l) ->
          let c =
            List.map
              (fun (bind, body) ->
                add_subtypes (Extlib.the self#current_kf) bind, body)
              c
          in
          s.skind <- TryCatch(t,c,l);
          DoChildren
        | Instr (
            Call (
              None,
              { enode = Lval (Var f, NoOffset) },
              { enode =
                  (AddrOf (Var o, NoOffset)
                  | CastE (_, { enode = AddrOf (Var o, NoOffset)}))}
              :: args,
              loc))
          when Mangling.is_constructor_name f.vname
            && not o.vglob && not o.vformal ->
          let init = ConsInit (f,args,Constructor) in
          o.vdefined <- true;
          s.skind <- Instr (Local_init(o,init,loc));
          DoChildren
        | _ -> DoChildren
  end

let clean_whole_program file =
  Visitor.visitFramacFileSameGlobals (new clean) file

let register_transformation () =
  File.add_code_transformation_after_cleanup
    ~deps:[]
    ~before:[Exn_flow.transform_category]
    transform_category
    clean_whole_program
