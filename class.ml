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

open Intermediate_format

module Inheritance_graph =
  Graph.Persistent.Digraph.ConcreteLabeled
    (Fclang_datatype.Qualified_name)
    (struct
      type t = int * access_kind * vkind
      let compare = Stdlib.compare
      let default = (0, Private, VStandard)
     end)

module Inheritance_graph_datatype = 
  Datatype.Make
    (struct
        include Datatype.Undefined
        type t = Inheritance_graph.t
        let name = "Inheritance_graph"
        let reprs = [ Inheritance_graph.empty ]
        let copy = Datatype.identity
        let pretty =
          let module D = Graph.Graphviz.Dot(
            struct
              include Inheritance_graph
              let graph_attributes _ = []
              let default_vertex_attributes _ = []
              let vertex_name s =
                Pretty_utils.to_string Fclang_datatype.Qualified_name.pretty s
              let vertex_attributes _ = []
              let get_subgraph _ = None
              let default_edge_attributes _ = []
              let edge_attributes (_,(o,a,v),_) =
                let a = match a with
                  | Public -> "public"
                  | Private -> "private"
                  | Protected -> "protected"
                in
                let v = match v with
                  | VVirtual -> ",virtual"
                  | VStandard -> ""
                in
                [ `Label (a ^ v ^ "(order: " ^ string_of_int o ^ ")") ]
            end
            ) in
          D.fprint_graph
        let mem_project = Datatype.never_any_project
     end)

module Inheritance_graph_state =
  State_builder.Ref
    (Inheritance_graph_datatype)
    (struct
        let name = "FramaClang.Class.Inheritance_graph"
        let dependencies = [ Kernel.Files.self ]
        let default () = Inheritance_graph.empty
     end)

let inheritance_graph_state = Inheritance_graph_state.self

let add_class c =
  let g = Inheritance_graph_state.get () in
  let g = Inheritance_graph.add_vertex g c
  in Inheritance_graph_state.set g

let add_inheritance_relation c b =
  let g = Inheritance_graph_state.get () in
  let o = Inheritance_graph.out_degree g c + 1 in
  let g =
    Inheritance_graph.add_edge_e g
      (c,(o,b.access,b.is_virtual),(b.base,b.templated_kind))
  in
  Inheritance_graph_state.set g

let get_bases_list derived =
  let g = Inheritance_graph_state.get () in
  let create_inheritance ((_, _), (_, access, is_virtual), (base, t)) =
    { base = base; templated_kind = t; access = access;
      is_virtual = is_virtual; vmt_position = 0 }
  in
  let bases =
    try
      Inheritance_graph.succ_e g derived
    with Invalid_argument _ ->
      []
  in let bases =
    List.sort (fun (_,(o1,_,_),_) (_,(o2,_,_),_) -> compare o1 o2) bases
  in
  List.map create_inheritance bases

let has_virtual_base_class derived =
  let g = Inheritance_graph_state.get () in
  let rec has_virtual_base_class_aux derived = 
    begin
      let does_virtual_inherit acc ((_, _), (_, _, is_virtual), (base, t))
        = if (acc) then acc
          else begin
            match (is_virtual) with 
            | VVirtual -> true
            | VStandard -> (has_virtual_base_class_aux (base, t))
          end
      in let bases =
       try
         Inheritance_graph.succ_e g derived
       with Invalid_argument _ ->
         []
      in List.fold_left does_virtual_inherit false bases
    end
  in has_virtual_base_class_aux derived

let get_virtual_base_classes derived =
  let g = Inheritance_graph_state.get () in
  let rec get_virtual_base_class_aux derived = 
    begin
      let add_virtual_inherit acc ((_, _), (_, _, is_virtual), (base, t))
        = match (is_virtual) with 
            | VVirtual -> (List.append ((base, t)
                :: (get_virtual_base_class_aux (base, t))) acc)
            | VStandard -> (List.append
                (get_virtual_base_class_aux (base, t)) acc)
      in let bases =
       try
         Inheritance_graph.succ_e g derived
       with Invalid_argument _ ->
         []
      in List.fold_left add_virtual_inherit [] bases
    end
  in get_virtual_base_class_aux derived

let dkey = Frama_Clang_option.register_category "inheritance:subtype"

let subtypes base =
  Frama_Clang_option.debug ~dkey
    "Searching for derived classes of %a"
    Fclang_datatype.Qualified_name.pretty base;
  let module Op = Graph.Oper.P(Inheritance_graph) in
  let module T = Graph.Traverse.Bfs(Inheritance_graph) in
  (* the main graph is directed from derived to bases, and we
     want to traverse from bases to derived, hence operate on
     the mirror of the graph
   *)
  let rev = Op.mirror (Inheritance_graph_state.get()) in
  let res = ref Fclang_datatype.Qualified_name.Set.empty in
  let add_elt n =
    Frama_Clang_option.debug ~dkey
      "Found %a" Fclang_datatype.Qualified_name.pretty n;
    if not (Fclang_datatype.Qualified_name.equal n base) then
      res := Fclang_datatype.Qualified_name.Set.add n !res
  in
  T.iter_component add_elt rev base;
  !res

let dkey = Frama_Clang_option.register_category "inheritance:mangled"

let class_of_mangled name =
  Frama_Clang_option.debug ~dkey "Searching for mangled name %s" name;
  let module M =
      struct exception Found of Fclang_datatype.Qualified_name.t end
  in
  try
    Inheritance_graph.iter_vertex
      (fun qual ->
        let mangled = Extlib.uncurry Mangling.mangle qual None in
        Frama_Clang_option.debug ~dkey
          "Class name: %a; Mangled: %s --> %sfound"
          Fclang_datatype.Qualified_name.pretty qual mangled
          (if mangled = name then "" else "not ");
        if mangled = name then raise (M.Found qual))
      (Inheritance_graph_state.get());
    None
    (* if this is not the name of a known C++ class, it has no derived class. *)
  with M.Found base -> Some base

(* NB: is it really useful to maintain a cache of
   the possible inheritance paths? *)
module Inheritance_paths =
  State_builder.Hashtbl
    (Fclang_datatype.Qualified_name.Hashtbl)
    (Fclang_datatype.Qualified_name.Map.Make(
      Datatype.List(
        Datatype.List(
          Datatype.Triple
            (Fclang_datatype.Qualified_name)
            (Datatype.Triple
               (Datatype.Int)
               (Fclang_datatype.Access_kind)(Fclang_datatype.Vkind))
            (Fclang_datatype.Qualified_name)
        ))))
    (struct
        let name = "FramaClang.Class.Inheritance_paths"
        let dependencies = [ Inheritance_graph_state.self ]
        let size = 17
     end)

let add_path map base path =
  let existing =
    try Fclang_datatype.Qualified_name.Map.find base map
    with Not_found -> []
  in
  Fclang_datatype.Qualified_name.Map.add base (path::existing) map

let extend_paths prefix base base_paths map =
  let existing =
    try Fclang_datatype.Qualified_name.Map.find base map
    with Not_found -> []
  in
  let new_paths = List.map (fun p -> prefix :: p) base_paths in
  Fclang_datatype.Qualified_name.Map.add base (existing @ new_paths) map

let find_all_paths derived base =
  let rec aux curr_class =
    try
      Inheritance_paths.find curr_class
    with Not_found ->
      let direct_bases =
        Inheritance_graph.succ_e (Inheritance_graph_state.get()) curr_class
      in
      let curr_paths =
        List.fold_left add_path_direct
          Fclang_datatype.Qualified_name.Map.empty direct_bases
      in
      Inheritance_paths.add curr_class curr_paths;
      curr_paths
  and add_path_direct acc (_, _, direct as edge) =
    let base_inheritance = aux direct in
    let direct_path = add_path acc direct [edge] in
    Fclang_datatype.Qualified_name.Map.fold
      (extend_paths edge) base_inheritance direct_path
  in
  let all_paths = aux derived in
  try
    Fclang_datatype.Qualified_name.Map.find base all_paths
  with Not_found -> []

let has_unambiguous_path derived base =
  match find_all_paths derived base with
    | [] -> false
    | [_] -> true
    | _::_::_ -> false
       (* TODO: checks whether some kind of multiple virtual inheritance
          should be accepted here. *)

let has_public_path derived base =
  let is_public_path p = List.for_all (fun (_,(_,a,_),_) -> a = Public) p in
  List.exists is_public_path (find_all_paths derived base)

exception No_path

let inheritance_path derived base =
  match find_all_paths derived base with
    | [] -> raise No_path
    | p :: _ -> List.map (fun (s,(_,k,v),d) -> (s,(k,v),d)) p
