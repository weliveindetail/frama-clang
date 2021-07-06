open Cabs

let dkey = Frama_Clang_option.dkey_reorder

type kind = Enum | Struct | Union | Typedef | Id | Field | Other

let string_of_kind = function
  | Enum -> "enum"
  | Struct -> "struct"
  | Union -> "union"
  | Typedef -> "typedef"
  | Field -> "field"
  | Id -> ""
  | Other -> "OTHER"

type dep_node =
  {
    kind: kind;
    name: string;
    is_def: bool;
    mutable glob: definition option;
    mutable ghost: bool; (* TODO: take ghost into account. *)
    mutable id: int
  }

let print_node fmt n =
  Format.fprintf fmt "%s %s (id %d, defined: %B)"
    (string_of_kind n.kind) n.name n.id n.is_def

module Dep_node = struct
  type t = dep_node

  let compare x y =
    if x.id = -1 || y.id = -1 then begin
      let res = Pervasives.compare x.kind y.kind in
      if res = 0 then begin
        let res = Pervasives.compare x.name y.name in
        if res = 0 then Pervasives.compare x.is_def y.is_def else res
      end else res
    end else begin
      let res = compare y.id x.id in
      if res <> 0 then res
      else if x.is_def = y.is_def then 0
      else if y.is_def then 1 else -1
    end

  let hash x = Hashtbl.(hash x.kind + 3 * hash x.name + 5 * hash x.is_def)

  let equal x y = compare x y = 0
end

let find_type_specifier l =
  match List.find_opt (function SpecType _ -> true | _ -> false) l with
  | None -> Frama_Clang_option.fatal "ill-formed type definition"
  | Some (SpecType t) -> t
  | Some _ -> assert false

let kind_of_glob = function
  | FUNDEF _ | DECDEF _ -> Id
  | TYPEDEF _  -> Typedef
  | ONLYTYPEDEF (l,_) ->
    (match find_type_specifier l with
     | Tstruct _ -> Struct
     | Tunion _ -> Union
     | Tenum _ -> Enum
     | _ -> Other)
  (* TODO: find dependencies also in GLOBANNOT... *)
  | GLOBASM _ | PRAGMA _ | LINKAGE _ | GLOBANNOT _ | CUSTOM _ -> Other

let name_of_glob d = match d with
  | FUNDEF(_,(_,(name,_,_,_)),_,_,_) -> name
  | DECDEF(_,(_,((name,_,_,_),_)::_),_) -> name
  | DECDEF _ ->
    Frama_Clang_option.fatal "Empty object declaration: %a"
      Cabs_debug.pp_def d
  | TYPEDEF((_,((name,_,_,_)::_)),_) -> name
  | TYPEDEF _ ->
    Frama_Clang_option.fatal "Empty type declaration: %a"
      Cabs_debug.pp_def d
  | ONLYTYPEDEF (l,_) ->
    (match find_type_specifier l with
     | Tstruct(s,_,_) -> s
     | Tunion(s,_,_) -> s
     | Tenum (s,_,_) -> s
     | _ ->
       Frama_Clang_option.fatal "Unknown type declaration: %a"
         Cabs_debug.pp_def d
    )
  | GLOBASM _ | PRAGMA _ | LINKAGE _ | GLOBANNOT _ | CUSTOM _ -> ""

let has_init = List.exists (function (_,NO_INIT) -> false | _ -> true)

let glob_is_def = function
  | FUNDEF _ -> true
  | DECDEF (_,(_,l),_) -> has_init l
  | TYPEDEF _ -> true
  | ONLYTYPEDEF (l,_) ->
    (match find_type_specifier l with
     | Tstruct(_,Some _,_) -> true
     | Tstruct(_,None,_) -> false
     | Tunion(_,Some _,_) -> true
     | Tunion(_,None,_) -> false
     | Tenum(_,Some _,_) -> true
     | Tenum(_,None,_) -> false
     | _ -> false)
  | GLOBASM _ | PRAGMA _ | LINKAGE _ | GLOBANNOT _ | CUSTOM _ -> false

let decl_of_def = function
  | FUNDEF (_,(s,n),_,b,_) -> DECDEF(None,(s,[n,NO_INIT]),b)
  | DECDEF(_,(s,l),loc) ->
    let erase_init (n,_) = (n, NO_INIT) in
    DECDEF(None,(s, List.map erase_init l),loc)
  | ONLYTYPEDEF(l,loc) ->
    let erase_def s =
      match s with
      | SpecType (Tstruct(n,_,_)) -> SpecType (Tstruct(n,None,[]))
      | SpecType (Tunion(n,_,_)) -> SpecType (Tunion(n, None,[]))
      | SpecType (Tenum(n,_,_)) -> SpecType (Tenum(n, None,[]))
      | _ -> s
    in
    ONLYTYPEDEF(List.map erase_def l, loc)
  | d -> d

let is_decl_with_spec = function
  | DECDEF (Some _, _, _) -> true
  | _ -> false

module Dependencies: sig
  val find_symbol: kind -> string -> bool -> Dep_node.t
  val set_symbol: kind -> string -> bool -> Dep_node.t -> unit
  val get_glob_node: definition -> Dep_node.t
  val add_dependency: Dep_node.t -> Dep_node.t -> unit
  (* whether the current graph has a definition in all its nodes. *)
  val is_complete: unit -> bool

  (* whether there is a dependency cycle in the current graph. *)
  val has_cycle: unit -> bool

  (* print nodes for which we don't have a definition yet. *)
  val print_missing: Format.formatter -> unit

  (* gives back the list of all globals in dependencies order.
     Only meaningful for a complete graph. Attempt to keep original order
     in which definitions have been provided to get_glob_node.
  *)
  val emit_deps: (bool * definition) list -> (bool * definition) list
end = struct
  module G = Graph.Imperative.Digraph.Concrete(Dep_node)

  module H = Hashtbl.Make(Dep_node)

  let deps = G.create ()

  let nodes = H.create 37

  let default_node kind name is_def =
    { kind; name; is_def; glob = None; id = -1; ghost = false }

  let replace_deps orig rep =
    if G.mem_vertex deps orig then begin
      G.add_vertex deps rep;
      List.iter (fun p -> G.add_edge deps p rep) (G.pred deps orig);
      List.iter (fun s -> G.add_edge deps rep s) (G.succ deps orig);
      G.remove_vertex deps orig
    end

  let find_symbol kind name is_def =
    let default = default_node kind name is_def in
    let add_new () =
      H.add nodes default default; G.add_vertex deps default; default
    in
    match H.find_opt nodes default with
    | Some node -> node
    | None ->
      if not is_def then begin
        match H.find_opt nodes (default_node kind name true) with
        | Some node -> node
        | None -> add_new ()
      end else add_new ()

  let set_symbol kind name is_def rep =
    let default = default_node kind name is_def in
    Frama_Clang_option.debug ~dkey "Choosing representative for %a -> %a"
      print_node default print_node rep;
    replace_deps default rep;
    H.add nodes default rep


   let get_glob_node =
    let id = ref 0 in
    fun d ->
      let kind = kind_of_glob d in
      let name = name_of_glob d in
      let is_def = glob_is_def d in
      let node = find_symbol kind name is_def in
      if node.id = -1 then begin
        node.glob <- Some d;
        node.id <- !id;
        Frama_Clang_option.debug ~dkey "Adding node %a@." print_node node;
        if is_def && kind <> Typedef then begin
          let d = decl_of_def d in
          let dec_node = default_node kind name false in
          match H.find_opt nodes dec_node with
          | Some ({ glob = None; is_def = false } as node)->
            (* we need the declaration somewhere before this point. Generate it
               so that we don't move all dependencies of the body as well. *)
            node.glob <- Some d;
            node.id <- !id
          | Some _ -> () (* we already have a proper declaration *)
          | None -> H.add nodes dec_node node
          (* no need to move the declaration independently
             from the definition. *)
        end;
        incr id;
        node
      end else if is_decl_with_spec d then begin
        (* keep a lonely node to avoid losing the spec. *)
        let node = default_node kind name is_def in
        node.glob <- Some d;
        node.id <- !id;
        incr id;
        node
      end else node

  let add_dependency src dest = if src != dest then G.add_edge deps src dest

  let is_complete () =
    let has_def node ok = ok && node.glob <> None in
    G.fold_vertex has_def deps true

  let has_cycle () =
    let module T = Graph.Traverse.Dfs(G) in T.has_cycle deps

  let print_missing fmt =
    let print_one n =
      if n.glob = None then Format.fprintf fmt "%a@\n" print_node n
    in
    G.iter_vertex print_one deps

  let emit_deps l =
    let emitted = H.create 37 in
    let l = List.map (fun (ghost, def) -> ghost, def, None) l in
    let rec add_dep res wlist =
      match wlist with
      | [] -> List.rev res
      | (ghost, def, node) :: wtail ->
        let node =
          match node with
          | None -> get_glob_node def
          | Some n -> n
        in
        if node.kind = Other || not (G.mem_vertex deps node) then
          (* we don't treat these kind of nodes. Just let them stay
             at their current place. *)
          add_dep ((ghost,def) :: res) wtail
        else begin
          if H.mem emitted node then add_dep res wtail
          else
            let preds = G.pred deps node in
            let preds = List.filter (fun x -> not (H.mem emitted x)) preds in
            match preds with
            | [] ->
              H.add emitted node ();
              add_dep ((ghost, def) :: res) wtail
            | _ ->
              let defs =
                List.map
                  (fun n ->
                     Frama_Clang_option.debug
                       ~dkey "Need to move %a before %a"
                       print_node n print_node node;
                     (false, Extlib.the n.glob, Some n))
                  preds
              in
              add_dep res (defs @ wlist)
          end
    in add_dep [] l
end

(* rough idea of the algorithm: maintain
   correspondance between symbol name (+decl/def status) and node number.
   Needs introducing nodes not
   related yet to a definition for forward references.
   For field accesses (but also variables defined by the same definition,
   as this is allowed in Cabs), this means potentially having
   several nodes for the same definition. Note that in addition, the same field
   name might be shared by several structs. An idea to keep track of these
   dependencies is to put a def-dependencies to all structs/union for which
   we have already a decl-dependency as soon as we see a dereference to a field.
   This must be done transitively across typedefs. Arrows must be decorated
   with the field name so that we know which dependencies we can safely make
   decl again when we see an actual definition for the struct.
   We collapse nodes as needed so that all symbols concerned by a given
   definition maps to a single node (see if there's a mean to that in
   ocamlgraph directly). In the end, there should be a one-to-one mapping
   between definitions and node (via the names defined by the definition).
   We also store the pragma states for the pragmas
   we care about for each definition. After the visit to put all dependencies
   in place, we iter over each definition, and maintain a table of the
   definitions we have put so far in the result. For each definition,
   we check whether all its dependencies are already in. If not, we add the
   appropriate dependencies, in appropriate order (the decl/def dependencies
   should guarantee us that there's no cycle). For each dependency thus added,
   we also introduce appropriate pragmas to ensure a correct context for
   the dependencies and for the rest of the code (i.e. restoring pragmas
   environment afterwards).
*)

class compute_deps =
  let open Cil in
  let is_global s = Extlib.string_prefix ~strict:true "_Z" s in
  object(self)
    inherit Cabsvisit.nopCabsVisitor

    val mutable current_def = None

    method private add_deps node =
      Dependencies.add_dependency node (Extlib.the current_def)

    method! vtypespec = function
      | Tstruct (s,_,_) ->
        self#add_deps (Dependencies.find_symbol Struct s false);
        DoChildren
      | Tunion (s,_,_) ->
        self#add_deps (Dependencies.find_symbol Union s false);
        DoChildren
      | Tenum (s,_,_) ->
        self#add_deps (Dependencies.find_symbol Enum s false);
        DoChildren
      | Tnamed s when s <> "__builtin_va_list" ->
        self#add_deps (Dependencies.find_symbol Typedef s false);
        DoChildren
      | _ -> DoChildren

    method! vexpr = function
      | { expr_node = MEMBEROF(_,name) | MEMBEROFPTR(_,name) } ->
        (* TODO: handle field name clashes. *)
        self#add_deps (Dependencies.find_symbol Field name false);
        DoChildren
      | _ -> DoChildren

    method! vvar s =
      if is_global s then begin
        self#add_deps (Dependencies.find_symbol Id s false);
      end;
      s

    method private add_tag_field_def = function
      | ONLYTYPEDEF (l,_) ->
        (match find_type_specifier l with
         | Tenum(_, Some tags,_) ->
           let process_tag (name,_,_) =
             Dependencies.set_symbol Id name false (Extlib.the current_def)
           in
           List.iter process_tag tags
         | Tstruct(_, Some l, _) | Tunion(_, Some l, _) ->
           let process_tag =
             function
             | FIELD(_,l) ->
               let process_name ((n,_,_,_),_) =
                 Dependencies.set_symbol Field n false (Extlib.the current_def)
               in
               List.iter process_name l
             | TYPE_ANNOT _ -> ()
           in
           List.iter process_tag l
         | _ -> ())
      | _ -> ()

    method! vdef d =
      let is_def = glob_is_def d in
      let kind = kind_of_glob d in
      if current_def = None then begin
        let node = Dependencies.get_glob_node d in
        if is_def && kind <> Typedef then begin
          ignore
            (Cabsvisit.visitCabsDefinition
               (self:>Cabsvisit.cabsVisitor)
               (decl_of_def d))
        end;
        current_def <- Some node;
        self#add_tag_field_def d;
        DoChildrenPost (fun d -> current_def <- None; d)
      end else DoChildren
  end

let reorder file =
  ignore (Cabsvisit.visitCabsFile (new compute_deps) file);
  if not (Dependencies.is_complete()) then
    Frama_Clang_option.fatal "could not find all needed definitions:@\n%t"
      Dependencies.print_missing;
  if Dependencies.has_cycle () then
    Frama_Clang_option.fatal
      "cannot reorder global definitions: dependencies cycle";
  (fst file, Dependencies.emit_deps (snd file))
