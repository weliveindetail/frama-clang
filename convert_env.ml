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

type aggregate_info =
  { fields: (string * qual_type) list;
    has_virtual: bool;
    default_constructor: (qualified_name * signature) option;
    default_constructor_base: (qualified_name * signature) option;
    copy_constructor: (qualified_name * signature) option;
    copy_constructor_base: (qualified_name * signature) option;
    move_constructor: (qualified_name * signature) option;
    move_constructor_base: (qualified_name * signature) option;
    assign_operator: (qualified_name * signature) option;
    assign_operator_base: (qualified_name * signature) option;
    move_operator: (qualified_name * signature) option;
    move_operator_base: (qualified_name * signature) option;
    destructor: bool;
    destructor_base: bool;
  }

type env =
  { namespace: qualification list list;
    location: Cabs.cabsloc;
    local_vars: typ Datatype.String.Map.t;
    captured_vars: bool Datatype.String.Map.t list;
    global_vars: (bool * typ) Fclang_datatype.Qualified_name.Map.t;
    is_extern_c: bool;
    is_ghost: bool;
    current_func_name: qualified_name;
    current_return_type: typ;
    current_class: Fclang_datatype.Qualified_name.t list;
    typedefs: qual_type Fclang_datatype.Qualified_name.Map.t;
    structs: aggregate_info Fclang_datatype.Qualified_name.Map.t;
    aggregate_kind: (ckind * bool) Fclang_datatype.Qualified_name.Map.t;
    c_globals: (bool * Cabs.definition) list;
  }

let empty_aggregate_info =
  { fields = [];
    default_constructor = None; default_constructor_base = None;
    copy_constructor = None; copy_constructor_base = None;
    has_virtual = false;
    move_constructor = None; move_constructor_base = None;
    move_operator = None; move_operator_base = None;
    assign_operator = None; assign_operator_base = None;
    destructor = false; destructor_base = false;
  }

let empty_func_name =
  { prequalification = []; decl_name = "#### Not in a function ####" }
let empty_return_type =
  Named ({prequalification=[]; decl_name = "###Illegal type" }, true)

let empty_env =
  { namespace = [];
    location = Cil_datatype.Location.unknown;
    local_vars = Datatype.String.Map.empty;
    captured_vars = [];
    global_vars = Fclang_datatype.Qualified_name.Map.empty;
    is_extern_c = false;
    is_ghost = false;
    current_func_name = empty_func_name;
    current_return_type = empty_return_type;
    typedefs = Fclang_datatype.Qualified_name.Map.empty;
    structs = Fclang_datatype.Qualified_name.Map.empty;
    aggregate_kind = Fclang_datatype.Qualified_name.Map.empty;
    current_class = [];
    c_globals = [];
  }

let add_c_global env def =
  { env with c_globals = (env.is_ghost, def) :: env.c_globals }

let get_c_globals env = List.rev env.c_globals

let fatal env msg =
  let source = fst env.location in
  Frama_Clang_option.fatal ~source msg

let get_namespace { namespace } =
  match namespace with [] -> [] | inner :: _ -> inner

let add_namespace env n =
  let inner_namespace = get_namespace env @ [n] in
  { env with namespace = inner_namespace :: env.namespace }

let set_namespace env n =
  { env with namespace = n.prequalification :: env.namespace }

let set_namespace_from_class env (n,t) =
  let inner_namespace =
    match t with
    | TStandard -> n.prequalification @ [QStructOrClass n.decl_name]
    | TTemplateInstance l ->
      n.prequalification @ [QTemplateInstance (n.decl_name,l)]
  in
  { env with namespace = inner_namespace :: env.namespace }

let reset_namespace env =
  match env.namespace with [] -> env | _ :: namespace -> { env with namespace }

let add_local_var env v t =
  { env with
    local_vars = Datatype.String.Map.add v t env.local_vars }

let unscope env previous = { env with local_vars = previous.local_vars }

let add_formal_parameters env args =
  List.fold_left
    (fun env arg -> add_local_var env arg.arg_name arg.arg_type.plain_type)
    env args

let add_global_var env v t =
  (* Format.printf "add global var %a\n" Fclang_datatype.Qualified_name.pretty (v, TStandard); *)
  { env with
    global_vars =
      Fclang_datatype.Qualified_name.Map.add
        (v,TStandard) (env.is_extern_c,t) env.global_vars }

let get_local_var env v =
  try
    Datatype.String.Map.find v env.local_vars
  with Not_found ->
    fatal env "Unknown local variable %s" v

let get_global_var env v =
  try
    Fclang_datatype.Qualified_name.Map.find (v,TStandard) env.global_vars
  with Not_found ->
    fatal env "Unknown global variable %a"
      Fclang_datatype.Qualified_name.pretty (v,TStandard)

let temp_name env s =
  let rec aux i =
    let name = s ^ "_" ^ string_of_int i in
    if Datatype.String.Map.mem name env.local_vars then aux (i+1) else name
  in
  if Datatype.String.Map.mem s env.local_vars then aux 0 else s

let set_loc env loc =
  let loc = Cil_datatype.Location.of_lexing_loc loc in
  Cil.CurrentLoc.set loc; { env with location = loc }

let get_loc env = env.location

let get_clang_loc env = Cil_datatype.Location.to_lexing_loc env.location

let set_extern_c env flag = { env with is_extern_c = flag }

let is_extern_c env = env.is_extern_c

let set_ghost env flag = { env with is_ghost = flag }

let is_ghost env = env.is_ghost

let qualify env n =
  let prequalification = get_namespace env in
  { prequalification; decl_name = n }

let get_current_class env =
  match env.current_class with [] -> None | hd :: _ -> Some hd

let set_current_class env c =
  let env = set_namespace_from_class env c in
  { env with current_class = c :: env.current_class }

let reset_current_class env =
  let current_class =
    match env.current_class with [] -> [] | _ :: tl -> tl
  in
  reset_namespace { env with current_class }

let class_name_from_qualifications env l =
  let rec aux acc l =
    match l with
      | [] -> None
      | [QStructOrClass n]
        -> Some ({ prequalification = List.rev acc; decl_name = n }, TStandard)
      | [ QNamespace _ ] -> None
      | [ QTemplateInstance(n,tl) ] ->
        let name =
          ({ prequalification = List.rev acc; decl_name = n },
           TTemplateInstance tl)
        in
        if Fclang_datatype.Qualified_name.Map.mem name env.aggregate_kind
        then Some name
        else None
      | a :: l -> aux (a::acc) l
  in aux [] l

let set_class_from_qual env name =
  match name.prequalification with
  | [] -> env
  | l ->
    (match class_name_from_qualifications env l with
     | None -> set_namespace env name
     | Some class_name -> set_current_class env class_name)

let reset_class_from_qual env name =
  match name.prequalification with
  | [] -> env
  | l ->
    (match class_name_from_qualifications env l with
     | None -> reset_namespace env
     | Some _ -> reset_current_class env)

let set_current_func_name env name =
  let env = { env with current_func_name = name } in
  set_class_from_qual env name

let reset_func env =
  let new_env =
    { env with
      current_func_name = empty_func_name;
      current_return_type = empty_return_type }
  in
  reset_class_from_qual new_env env.current_func_name

let get_current_func_name env = env.current_func_name.decl_name

let set_current_return_type env typ =
  { env with current_return_type = typ }

let get_current_return_type env = env.current_return_type

let add_typedef env name qtype =
  { env with typedefs =
    Fclang_datatype.Qualified_name.Map.add (name,TStandard) qtype env.typedefs}

let get_typedef env name =
  try
    Fclang_datatype.Qualified_name.Map.find (name,TStandard) env.typedefs
  with Not_found ->
    fatal env "Unknown typedef %a"
      Fclang_datatype.Qualified_name.pretty (name,TStandard)

let has_typedef env name =
  Fclang_datatype.Qualified_name.Map.mem (name, TStandard) env.typedefs

let rec template_parameter_normalize env tparam = match tparam with
  | TPStructOrClass name -> TPStructOrClass
    { name with prequalification
        = qualification_list_normalize env name.prequalification }
  | TPTypename qtype -> TPTypename (qual_type_normalize env qtype)
  | TPConstant _ -> tparam
  | TPDeclaration name -> TPDeclaration
    { name with prequalification
        = qualification_list_normalize env name.prequalification }
and qualification_normalize env qual = match qual with
  | QTemplateInstance (name, params)
  -> QTemplateInstance(name, List.map (template_parameter_normalize env) params)
  | _ -> qual
and qualification_list_normalize env lqual = match lqual with
  | [] -> []
  | qual::lqual ->
      (qualification_normalize env qual)
        :: (qualification_list_normalize env lqual)
and tkind_normalize env tk = match tk with
  | TStandard -> tk
  | TTemplateInstance ltparams
    -> TTemplateInstance (List.map (template_parameter_normalize env) ltparams)
and signature_normalize env sign =
  { result = qual_type_normalize env sign.result;
    parameter = qual_type_list_normalize env sign.parameter;
    variadic = sign.variadic
  }
and pkind_normalize env pk = match pk with
  | PDataPointer qtype -> PDataPointer (qual_type_normalize env qtype)
  | PFunctionPointer sign -> PFunctionPointer (signature_normalize env sign)
  | PStandardMethodPointer (decl, shift)
    -> PStandardMethodPointer (signature_normalize env decl, shift)
  | PVirtualMethodPointer (decl, index, shift)
    -> PVirtualMethodPointer (signature_normalize env decl, index, shift)
and qual_type_normalize env qtype = match qtype.plain_type with
  | Pointer kind
    -> { qtype with plain_type = Pointer (pkind_normalize env kind) }
  | LVReference kind ->
      { qtype with plain_type = LVReference (pkind_normalize env kind) }
  | RVReference kind ->
      { qtype with plain_type = RVReference (pkind_normalize env kind) }
  | Array kind -> { qtype with plain_type = Array
    { kind with subtype = qual_type_normalize env kind.subtype } }
  | Struct (body, tk) -> { qtype with plain_type
      = Struct({ body with prequalification
                   = qualification_list_normalize env body.prequalification },
               tkind_normalize env tk) }
  | Union (body, tk) -> { qtype with plain_type
      = Union({ body with prequalification
                   = qualification_list_normalize env body.prequalification },
               tkind_normalize env tk) }
  | Named (qname,is_extern_c) ->
    begin
      try
        let def =
          Fclang_datatype.Qualified_name.Map.find (qname,TStandard) env.typedefs
        in
        let qtype = Cxx_utils.add_qualifiers qtype.qualifier def in
        qual_type_normalize env qtype
      with Not_found ->
        { qtype with plain_type = Named
          ({ qname with prequalification
              = qualification_list_normalize env qname.prequalification },
           is_extern_c) }
    end
  | _ -> qtype
and qual_type_list_normalize env ltype = match ltype with
  | [] -> []
  | qtype::ltype ->
      (qual_type_normalize env qtype)
        :: (qual_type_list_normalize env ltype)

let typedef_normalize env name tk =
  { name with prequalification
         = qualification_list_normalize env name.prequalification },
  (tkind_normalize env tk)

let add_struct env (name,t) fields =
  let info =
    try
      Fclang_datatype.Qualified_name.Map.find (name,t) env.structs
    with Not_found -> empty_aggregate_info
  in
  let info = { info with fields = fields } in
  { env with structs =
      Fclang_datatype.Qualified_name.Map.add (name,t) info env.structs
  }

let virtual_struct env (name, t) =
  let info =
    try
      Fclang_datatype.Qualified_name.Map.find (name, t) env.structs
    with Not_found -> empty_aggregate_info
  in
  let info = { info with has_virtual = true } in
  { env with
    structs = Fclang_datatype.Qualified_name.Map.add (name, t) info env.structs}

let get_struct env (name,t) =
  try
    (Fclang_datatype.Qualified_name.Map.find (name,t) env.structs).fields
  with Not_found ->
    fatal env "Unknown struct %a"
      Fclang_datatype.Qualified_name.pretty (name,t)

let struct_has_virtual env full_name =
  try
    (Fclang_datatype.Qualified_name.Map.find full_name env.structs).has_virtual
  with Not_found ->
    fatal env "Unknown struct %a"
      Fclang_datatype.Qualified_name.pretty full_name

let aggregate_info err env name =
  try
    Fclang_datatype.Qualified_name.Map.find name env.structs
  with Not_found ->
    if err then
      fatal env "Unknown aggregate_type %a"
        Fclang_datatype.Qualified_name.pretty name
    else empty_aggregate_info

let force_class_name env quals =
  match class_name_from_qualifications env quals with
  | None ->
    Frama_Clang_option.fatal
      "this function must be called inside the scope of a class"
  | Some name -> name

let add_default_constructor env name signature =
  let full_name = force_class_name env name.prequalification in
  let info = aggregate_info false env full_name in
  let info =
    match info.default_constructor with
      | None -> { info with default_constructor = Some (name,signature) }
      | Some _ -> info
  in
  { env with
    structs =
      Fclang_datatype.Qualified_name.Map.add full_name info env.structs }

let add_default_constructor_base env name signature =
  let full_name = force_class_name env name.prequalification in
  let info = aggregate_info false env full_name in
  let info =
    match info.default_constructor_base with
      | None -> { info with default_constructor_base = Some (name,signature) }
      | Some _ -> info
  in
  { env with
    structs =
      Fclang_datatype.Qualified_name.Map.add full_name info env.structs }

let get_option_default_constructor env name =
  let info = aggregate_info true env name in info.default_constructor

let get_option_default_constructor_base env name =
  let info = aggregate_info true env name in info.default_constructor_base

let get_default_constructor env name =
  match get_option_default_constructor env name with
    | None ->
        fatal env "No usable default constructor for %a"
          Fclang_datatype.Qualified_name.pretty name
    | Some cons -> cons

let add_copy_constructor env name signature =
  let full_name = force_class_name env name.prequalification in
  let info = aggregate_info false env full_name in
  let info =
    match info.copy_constructor with
      | None -> { info with copy_constructor = Some (name,signature) }
      | Some _ -> info
  in
  { env
    with structs =
      Fclang_datatype.Qualified_name.Map.add full_name info env.structs }

let add_copy_constructor_base env name signature =
  let full_name = force_class_name env name.prequalification in
  let info = aggregate_info false env full_name in
  let info =
    match info.copy_constructor_base with
      | None -> { info with copy_constructor_base = Some (name,signature) }
      | Some _ -> info
  in
  { env
    with structs =
      Fclang_datatype.Qualified_name.Map.add full_name info env.structs }

let get_option_copy_constructor env name =
  let info = aggregate_info true env name in info.copy_constructor

let get_option_copy_constructor_base env name =
  let info = aggregate_info true env name in info.copy_constructor_base

let get_copy_constructor env name =
  match get_option_copy_constructor env name with
    | Some c -> c
    | None ->
        fatal env "No usable copy constructor for %a"
          Fclang_datatype.Qualified_name.pretty name

let add_move_constructor env name signature =
  let full_name = force_class_name env name.prequalification in
  let info = aggregate_info false env full_name in
  let info =
    match info.move_constructor with
      | None -> { info with move_constructor = Some (name,signature) }
      | Some _ -> info
  in
  { env
    with structs =
      Fclang_datatype.Qualified_name.Map.add full_name info env.structs }

let add_move_constructor_base env name signature =
  let full_name =  force_class_name env name.prequalification in
  let info = aggregate_info false env full_name in
  let info =
    match info.move_constructor_base with
      | None -> { info with move_constructor_base = Some (name,signature) }
      | Some _ -> info
  in
  { env
    with structs =
      Fclang_datatype.Qualified_name.Map.add full_name info env.structs }

let get_option_move_constructor env name =
  let info = aggregate_info true env name in info.move_constructor

let get_option_move_constructor_base env name =
  let info = aggregate_info true env name in info.move_constructor_base

let get_move_constructor env name =
  match get_option_move_constructor env name with
    | Some c -> c
    | None ->
        fatal env "No usable move constructor for %a"
          Fclang_datatype.Qualified_name.pretty name

let add_destructor env name =
  let full_name = force_class_name env name in
  let info = aggregate_info false env full_name in
  let info =
    if not(info.destructor) then { info with destructor = true } else info
  in
  { env with
    structs =
      Fclang_datatype.Qualified_name.Map.add full_name info env.structs }

let add_destructor_base env name =
  let full_name = force_class_name env name in
  let info = aggregate_info false env full_name in
  let info =
    if not(info.destructor_base) then
      { info with destructor_base = true }
    else info
  in
  { env with
    structs =
      Fclang_datatype.Qualified_name.Map.add full_name info env.structs }

let has_destructor env class_name =
    let info = aggregate_info true env class_name in info.destructor

let has_destructor_base env class_name =
    let info = aggregate_info true env class_name in info.destructor_base

let add_assign_operator env name signature =
  let full_name = force_class_name env name.prequalification in
  let info = aggregate_info false env full_name in
  let info =
    match info.assign_operator with
      | None -> { info with assign_operator = Some (name,signature) }
      | Some _ -> info
  in
  { env with
    structs =
      Fclang_datatype.Qualified_name.Map.add full_name info env.structs }

let add_assign_operator_base env name signature =
  let full_name = force_class_name env name.prequalification in
  let info = aggregate_info false env full_name in
  let info =
    match info.assign_operator_base with
      | None -> { info with assign_operator_base = Some (name,signature) }
      | Some _ -> info
  in
  { env with
    structs =
      Fclang_datatype.Qualified_name.Map.add full_name info env.structs }

let get_option_assign_operator env name =
  let info = aggregate_info true env name in info.assign_operator

let get_option_assign_operator_base env name =
  let info = aggregate_info true env name in info.assign_operator_base

let get_assign_operator env name =
  match get_option_assign_operator env name with
    | None -> 
        fatal env "No usable assign operator for %a"
          Fclang_datatype.Qualified_name.pretty name
    | Some a -> a

let add_move_operator env name signature =
  let full_name = force_class_name env name.prequalification in
  let info = aggregate_info false env full_name in
  let info =
    match info.move_operator with
      | None -> { info with move_operator = Some (name,signature) }
      | Some _ -> info
  in
  { env
    with structs =
      Fclang_datatype.Qualified_name.Map.add full_name info env.structs }

let add_move_operator_base env name signature =
  let full_name = force_class_name env name.prequalification in
  let info = aggregate_info false env full_name in
  let info =
    match info.move_operator_base with
      | None -> { info with move_operator_base = Some (name,signature) }
      | Some _ -> info
  in
  { env
    with structs =
      Fclang_datatype.Qualified_name.Map.add full_name info env.structs }

let get_option_move_operator env name =
  let info = aggregate_info true env name in info.move_operator

let get_option_move_operator_base env name =
  let info = aggregate_info true env name in info.move_operator_base

let get_move_operator env name =
  match get_option_move_operator env name with
    | None ->
        fatal env "No usable move operator for %a"
          Fclang_datatype.Qualified_name.pretty name
    | Some a -> a

let add_aggregate env name kind tc extern_c =
  { env with aggregate_kind =
      Fclang_datatype.Qualified_name.Map.add
        (name,tc) (kind,extern_c) env.aggregate_kind }

let get_aggregate env (name,t) =
  try
    Fclang_datatype.Qualified_name.Map.find (name,t) env.aggregate_kind
  with Not_found ->
    fatal env "Unknown aggregate type %a"
      Fclang_datatype.Qualified_name.pretty (name,t)

let struct_or_union env (name,t) =
  match fst (get_aggregate env (name,t)) with
    | CStruct | CClass -> Struct (name,t)
    | CUnion -> Union (name,t)

let is_extern_c_aggregate env name t = snd (get_aggregate env (name,t))

let class_type_from_qualifications env n =
  struct_or_union env (force_class_name env n)

let current_struct_or_union env =
  fst (get_aggregate env (List.hd env.current_class))

let is_anonymous env =
  let (name,_) = List.hd env.current_class in
  let name = name.decl_name in
  let prefix = "anonymous_" in (* TODO: get this information from clang *)
  let prefix_len = String.length prefix in
    if String.length name <= prefix_len then false
    else
      String.sub name 0 prefix_len = prefix

let unroll_typedef env f typ =
  let rec aux typ =
    match typ with
      | Named (ty, _) when Cxx_utils.is_builtin_qual_type ty ->
          fatal env "unroll_typedef on a builtin type"
      | Named (ty, _) -> aux (get_typedef env ty).plain_type
      | _ -> f env typ
  in
  aux typ

let get_class_name env typ =
  let f env = function
    | Struct (name,t) -> (name,t)
    | _ -> fatal env "type should be a class"
  in
  unroll_typedef env f typ

let get_class_name_from_pointer env typ =
  let f env = function
    | Pointer ( PDataPointer { plain_type } ) -> get_class_name env plain_type
    | _ -> fatal env "type should be a pointer to a class"
  in
  unroll_typedef env f typ

let get_class_name_from_reference env typ =
  let f env = function
    | Struct (name,t) -> (name,t,false)
    | LVReference (PDataPointer { plain_type })
    | RVReference (PDataPointer { plain_type }) ->
        let (name,t) = get_class_name env plain_type in (name,t,true)
    | _ -> fatal env "type should be a class"
  in
  unroll_typedef env f typ

let rec get_struct_name env t =
  let aux env = function
    | Struct (s,t) -> (s, t)
    | Union (s,t) -> (s, t)
    | Pointer (PDataPointer t) -> get_struct_name env t.plain_type
    | LVReference (PDataPointer t) | RVReference (PDataPointer t) ->
        get_struct_name env t.plain_type
    | _ -> fatal env "no struct type information for type"
  in
  unroll_typedef env aux t

let rec get_signature_type env t =
  let aux env = function
    | Pointer (PDataPointer t) -> get_signature_type env t.plain_type
    | LVReference (PDataPointer t)
    | RVReference(PDataPointer t) -> get_signature_type env t.plain_type
    | Pointer (PFunctionPointer s) -> s
    | LVReference (PFunctionPointer s)
    | RVReference (PFunctionPointer s) -> s
    | Pointer(PStandardMethodPointer _)
    | LVReference (PStandardMethodPointer _) 
    | RVReference (PStandardMethodPointer _) ->
        Frama_Clang_option.not_yet_implemented "pointer to member"
    | Pointer(PVirtualMethodPointer _) 
    | LVReference (PVirtualMethodPointer _) 
    | RVReference (PVirtualMethodPointer _) ->
        Frama_Clang_option.not_yet_implemented "pointer to member"
    | Array a -> get_signature_type env a.subtype.plain_type
    | _ -> fatal env "no function type information for type"
  in
  unroll_typedef env aux t

let rec get_struct_name_exp env e =
  match e with
    | Variable (Local n) ->
        get_struct_name env (get_local_var env n.decl_name)
    | Variable (Global n) ->
        get_struct_name env (snd (get_global_var env n))
    | Variable (FunctionParameter n) ->
        get_struct_name env (get_local_var env n)
    | Dereference e -> get_struct_name_exp env e.econtent
    | Address e -> get_struct_name_exp env e.econtent
    | PointerCast(target,_,_) -> get_struct_name env target.plain_type
    | ShiftPointerCast(target,_,_,_) ->
        get_struct_name env target.plain_type
    | FieldAccess(e,f) ->
        let (s, ts) = (get_struct_name_exp env e.econtent) in
        let fields = get_struct env (s,ts) in
        get_struct_name
          env
          (snd (List.find (fun (n,_) -> n = f) fields)).plain_type
    | Conditional(_,etrue,_) -> get_struct_name_exp env etrue.econtent
    | Static_call(_,signature,_,_,_,_) ->
        get_struct_name env signature.result.plain_type
    | Virtual_call(_,signature,_,_,_,_,_,_) ->
        get_struct_name env signature.result.plain_type
    | Dynamic_call(_,ptr,_) ->
      let signature = get_dynamic_signature env ptr.econtent in
      get_struct_name env signature.result.plain_type
    | Temporary(_, ctyp, _, _) -> get_struct_name env ctyp.plain_type
    | _ -> fatal env "no struct type information for expression"

and get_dynamic_signature env e = 
  match e with
    | Variable (Local n) ->
        get_signature_type env (get_local_var env n.decl_name)
    | Variable (Global n) ->
        get_signature_type env (snd (get_global_var env n))
    | Variable (FunctionParameter n) ->
        get_signature_type env (get_local_var env n)
    | Variable (CodePointer (_,signature,_,_,_)) -> signature
    | Assign(_,e) -> get_dynamic_signature env e.econtent
    | Unary_operator(UOCastNoEffect t,_) ->
        get_signature_type env t.plain_type
    | Dereference e -> get_dynamic_signature env e.econtent
    | Address e -> get_dynamic_signature env e.econtent
    | PointerCast(target,_,_)
      -> get_signature_type env target.plain_type
    | ShiftPointerCast(target,_,_,_)
      -> get_signature_type env target.plain_type
    | FieldAccess(e,f)
      -> let (s, ts) = (get_struct_name_exp env e.econtent) in
         let fields = get_struct env (s,ts) in
         get_signature_type env
           (snd (List.find (fun (n, _) -> n = f) fields)).plain_type
    | ArrayAccess(a,_) -> get_dynamic_signature env a.econtent
    | Conditional(_,etrue,_) ->
        get_dynamic_signature env etrue.econtent
    | Static_call(_, signature,_,_,_,_) ->
        get_signature_type env signature.result.plain_type
    | Virtual_call(_,signature,_,_,_,_,_,_) ->
        get_signature_type env signature.result.plain_type
    | Dynamic_call(_,ptr,_) ->
      let signature = get_dynamic_signature env ptr.econtent in
      get_signature_type env signature.result.plain_type
    | Temporary(_, ctyp, _, _) -> get_signature_type env ctyp.plain_type
    | _ -> fatal env "no function type information for expression"

let add_closure_info env capture =
  let current_capture =
    List.fold_left
      (fun acc cap ->
         let cap_name, is_ref =
           match cap with
           | Cap_id (s, _, is_ref) -> s, is_ref
           | Cap_this is_ref -> "this", is_ref
         in
         Datatype.String.Map.add cap_name is_ref acc)
      Datatype.String.Map.empty
      capture
  in
  let captured_vars = current_capture :: env.captured_vars in
  { env with captured_vars }

let closure_var_kind env name =
  match env.captured_vars with
  | [] -> None
  | map :: _ -> Datatype.String.Map.find_opt name map

let reset_closure env =
  match env.captured_vars with
  | [] -> env
  | _::captured_vars -> { env with captured_vars }
