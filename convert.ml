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
open Cabs
open Cil

let lambda_unique_name typ infix id =
  (Mangling.mangle_cc_type typ) ^ infix ^ Int64.to_string id

let lambda_unique_overload_name id =
  "__fc_lambda_overload_" ^ Int64.to_string id

let closure_name = "__fc_closure"

let fc_implicit_attr = "__fc_implicit"

let fc_pure_template_decl_attr = "__fc_pure_template_decl"

let capture_name_type env =
  function
  | Cap_id (s, typ, is_ref) ->
    let typ = if is_ref then Cxx_utils.obj_lvref typ else typ in (s, typ)
  | Cap_this(is_ref) ->
    let (name,tkind as cname) =
      Option.get (Convert_env.get_current_class env)
    in
    let typ =
      if is_ref then Cxx_utils.unqual_type (Struct (name, tkind))
      else Cxx_utils.class_lvref cname
    in ("this", typ)

let id x = x

let raw_block stmts = {blabels = []; battrs = []; bstmts = stmts}

let make_block env stmts =
  let loc = Convert_env.get_loc env in
  BLOCK(raw_block stmts,loc, loc)

let make_stmt env stmt_node =
  { stmt_ghost = Convert_env.is_ghost env; stmt_node }

let make_block_stmt env stmts = make_stmt env (make_block env stmts)

let make_computation env expr =
  make_stmt env (COMPUTATION (expr, expr.expr_loc))

let is_static l = List.mem Static l

(* f(void) means no argument, not one argument of type void *)
let remove_void prm =
  match prm with
    [ { plain_type = Void } ] -> []
  | prm -> prm

let convert_cv = function
  | Const -> SpecCV CV_CONST
  | Volatile -> SpecCV CV_VOLATILE
  | Restrict -> SpecCV CV_RESTRICT
  | Static -> SpecStorage STATIC

let cv_to_attr = function
  | SpecCV CV_CONST -> "const",[]
  | SpecCV CV_VOLATILE -> "volatile",[]
  | SpecCV CV_RESTRICT -> "restrict", []
  | SpecStorage STATIC -> "static", []
  | _ -> "unknown_cv_specifier", []

(* creates an array[dim] of d. Because Cabs follows closely the C
   syntax, we have to take some precautions here. *)
let rec protect_array_type al dim d =
  match d with
  | JUSTBASE -> ARRAY(d,al,dim)
  | PARENTYPE (al1,d',al2) -> 
    PARENTYPE(al1,protect_array_type al dim d', al2)
  | ARRAY(d',al',dim') ->
    (* array dim of array dim' of d' is d' foo[dim][dim'] *)
    ARRAY(protect_array_type al dim d',al',dim')
  | PTR (al',d') ->
    (* array dim of ptr to d' is d' *foo[dim] *)
    PTR(al',protect_array_type al dim d')
    (* array dim of ptr to function returning d' is d' ( *foo[dim]()) *)
  | PROTO(d',args,ghost_args,variadic) ->
    PROTO(protect_array_type al dim d',args,ghost_args, variadic)

(* creates a *d. Similar issue as for protect_array_type. *)
let rec protect_ptr_type al d =
  match d with
  | JUSTBASE -> PTR(al,d)
  | PARENTYPE(al1,d',al2) -> PARENTYPE(al1,protect_ptr_type al d', al2)
  | ARRAY(d',al',dim') ->
    (* pointer to array dim of d is d ( *foo)[dim] *)
    ARRAY(PARENTYPE([],protect_ptr_type al d',[]),al',dim')
  | PTR(al',d') -> PTR(al', protect_ptr_type al d')
  | PROTO _ ->
    (* pointer to function is handled differently. Here, we have a function
       returning a pointer to something else. *)
    PTR (al, d)

let spec_type t = SpecType t

let spec_of_ikind s =
  Cil_types.(
    match s with
      | IBool -> [ SpecType Tbool ]
      | IChar -> [ SpecType Tchar ]
      | ISChar -> [ SpecType Tsigned; SpecType Tchar ]
      | IUChar -> [ SpecType Tunsigned; SpecType Tchar ]
      | IInt -> [ SpecType Tint ]
      | IUInt -> [ SpecType Tunsigned ]
      | IShort -> [ SpecType Tshort ]
      | IUShort -> [ SpecType Tunsigned; SpecType Tshort ]
      | ILong -> [ SpecType Tlong ]
      | IULong -> [ SpecType Tunsigned; SpecType Tlong ]
      | ILongLong -> [ SpecType Tlong; SpecType Tlong ]
      | IULongLong -> [ SpecType Tunsigned; SpecType Tlong; SpecType Tlong ]
  )

let make_integral_constant_kind k v =
  let v = Integer.to_string v in
  let s =
    match k with
      | IBool
      | IChar_s | ISChar | IWChar_s | IWSChar 
      | IChar | IWChar | IShort | IInt -> ""
      | IChar_u | IUChar | IChar16 | IChar32 | IWChar_u | IWUChar
      | IUShort | IUInt -> "U"
      | ILong -> "L"
      | IULong -> "UL"
      | ILongLong -> "LL"
      | IULongLong -> "ULL"
  in CONST_INT (v ^ s)

let is_unsigned_kind = function
  | IBool -> true (* standard says that bool is neither signed nor unsigned,
                     but at some point you have to take sides. *)
  | IChar_s | ISChar | IWChar_s | IWSChar -> false
  | IChar | IWChar -> Cil.theMachine.theMachine.char_is_unsigned
  | IShort | IInt -> false
  | IChar_u | IUChar | IChar16 | IChar32 | IWChar_u | IWUChar
  | IUShort | IUInt -> true
  | ILong | ILongLong -> false
  | IULong | IULongLong -> true

let mk_expr_l expr_loc expr_node = { expr_loc; expr_node }

let mk_expr env node = mk_expr_l (Convert_env.get_loc env) node

let mk_cast_n typ e = CAST (typ, SINGLE_INIT e)

let mk_cast env typ e = mk_expr env (mk_cast_n typ e)

let mk_var_l loc name = mk_expr_l loc (VARIABLE name)

let mk_var env name = mk_expr env (VARIABLE name)

let mk_addrof env e = mk_expr env (UNARY(ADDROF,e))

let mk_int64_cst_n env ?(kind=IInt) i =
  let mk_node i = CONSTANT (make_integral_constant_kind kind i) in
  let mk_node_64 i = mk_node (Integer.of_int64 i) in
  let mk_exp_64 i = mk_expr env (mk_node_64 i) in
  if i < Int64.zero then begin
    if is_unsigned_kind kind then begin
      (* must convert back into unsigned version. *)
      let v = Integer.of_int64 i in
      let v =
        Integer.(add (neg (mul (of_int 2) (of_int64 Int64.min_int)))) v
      in
      mk_node v
    end else if i = Int64.min_int then begin
      let m = Int64.neg (Int64.succ i) in
      BINARY(
        SUB, mk_expr env (UNARY (MINUS, (mk_exp_64 m))), mk_exp_64 Int64.one)
    end else UNARY(MINUS, mk_exp_64 i)
  end else mk_node_64 i

let mk_int64_cst env ?kind i = mk_expr env (mk_int64_cst_n env ?kind i)

let mk_zero ?kind env = (mk_int64_cst env ?kind Int64.zero)

let mk_assign env dst src = mk_expr env (BINARY(ASSIGN, dst, src))

let make_closure_access env id_name is_ref =
  let access = MEMBEROFPTR (mk_var env closure_name, id_name) in
  if is_ref then UNARY(MEMOF,mk_expr env access) else access

let mk_signature res_type param_types = 
  { result = res_type; parameter = param_types; variadic = false }

let mk_arg_decl ty name loc =
  { arg_type = ty; arg_name = name; arg_loc = loc; }

let convert_variable env = function
  | Local({ decl_name = "__func__" }) ->
    CONSTANT(CONST_STRING (Convert_env.get_current_func_name env))
  | Local n ->
    (match Convert_env.closure_var_kind env n.decl_name with
     | None -> VARIABLE n.decl_name
     | Some is_ref -> make_closure_access env n.decl_name is_ref)
  | Global n ->
    let (is_extern_c,_) = Convert_env.get_global_var env n in
    let cname =
      if is_extern_c then n.decl_name else Mangling.mangle n TStandard None
    in
    VARIABLE cname
  | FunctionParameter n ->
    (match Convert_env.closure_var_kind env n with
     | None -> VARIABLE n
     | Some is_ref -> make_closure_access env n is_ref)
  | CodePointer (n,signature,kind,is_extern_c,tm) ->
    let cname =
      if is_extern_c then n.decl_name
      else
        let n, tm = Convert_env.typedef_normalize env n tm in
        let signature = Convert_env.signature_normalize env signature in
        Mangling.mangle n tm (Some (kind,signature))
    in VARIABLE cname

let convert_binary kind assgn e1 e2 =
  match kind,assgn with
    | BOPlus, AKRValue -> BINARY(ADD,e1,e2)
    | BOPlus, AKAssign -> BINARY(ADD_ASSIGN,e1,e2)
    | BOMinus, AKRValue -> BINARY(SUB,e1,e2)
    | BOMinus, AKAssign -> BINARY(SUB_ASSIGN,e1,e2)
    | BOLess, AKRValue -> BINARY(LT,e1,e2)
    | BOLessOrEqual, AKRValue -> BINARY(LE, e1, e2)
    | BOEqual, AKRValue -> BINARY(EQ,e1,e2)
    | BODifferent, AKRValue -> BINARY(NE,e1,e2)
    | BOGreaterOrEqual, AKRValue -> BINARY(GE,e1,e2)
    | BOGreater, AKRValue -> BINARY(GT,e1,e2)
    | BOTimes, AKRValue -> BINARY(MUL,e1,e2)
    | BOTimes, AKAssign -> BINARY(MUL_ASSIGN,e1,e2)
    | BODivide, AKRValue -> BINARY(DIV,e1,e2)
    | BODivide, AKAssign -> BINARY(DIV_ASSIGN,e1,e2)
    | BOModulo, AKRValue -> BINARY(MOD,e1,e2)
    | BOModulo, AKAssign -> BINARY(MOD_ASSIGN,e1,e2)
    | BOBitOr, AKRValue -> BINARY(BOR,e1,e2)
    | BOBitOr, AKAssign -> BINARY(BOR_ASSIGN,e1,e2)
    | BOBitAnd, AKRValue -> BINARY(BAND,e1,e2)
    | BOBitAnd, AKAssign -> BINARY(BAND_ASSIGN,e1,e2)
    | BOBitExclusiveOr, AKRValue -> BINARY(XOR,e1,e2)
    | BOBitExclusiveOr, AKAssign -> BINARY(XOR_ASSIGN,e1,e2)
    | BOLeftShift, AKRValue -> BINARY(SHL,e1,e2)
    | BOLeftShift, AKAssign -> BINARY(SHL_ASSIGN,e1,e2)
    | BORightShift, AKRValue -> BINARY(SHR,e1,e2)
    | BORightShift, AKAssign -> BINARY(SHR_ASSIGN,e1,e2)
    | BOLogicalAnd, AKRValue -> BINARY(AND,e1,e2)
    | BOLogicalOr, AKRValue -> BINARY(OR,e1,e2)
    | BOComma, AKRValue -> COMMA [e1;e2]
    | _, AKAssign -> 
        Frama_Clang_option.fatal
          "Binary operator is not supposed to have an assign kind"

let is_bin_assign = function
  | ADD | SUB | MUL | DIV | MOD | AND | OR | BAND | BOR | XOR
  | SHL | SHR | EQ | NE | LT | GT | LE | GE
    -> false
  | ASSIGN | ADD_ASSIGN | SUB_ASSIGN | MUL_ASSIGN | DIV_ASSIGN | MOD_ASSIGN
  | BAND_ASSIGN | BOR_ASSIGN | XOR_ASSIGN | SHL_ASSIGN | SHR_ASSIGN
    -> true

let is_unary_assign = function
  | MINUS | PLUS | NOT | BNOT | MEMOF | ADDROF -> false
  | PREINCR | PREDECR | POSINCR | POSDECR -> true

let rec make_addrof e =
  match e.expr_node with
    | VARIABLE _ | INDEX _ | MEMBEROF _ | MEMBEROFPTR _ -> 
       { e with expr_node = UNARY(ADDROF,e) }
    (* I think this is handled well by cabs2cil. *)
    | QUESTION _ -> { e with expr_node = UNARY(ADDROF,e) }
    | CAST(_,SINGLE_INIT e) -> make_addrof e
    | PAREN e -> make_addrof e
    | BINARY(a, e1, _) when is_bin_assign a ->
        { e with expr_node = COMMA [ e; make_addrof e1 ] }
    | UNARY(MEMOF, e) -> e
    | UNARY(a, e1) when is_unary_assign a ->
        { e with expr_node = COMMA [ e; make_addrof e1 ] }
    | COMMA l ->
        (match List.rev l with
           | [] ->
               Frama_Clang_option.fatal
                 "Trying to take the address of an empty expression"
           | a::l -> 
               { e with expr_node = COMMA (List.rev ((make_addrof a) :: l))})
    | NOTHING | UNARY _ | LABELADDR _ | BINARY _ | CALL _ | CONSTANT _
    | EXPR_SIZEOF _ | TYPE_SIZEOF _ | EXPR_ALIGNOF _ | TYPE_ALIGNOF _
    | GNU_BODY _ | EXPR_PATTERN _ | CAST _ ->
      Frama_Clang_option.fatal
        "Cannot take the address of a non-lval expression"

let is_builtin_va_list = function
  | Named({ decl_name = "__builtin_va_list"}, _) -> true
  | _ -> false

let rec convert_ref env typ expr =
  match typ, expr with
  (* special case for va_list. *)
  | (LVReference (PDataPointer ty)
    | RVReference (PDataPointer ty)), e
    when is_builtin_va_list ty.plain_type -> e
  | (LVReference _ | RVReference _), { expr_node = UNARY(MEMOF,e) } -> e
  | (LVReference _ | RVReference _), { expr_node = CAST(_,SINGLE_INIT e) } ->
      make_addrof e
  | (LVReference _ | RVReference _), _ -> make_addrof expr
  | Named (ty, _), _
      -> if Convert_env.has_typedef env ty
         then convert_ref env (Convert_env.get_typedef env ty).plain_type expr
         else expr
  | _, _ -> expr

let convert_reference_parameters env variadic prms args =
  let convert_ref typ arg = convert_ref env typ.plain_type arg in
  let rec convert = function
    | [], [] -> []
    | [], args when variadic -> args
    | prm::prms, arg::args -> convert_ref prm arg :: convert (prms,args)
    | _ ->
      Convert_env.fatal env
        "Wrong number of arguments in function call (expected %d, got %d)"
        (List.length prms) (List.length args)
  in
  convert (prms, args)

let rec is_constructor_call e =
 match e.econtent with
   | Static_call (_, _, FKConstructor _, _, _,_) -> true
   | Unary_operator(UOCastNoEffect _,e) -> is_constructor_call e
   | _ -> false

let rec extract_constructor_call e =
  match e.econtent with
    | Static_call (name, sigtype, (FKConstructor _ as kind), args, tn, _) ->
      (kind, name, tn, sigtype, args)
    | Unary_operator(UOCastNoEffect _,e) -> extract_constructor_call e
    | _ -> Frama_Clang_option.fatal "Not a constructor"

let add_attr env name args =
  let expr_loc = Convert_env.get_loc env in
  let name = { expr_loc; expr_node = VARIABLE name } in
  let payload =
    match args with
    | [] -> name
    | _ -> { expr_loc; expr_node = CALL (name, args, []) }
  in
  ("__declspec", [ payload ])

let add_fc_destructor_attr env typ attrs =
  let expr_loc = Convert_env.get_loc env in
  match (Convert_env.qual_type_normalize env typ).plain_type with
  | Struct (n,args) when Convert_env.has_destructor env (n,args) ->
    let name =
      Mangling.mangle
        (Cxx_utils.meth_name n args ("~" ^ n.decl_name))
        TStandard
        (Some
           (FKDestructor true,
            { result = Cxx_utils.unqual_type Void;
              parameter = [];
              variadic = false;
            }))
    in
    let arg =
      { expr_loc;
        expr_node =
          UNARY(
            ADDROF,
            { expr_loc; expr_node = CONSTANT (CONST_STRING name)})}
    in
    let attr = add_attr env Cabs2cil.frama_c_destructor [arg] in
    attr :: attrs
  | _ -> attrs

let rm_fc_destructor_attr attrs =
  List.filter
    (fun (name,content) ->
       name <> "__declspec" ||
       (match content with
        | [ { expr_node = CALL ({ expr_node = VARIABLE n }, _, _)}] ->
          n <> Cabs2cil.frama_c_destructor
        | _ -> true))
    attrs

let add_temporary (* env *) e =
  if is_constructor_call e then
    let (kind, cons,tc,signature,args) = extract_constructor_call e in
    let e =
      { e with econtent
            = Static_call(cons,signature,kind,args,tc,false)
      }
    in e
  else e

(* some temporary might be needed. Note that their list is returned reverted.
   convert_full_expr takes care of putting it in the good order. *)
let var_name s =
  let counter = ref (-1) in
  fun () -> incr counter; s ^ "_" ^ string_of_int !counter

let shift_ptr_var_name = var_name "__cast_tmp"
let virtual_var_name = var_name "__virtual_tmp"
let shift_object_name = var_name "__shift_object"

let find_loc_list f l =
  match l with
    | [] -> Lexing.dummy_pos, Lexing.dummy_pos
    | [ s ] -> f s
    | s :: l ->
        let (beg_loc,_) = f s in
        let rec aux = function
          | [] -> assert false
          | [ s ] ->
              let (_,end_loc) = f s in
              (beg_loc, end_loc)
          | _::l -> aux l
        in
        aux l

let find_loc_stmt =
  function
    | Nop l -> l
    | Return (l,_) -> l
    | Expression (l,_) -> l
    | VirtualExpression (l,_) -> l
    | Ghost_block(l,_) -> l
    | Block (l,_) -> l
    | Condition (l,_,_,_) -> l
    | Label(l,_) -> l
    | Goto(l,_) -> l
    | Switch(l,_,_) -> l
    | VarDecl(l,_,_,_) -> l
    | Break l -> l
    | Continue l -> l
    | While(l,_,_,_) -> l
    | DoWhile(l,_,_,_) -> l
    | For(l,_,_,_,_,_) -> l
    | Code_annot(l,_) -> l
    | TryCatch(l,_,_) -> l
    | GccInlineAsm(l,_,_,_) -> l

let find_loc_list_stmt = find_loc_list find_loc_stmt

let find_loc_case_stmt =
  function
    | Case(_,l) | Default l -> find_loc_list_stmt l

let find_loc_case_stmt_list = find_loc_list find_loc_case_stmt

let empty_aux = []

let merge_aux aux1 aux2 = aux1 @ aux2

let add_local_aux_def defs def = (Some def, None) :: defs

let add_local_aux_def_init defs def init = (Some def, Some init) :: defs

let add_local_aux_init defs init = (None, Some init) :: defs

let add_temp env stmts (dec, init) =
  let stmts =
    match init with
      | None -> stmts
      | Some init -> init :: stmts
  in
  match dec with
    | None -> stmts
    | Some dec -> (make_stmt env (DEFINITION dec)) :: stmts

let add_temp_update env acc (dec,inits) =
  (* We have three possibilities:
     - no definition and a statement
     - a single init expression in the definition and no init statement
     - no init expression and an init statement *)
  match dec with
    | None ->
      (match inits with
        | None -> acc
        | Some s -> s :: acc)
    | Some (DECDEF(_,(_,[(name,_,_,_),inite]),_)) ->
      let stmt =
        match inite, inits with
          | SINGLE_INIT e, None ->
            make_stmt env
              (COMPUTATION(
                  mk_expr env (BINARY(ASSIGN, mk_expr env (VARIABLE name), e)),
                  Convert_env.get_loc env))
          | NO_INIT, Some s -> s
          | _ ->
            Convert_env.fatal env "Unexpected initialization for a temporary"
      in
      stmt :: acc
    | _ -> Convert_env.fatal env "Unexpected definition for a temporary"

let mk_compound_init env lv typ init =
  let loc = Convert_env.get_loc env in
  let rec aux acc lv typ init =
    match init with
    | SINGLE_INIT def ->
      COMPUTATION (
        { expr_loc = def.expr_loc; expr_node = BINARY(ASSIGN,lv,def)},
        def.expr_loc)
      :: acc
    | NO_INIT -> NOP loc :: acc
    | COMPOUND_INIT l ->
      (match typ.plain_type with
       | Array { subtype } ->
         let rec aux_array acc i l =
           match l with
           | [] -> acc
           | (what,init) :: l ->
             (* translation scheme uses that for now. *)
             assert (what = NEXT_INIT);
             let lv =
               { expr_loc = lv.expr_loc;
                 expr_node =
                   INDEX(
                     lv,
                     { expr_loc = lv.expr_loc;
                       expr_node = CONSTANT (CONST_INT (string_of_int i))})}
             in
             aux_array (aux acc lv subtype init) (i+1) l
         in
         aux_array acc 0 l
       | Struct (name, tk) ->
         let rec aux_struct acc lfields linit =
           match lfields, linit with
           | _,[] -> acc
           | [],_ -> 
             Convert_env.fatal
               env "Too many initializers for class %a" 
               Fclang_datatype.Qualified_name.pretty (name,tk)
           | (fname,ftype)::lfields, (what,i)::linit ->
             assert (what = NEXT_INIT);
             let lv = {expr_loc=lv.expr_loc; expr_node=MEMBEROF(lv,fname)} in
             aux_struct (aux acc lv ftype i) lfields linit
         in
         aux_struct acc (Convert_env.get_struct env (name,tk)) l
       | _ -> Convert_env.fatal env "Compound init on a scalar type")
  in
  let init_stmts = aux [] lv typ init in
  match init_stmts with
  | [] -> assert false (* at least one initialization is supposed to occur. *)
  | [ single_init ] -> single_init
  | l -> let l = List.rev_map (make_stmt env) l in make_block env l

let computation_or_nop loc exp =
  match exp.expr_node with
  | NOTHING -> NOP loc
  | _ -> COMPUTATION(exp,loc)

let preserved_returned_object aux e =
  match e.expr_node with
  | VARIABLE n ->
    let transf (d,s as res) =
      match d with
      | Some (DECDEF(spec,(t,l),loc)) ->
        let change_name ((n',decl,attrs,loc),init as res) =
          if n <> n' then res
          else
            ((n,decl,rm_fc_destructor_attr attrs,loc),init)
        in
        let l' = List.map change_name l in
        Some (DECDEF(spec,(t,l'),loc)),s
      | _ -> res
    in
    List.map transf aux
  | _ -> aux

let rec convert_base_type env spec decl typ does_remove_virtual =
  match typ with
  | Void -> spec_type Tvoid :: spec, decl
  | Int IBool -> spec_type Tbool :: spec, decl
  | Int (IChar_u | IChar_s | IChar) -> spec_type Tchar :: spec, decl
  | Int IUChar -> (List.map spec_type [Tunsigned; Tchar]) @ spec, decl
  | Int ISChar -> (List.map spec_type [Tsigned; Tchar ]) @ spec, decl
    (* TODO: intKindForSize returns a type of exactly 16 bits. There is no
       function for providing an ikind of at least 16 bits yet. This should
       be added to Cil. Indeed, it could theoretically be possible that 
       intKindForSize 2 fails while there exist types of a strictly
       greater size. *)
  | Int IChar16 -> spec_of_ikind (Cil.intKindForSize 2 true) @ spec, decl
  | Int IChar32 -> spec_of_ikind (Cil.intKindForSize 4 true) @ spec, decl
  | Int (IWChar_u | IWChar_s | IWUChar | IWSChar | IWChar ) ->
      let wchar_name = { prequalification=[];decl_name="fc_wchar_t"} in
      let base =
        if Convert_env.has_typedef env wchar_name then begin
          let rep = (Convert_env.get_typedef env wchar_name).plain_type in
          match rep with
            | Named (_,is_extern_c) ->
                let name =
                  if is_extern_c then wchar_name.decl_name
                  else Mangling.mangle wchar_name TStandard None
                in
                [ SpecType (Tnamed name) ]
            | Int _ ->
              let spec,_ =
                convert_base_type env [] decl rep does_remove_virtual
              in
              spec
            | _ ->
                Frama_Clang_option.fatal
                  "wchar_t should be linked to a named or integral type"
        end else
          spec_of_ikind Cil.theMachine.Cil.wcharKind
      in
      base @ spec, decl
  | Int IInt -> spec_type Tint :: spec, decl
  | Int IShort -> spec_type Tshort :: spec, decl
  | Int IUShort -> (List.map spec_type [Tunsigned; Tshort ]) @ spec, decl
  | Int IUInt -> (List.map spec_type [Tunsigned; Tint]) @ spec, decl
  | Int ILong -> spec_type Tlong :: spec, decl
  | Int IULong -> (List.map spec_type [Tunsigned; Tlong]) @ spec,decl
  | Int ILongLong -> (List.map spec_type [Tlong; Tlong]) @ spec,decl
  | Int IULongLong ->
    (List.map spec_type [Tunsigned; Tlong; Tlong]) @ spec,decl
  | Float FFloat -> spec_type Tfloat :: spec, decl
  | Float FDouble -> spec_type Tdouble :: spec, decl
  | Float FLongDouble -> (List.map spec_type [Tlong; Tdouble]) @ spec, decl
  | Enum e ->
    let body_name, t = Convert_env.typedef_normalize env e.body TStandard in
    let name =
      if e.ekind_is_extern_c then body_name.decl_name
      else Mangling.mangle body_name t None
    in
    spec_type (Tenum(name,None,[]))::spec, decl
  | Struct (s,t) ->
    let name =
      if Convert_env.is_extern_c_aggregate env s t then s.decl_name
      else
        let s, t = Convert_env.typedef_normalize env s t in
        Mangling.mangle s t None
    in
    spec_type (Tstruct (name, None, [])) :: spec, decl
  | Union (s,t) ->
    let name =
      if Convert_env.is_extern_c_aggregate env s t then s.decl_name
      else
        let s, t = Convert_env.typedef_normalize env s t in
        Mangling.mangle s t None
    in
    spec_type (Tunion (name, None, [])) :: spec, decl
  | Pointer (PDataPointer t) ->
    let attrs = List.map cv_to_attr spec in
    let decl d = decl (protect_ptr_type attrs d) in
    convert_type env decl t does_remove_virtual
  | LVReference (PDataPointer t) | RVReference(PDataPointer t)->
    let attrs = List.map cv_to_attr spec in
    convert_type
      env (fun d -> decl (protect_ptr_type attrs d)) t does_remove_virtual
  | Pointer (PFunctionPointer s) ->
    let rt, rt_decl, args, variadic =
      convert_fptr env s does_remove_virtual
    in
    let attrs = List.map cv_to_attr spec in
    rt,
    (fun d ->
      rt_decl
        (PROTO (decl (protect_ptr_type attrs d), args,[],variadic)))
  | LVReference (PFunctionPointer s)
  | RVReference (PFunctionPointer s) ->
    let rt, rt_decl, args, variadic =
      convert_fptr env s does_remove_virtual
    in
    let attrs= List.map cv_to_attr spec in
    rt,
    (fun d ->
       rt_decl (PROTO (decl (protect_ptr_type attrs d),args,[],variadic)))
  | Pointer(PStandardMethodPointer _)
  | LVReference (PStandardMethodPointer _) 
  | RVReference (PStandardMethodPointer _) ->
      Frama_Clang_option.not_yet_implemented "pointer to member"
  | Pointer(PVirtualMethodPointer _)
  | LVReference (PVirtualMethodPointer _)
  | RVReference (PVirtualMethodPointer _) ->
      Frama_Clang_option.not_yet_implemented "pointer to member"
  | Array a ->
    let is_array_attribute = function
      | SpecCV _ -> true
      | _ -> false
    in
    let attrs = Extlib.filter_map is_array_attribute cv_to_attr spec in
      convert_type
        env
        (fun d ->
          let dim =
            Option.fold
              ~some:(fun e ->
                  let _,_,ce =
                    convert_expr env empty_aux e does_remove_virtual
                  in
                  ce.expr_node)
              ~none:NOTHING
              a.dimension
          in
          let exp =
            { expr_loc = Cil_datatype.Location.unknown; expr_node = dim }
          in
          decl (protect_array_type attrs exp d))
        a.subtype
        does_remove_virtual
  | Named (name, is_extern_c_name) ->
    let cname =
      if Cxx_utils.is_builtin_qual_type name then name.decl_name
      else if is_extern_c_name
      then name.decl_name
      else
        let name, t = Convert_env.typedef_normalize env name TStandard in
        Mangling.mangle name t None
    in
    spec_type (Tnamed cname)::spec, decl
  | Lambda _ ->
    let type_name = Mangling.mangle_cc_type typ in
    (SpecType (Tstruct (type_name, None, []))) :: spec, decl

and convert_type env decl t does_remove_virtual =
  let spec = List.map convert_cv t.qualifier in
  convert_base_type env spec decl t.plain_type does_remove_virtual

and convert_fptr env s does_remove_virtual =
  let args, variadic =
    if s.variadic && s.parameter = [] then [], false
    else
      convert_signature env s.parameter does_remove_virtual, s.variadic
  in
  let rt, rt_decl =
    convert_specifiers env s.result does_remove_virtual
  in
  rt, rt_decl, args, variadic

and convert_signature env l does_remove_virtual =
  match l with
    | [] ->
      (* in C++, an empty list is strictly equivalent to (void), i.e. no 
         argument at all. In C, a prototype with no argument means that the
         arguments are not specified, so that a subsequent declaration could
         provides one or more arguments. We thus normalize that to (void) for
         the C translation.
       *)
      [ [SpecType Tvoid],("",JUSTBASE,[],Convert_env.get_loc env) ]
    | _ -> List.map (convert_anonymous_decl env does_remove_virtual) l

and convert_specifiers env t does_remove_virtual =
  let spec = List.map convert_cv t.qualifier in
  convert_base_type env spec (fun d -> d) t.plain_type does_remove_virtual

and convert_anonymous_decl env does_remove_virtual t =
  let typ, decl = convert_specifiers env t does_remove_virtual in
  (typ, ("",decl JUSTBASE,[],Cil_datatype.Location.unknown))

and convert_decl env does_remove_virtual arg =
  let typ,decl = convert_specifiers env arg.arg_type does_remove_virtual in
  (typ,
   (arg.arg_name, decl JUSTBASE, [],
    Cil_datatype.Location.of_lexing_loc arg.arg_loc))

and make_prototype loc env name kind rt args variadic does_remove_virtual =
  let rt, decl = convert_specifiers env rt does_remove_virtual in
  let args =
    match args with
      | [] -> (* empty list in C++ always mean void, not unspecified *)
        [[SpecType Tvoid],("",JUSTBASE,[],loc)]
      | _ -> List.map (convert_decl env does_remove_virtual) args
  in
  let args =
    match kind, args with
    | FKConstructor _, (spec, name) :: args' ->
      (SpecAttr (add_attr env Cil.frama_c_init_obj []) :: spec, name) :: args'
    | _ -> args
  in
  env, (rt, (name,decl (PROTO(JUSTBASE,args,[],variadic)),[],loc))

and convert_constant env c does_remove_virtual = match c with
  | IntCst (kind,_,v) -> mk_int64_cst_n env ~kind v
  | FloatCst(_,v) -> CONSTANT(CONST_FLOAT v)
  | EnumCst(n,e,_) ->
    let n, t = Convert_env.typedef_normalize env n TStandard in
    let name =
      if e.ekind_is_extern_c then n.decl_name else Mangling.mangle n t None
    in
    let body_name, t' = Convert_env.typedef_normalize env e.body TStandard in
    let enum =
      if e.ekind_is_extern_c then body_name.decl_name
      else Mangling.mangle body_name t' None
    in
    (* C++ enum constant are of type Enum, while C treat them as integers.
       This is not an issue for most purposes, except when it comes to
       handle exceptions: catching enum e is not the same as catching int x.
     *)
    mk_cast_n ([SpecType (Tenum (enum,None,[]))], JUSTBASE) (mk_var env name)
  | TypeCst (TCCSizeOf, t) ->
    let bt,decl = convert_base_type env [] id t does_remove_virtual in
    TYPE_SIZEOF (bt,decl JUSTBASE)
  | TypeCst (TCCAlignOf, t) ->
    let bt,decl = convert_base_type env [] id t does_remove_virtual in
    TYPE_ALIGNOF (bt,decl JUSTBASE)

and convert_unary env kind arg does_remove_virtual =
  match kind with
    (* Not a real cast, merely a compilation's artifact *)
    | UOCastNoEffect _ -> arg.expr_node
    (* Marks initialization of a ref field. treated elsewhere. *)
    | UOCastDerefInit -> arg.expr_node
    (* Use the actual rvalue of a reference. *)
    | UOCastDeref -> UNARY(MEMOF,arg)
    | UOCastToVoid -> mk_cast_n ([SpecType Tvoid], JUSTBASE) arg
    | UOCastInteger(t,_)
    | UOCastEnum(t,_) | UOCastFloat(t,_) | UOCastC t ->
      let rt, decl = convert_specifiers env t does_remove_virtual in
      mk_cast_n (rt, decl JUSTBASE) arg
    | UOPostInc -> UNARY(POSINCR,arg)
    | UOPostDec -> UNARY(POSDECR,arg)
    | UOPreInc  -> UNARY(PREINCR,arg)
    | UOPreDec  -> UNARY(PREDECR,arg)
    | UOOpposite -> UNARY(MINUS,arg)
    | UOBitNegate -> UNARY(BNOT,arg)
    | UOLogicalNegate -> UNARY(NOT,arg)

(* drop_temp is true when the resulting value is not considered further,
   i.e. the expression is evaluated only for its side effect. In this setting,
   temporaries will be translated as NOTHING, since computations occur in the
   tmps instructions and not the returned expression.
*)
and convert_expr_node ?(drop_temp=false) env aux e does_remove_virtual =
  let create_this_access e origin_type aux env is_reference noeffect =
    if (noeffect)
    then e, aux, env
    else begin
      let derived_name, td
        = if not is_reference
          then Convert_env.get_class_name_from_pointer env
            origin_type.plain_type
          else let derived_name, td, _ =
            Convert_env.get_class_name_from_reference env
              origin_type.plain_type
          in derived_name, td
      in
      let var_name = shift_ptr_var_name () in
      let env =
        Convert_env.add_local_var env var_name
          Cxx_utils.(
            plain_obj_ptr (unqual_type (Struct (derived_name,td))))
      in
      let derived_name, td =
        Convert_env.typedef_normalize env derived_name td
      in
      let init =
        if not is_reference then e else mk_expr env (UNARY(ADDROF, e))
      in
      let aux =
        add_local_aux_def aux
          (DECDEF(
              None,
              ([SpecType
                  (Tstruct
                     (Mangling.mangle derived_name td None, None, []))],
               [(var_name, PTR([], JUSTBASE),[], e.expr_loc),
                SINGLE_INIT(init)]), e.expr_loc))
      in
        mk_expr env (VARIABLE var_name), aux, env
    end
  in
  let create_table_access access aux env noeffect =
    if (noeffect) then access, aux, env
    else begin
      let table_access = virtual_var_name () in
      let qual_vmt_content_name = Cxx_utils.empty_qual "_frama_c_vmt_content" in
      let env =
        Convert_env.add_local_var env table_access
          Cxx_utils.(
            plain_obj_ptr (
              unqual_type (Struct (qual_vmt_content_name, TStandard))))
      in
      let qual_vmt_content_name, _ =
        Convert_env.typedef_normalize env qual_vmt_content_name TStandard
      in
      let tmp_decl = DECDEF( None,
       ([SpecType (Tstruct (Mangling.mangle
           qual_vmt_content_name TStandard None, None, []))],
         [(table_access,PTR( [], JUSTBASE),[],access.expr_loc),
           SINGLE_INIT (access)]),
       access.expr_loc)
      in
      let aux = add_local_aux_def aux tmp_decl in
      (mk_expr env (VARIABLE table_access)), aux, env
    end
  in
  let create_shift_object aux env loc =
    let var_name = shift_object_name () in
    let env =
      Convert_env.add_local_var
        env var_name Cxx_utils.(plain_obj_ptr(unqual_type (Int IInt)))
      in
      let def =
        DECDEF(
          None,
          ([SpecType Tint],
           [(var_name, JUSTBASE, [], loc),
            SINGLE_INIT (mk_expr env (CONSTANT (CONST_INT "0")))]), loc)
      in
      let aux = add_local_aux_def aux def in
      mk_expr env (VARIABLE var_name), aux, env
  in
  let env, aux, node =
    match e with
      | Constant c ->
        let e = convert_constant env c does_remove_virtual in env, aux, e
      | String s -> env, aux, CONSTANT (CONST_STRING s)
      | Variable v -> env, aux, convert_variable env v
      | Malloc(t) ->
          let bt,decl = convert_base_type env [] id t does_remove_virtual in
          env,
          aux,
          CALL(mk_expr env (VARIABLE "malloc"),
               [mk_expr env (TYPE_SIZEOF (bt,decl JUSTBASE))],[])
      | MallocArray(t,s) ->
          let bt,decl = convert_base_type env [] id t does_remove_virtual in
          let env, aux, size = convert_expr env aux s does_remove_virtual in
          env,
          aux,
          CALL(
            mk_expr env (VARIABLE "malloc"),
            [mk_expr env
               (BINARY
                  (MUL,
                   mk_expr env (TYPE_SIZEOF(bt,decl JUSTBASE)),size))], [])
      | Free e | FreeArray e ->
          let env, aux, arg = convert_expr env aux e does_remove_virtual in
          env, aux, CALL(mk_expr env (VARIABLE "free"),[arg],[])
      | Assign(x,e) when is_constructor_call e ->
        let kind, name, tn, sigtype, args = extract_constructor_call e in
        let e =
          { e with
            econtent =
              Static_call(name, sigtype, kind,
                { x with econtent = Address x}::args, tn, false)}
        in
        let env, aux, e = convert_expr env aux e does_remove_virtual in
        env, aux, e.expr_node
      (* Initialization of a reference with a reference:
         don't apply the derefs. *)
      | Assign({ econtent = Unary_operator (UOCastDerefInit, x) },e) ->
        let env, aux, lv = convert_expr env aux x does_remove_virtual in
        let env, aux, rv = convert_expr env aux e does_remove_virtual in
        let rv = mk_addrof env rv in
        env, aux, BINARY(ASSIGN,lv,rv)
      | Assign(x,e) ->
          let env, aux, lv = convert_expr env aux x does_remove_virtual in
          let env, aux, rv = convert_expr env aux e does_remove_virtual in
          env, aux, BINARY(ASSIGN,lv,rv)
      | Unary_operator(k,e) ->
          let env, aux, e = convert_expr env aux e does_remove_virtual in
          let e = convert_unary env k e does_remove_virtual in
          env, aux, e
      | Binary_operator(k,a,e1,e2) ->
          let env, aux, e1 = convert_expr env aux e1 does_remove_virtual in
          let env, aux, e2 = convert_expr env aux e2 does_remove_virtual in
          env, aux, convert_binary k a e1 e2
      | Dereference e ->
          let env, aux, e = convert_expr env aux e does_remove_virtual in
          env, aux, UNARY(MEMOF,e)
      | Address e ->
          let env, aux, e = convert_expr env aux e does_remove_virtual in
          env, aux, (make_addrof e).expr_node
      | PointerCast(target,base,e) ->
          let env, aux, e = convert_expr env aux e does_remove_virtual in
          let rt, decl = convert_specifiers env target does_remove_virtual in
            (match base with
              | RPKPointer ->
                  env, aux, mk_cast_n (rt,decl JUSTBASE) e
              | RPKReference ->
                  env, aux,
                  UNARY(
                    MEMOF,
                    mk_cast
                      env (rt,decl JUSTBASE) (mk_expr env (UNARY(ADDROF,e))))
              | RPKStaticBasePointer ->
                let (base_class_name, t) =
                  Convert_env.get_class_name_from_pointer env target.plain_type
                in let (base_class_name, t) =
                  Convert_env.typedef_normalize env base_class_name t
                in
                let cname =
                  "_frama_c_" ^ Mangling.mangle base_class_name t None
                in
                env, aux,
                mk_cast_n
                  (rt,decl JUSTBASE)
                  (mk_expr env
                     (UNARY(ADDROF, mk_expr env (MEMBEROFPTR (e,cname)))))
              | RPKStaticBaseReference ->
                let (base_class_name, t, _) =
                  Convert_env.get_class_name_from_reference
                    env target.plain_type
                in let (base_class_name, t) =
                  Convert_env.typedef_normalize env base_class_name t
                in
                let cname = "_frama_c_" ^ Mangling.mangle base_class_name t None
                in
                env, aux,
                UNARY
                  (MEMOF,
                   mk_cast
                     env (rt,decl JUSTBASE)
                     (mk_addrof env (mk_expr env (MEMBEROF(e, cname)))))
              | RPKVirtualBasePointer(base_index, origin_type, noeffect) ->
                let derived_name, td =
                  Convert_env.get_class_name_from_pointer
                    env origin_type.plain_type
                in
                let var_name = shift_ptr_var_name () in
                let env =
                  Convert_env.add_local_var
                    env var_name
                    Cxx_utils.(
                      plain_obj_ptr (unqual_type (Struct (derived_name,td))))
                in
                let def =
                  DECDEF(
                    None,
                    ([SpecType
                        (Tstruct
                           (Mangling.mangle derived_name td None, None, []))],
                     [(var_name, PTR([], JUSTBASE),[], e.expr_loc),
                      SINGLE_INIT(e)]), e.expr_loc)
                in
                let aux = add_local_aux_def aux def in
                let qual_vmt_name = Cxx_utils.empty_qual "_frama_c_vmt" in
                let this_access, aux, env =
                  create_this_access e origin_type aux env false noeffect
                in
                let qual_vmt_name, _ =
                  Convert_env.typedef_normalize env qual_vmt_name TStandard
                in
                let vmt_type =
                  [SpecType
                     (Tstruct
                        (Mangling.mangle qual_vmt_name
                           TStandard None, None, []))],
                  PTR ([], PTR ([], JUSTBASE))
                in
                let table_access_def =
                  mk_expr env
                    (BINARY
                       (ADD,
                        mk_expr env
                          (MEMBEROFPTR
                             (mk_expr env
                                (UNARY(
                                    MEMOF, mk_cast env vmt_type this_access)),
                              "table")),
                        mk_int64_cst env base_index))
                in
                let access, aux, env =
                  create_table_access table_access_def aux env noeffect
                in
                env, aux,
                mk_cast_n
                  (rt,decl JUSTBASE)
                  (mk_expr env
                     (BINARY
                        (ADD (* to keep positive shift by default
                               - virtual base classes are after *),
                         (* could add downcast with shift *)
                         (mk_cast env
                            ([SpecType Tchar], PTR ([], JUSTBASE))
                            this_access),
                         (mk_expr
                            env
                            (MEMBEROFPTR (access, "shift_this"))))))
              | RPKVirtualBaseReference(base_index, origin_type) ->
                let this_access, aux, env =
                  create_this_access e origin_type aux env
                    true (* is_reference *) false (* noeffect *)
                in
                let qual_vmt_name = Cxx_utils.empty_qual "_frama_c_vmt" in
                let qual_vmt_name,_ =
                  Convert_env.typedef_normalize env qual_vmt_name TStandard
                in
                let vmt_type =
                  [SpecType
                     (Tstruct
                        (Mangling.mangle
                           qual_vmt_name TStandard None, None, []))],
                  PTR ([], PTR ([], JUSTBASE))
                in
                let table_access_def =
                  mk_expr env
                    (BINARY
                       (ADD,
                        mk_expr env
                          (MEMBEROFPTR
                             (mk_expr env
                                (UNARY
                                   (MEMOF,
                                    mk_cast env vmt_type this_access)),
                              "table")),
                        mk_int64_cst env base_index))
                in
                let access, aux, env =
                  create_table_access
                    table_access_def aux env false (* noeffect *)
                in
                env, aux,
                UNARY(
                  MEMOF,
                  mk_cast env
                    (rt,decl JUSTBASE)
                    (mk_expr env
                       (BINARY
                          (ADD, (* to keep positive shift by default
                                   - virtual base classes are after *)
                           (* could add downcast with shift *)
                           mk_cast
                             env
                             ([SpecType Tchar], PTR ([], JUSTBASE)) this_access,
                           mk_expr
                             env (MEMBEROFPTR (access, "shift_this"))))))
              | RPKDynamicPointer (origin_type, pvmt) ->
                let shift_object, aux, env =
                  create_shift_object aux env e.expr_loc
                in
                let origin_name, td =
                  Convert_env.get_class_name_from_pointer
                    env origin_type.plain_type
                in
                let origin_qualification =
                  match td with
                    | TStandard -> QStructOrClass(origin_name.decl_name)
                    | TTemplateInstance params ->
                        QTemplateInstance(origin_name.decl_name, params)
                in
                let env, aux, fst_arg =
                  convert_expr_node env aux
                    (Address
                       { eloc = Convert_env.get_clang_loc env;
                         econtent =
                           (Variable
                              (Global 
                                 { prequalification = List.append
                                     origin_name.prequalification
                                     [origin_qualification];
                                   decl_name = "_frama_c_rtti_name_info" }))})
                    does_remove_virtual
                in
                let env, aux, snd_arg =
                  convert_expr env aux pvmt does_remove_virtual
                in
                let target_name, ttd =
                  Convert_env.get_class_name_from_pointer env target.plain_type
                in
                let target_qualification = 
                  match ttd with
                    | TStandard -> QStructOrClass(target_name.decl_name)
                    | TTemplateInstance params ->
                        QTemplateInstance(target_name.decl_name, params)
                in
                let env, aux, thd_arg =
                  convert_expr_node env aux
                    (Address
                       { eloc = Convert_env.get_clang_loc env;
                         econtent =
                           Variable
                             (Global
                                { prequalification = List.append
                                    target_name.prequalification
                                    [target_qualification];
                                  decl_name = "_frama_c_rtti_name_info" })})
                    does_remove_virtual
                in
                let fourth_arg = mk_addrof env shift_object in
                let args = [fst_arg; snd_arg; thd_arg; fourth_arg] in
                let arg_types =
                  Cxx_utils.([
                      class_ptr
                        (empty_qual "_frama_c_rtti_name_info_node", TStandard);
                      class_ptr (empty_qual "_frama_c_vmt", TStandard);
                      class_ptr
                        (empty_qual "_frama_c_rtti_name_info_node", TStandard);
                      obj_ptr (unqual_type (Int IInt))])
                in
                let dynamic_cast_name =
                  Mangling.mangle
                    (Cxx_utils.empty_qual "_frama_c_find_dynamic_cast")
                    TStandard
                    (Some
                       (FKFunction,
                        { result = Cxx_utils.unqual_type(Int(IInt));
                          parameter = arg_types;
                          variadic = false}))
                in
                env, aux,
                QUESTION(
                  mk_expr env
                    (CALL(mk_expr env (VARIABLE dynamic_cast_name),args,[])),
                  mk_cast env
                    (rt,decl JUSTBASE)
                    (mk_expr env
                       (BINARY
                          (ADD,
                           mk_cast env ([SpecType Tvoid], PTR ([], JUSTBASE)) e,
                           shift_object))),
                  mk_cast env (rt, decl JUSTBASE) (mk_zero env))
              | RPKDynamicReference (_, _) ->
                  env, aux, UNARY(MEMOF,
                    { expr_loc = e.expr_loc ;
                      expr_node =  CAST((rt,decl JUSTBASE),SINGLE_INIT
                      ( { expr_loc = e.expr_loc ;
                          expr_node = UNARY(ADDROF,e)}))}))
      | ShiftPointerCast(target,base,kind,e) ->
          let env, aux, e = convert_expr env aux e does_remove_virtual in
          let rt, decl = convert_specifiers env target does_remove_virtual in
          let derived_aux e derived_name td base_name tb =
            let var_name = shift_ptr_var_name () in
            let env =
              Convert_env.add_local_var
                env var_name (Cxx_utils.plain_class_ptr (derived_name,td))
            in
            let derived_name,td =
              Convert_env.typedef_normalize env derived_name td
            in
            let base_type =
              [SpecType
                    (Tstruct (Mangling.mangle derived_name td None, None, []))]
            in
            let def =
              DECDEF(
                None,
                (base_type,
                 [(var_name, PTR([], JUSTBASE),[], e.expr_loc),
                  SINGLE_INIT
                    (mk_cast
                       env (base_type, PTR([], JUSTBASE)) (mk_zero env))]),
                  e.expr_loc)
            in
            let aux = add_local_aux_def aux def in
            let var_tmp = mk_var env var_name in
            let type_char_ptr e =
               { expr_loc = e.expr_loc ;
                 expr_node =
                   CAST(([SpecType Tchar], PTR ([], JUSTBASE)),SINGLE_INIT e) }
            in
            let base_name,tb =
              Convert_env.typedef_normalize env base_name tb
            in
            let shift =
              mk_expr env
                (BINARY
                   (SUB,
                    (type_char_ptr var_tmp),
                    (type_char_ptr
                       (mk_addrof env
                          (mk_expr env
                             (MEMBEROFPTR
                                (var_tmp,
                                 "_frama_c_" ^
                                 Mangling.mangle base_name tb None)))))))
            in
            env, aux,
            mk_cast_n
              (rt,decl JUSTBASE)
              (mk_expr env (BINARY(ADD, (type_char_ptr e), shift)))
          in
          (match kind with
           | RPKPointer | RPKStaticBasePointer ->
             let derived_name, td =
               Convert_env.get_class_name_from_pointer env target.plain_type
             in
             let base_name, tb =
               Convert_env.get_class_name_from_pointer env base.plain_type
             in
             derived_aux e derived_name td base_name tb
           | RPKReference | RPKStaticBaseReference ->
             let derived_name, td, _ =
               Convert_env.get_class_name_from_reference
                 env target.plain_type
             in
             let base_name, tb, is_base_reference =
               Convert_env.get_class_name_from_reference env base.plain_type
             in
             if is_base_reference then
               let env, aux, expr =
                 derived_aux e derived_name td base_name tb
               in
               env, aux, UNARY(MEMOF, mk_expr env expr)
             else
               let env, aux, expr =
                 derived_aux (mk_addrof env e) derived_name td base_name tb
               in
               env, aux, UNARY(MEMOF, mk_expr env expr)
           | RPKVirtualBasePointer(_, _, _)
           | RPKVirtualBaseReference(_,_) ->
             Frama_Clang_option.fatal
               "virtual base class cannot be converted in derived class"
           | RPKDynamicPointer(_, _)
           | RPKDynamicReference(_, _) ->
             Frama_Clang_option.fatal
               "dynamic_cast class is not support in shift_pointer class")
      | FieldAccess(e,f) ->
          let env, aux, e = convert_expr env aux e does_remove_virtual in
          env, aux, MEMBEROF(e,f)
      | ArrayAccess(a,i) ->
          let env, aux, a = convert_expr env aux a does_remove_virtual in
          let env, aux, i = convert_expr env aux i does_remove_virtual in
          env, aux, INDEX(a,i)
      | Conditional(econd,etrue, efalse) ->
          let env, aux, econd =
            convert_expr env aux econd does_remove_virtual
          in
          let env, aux, etrue =
            convert_expr env aux etrue does_remove_virtual
          in
          let env, aux, efalse =
            convert_expr env aux efalse does_remove_virtual
          in
          env, aux, QUESTION(econd, etrue, efalse)
      | Lambda_call(lambda, args, id) ->
        let loc = Convert_env.get_loc env in
        let env, aux, callee =
          convert_expr env aux lambda does_remove_virtual
        in
        let env, aux, args =
          convert_list_expr env aux args does_remove_virtual
        in
        let args = mk_addrof env callee :: args in
        let mem_fn_name = lambda_unique_overload_name id in
        env, aux, CALL(mk_expr_l loc (MEMBEROF (callee, mem_fn_name)), args, [])
      | Static_call(name, signature, kind, args, t, is_extern_c) ->
        let cname =
          if is_extern_c then name.decl_name
          else
            let name, t = Convert_env.typedef_normalize env name t in
            let signature = Convert_env.signature_normalize env signature in
            Mangling.mangle name t (Some (kind,signature))
        in
        let class_type qualifier =
          let plain_type =
            Convert_env.class_type_from_qualifications env name.prequalification
          in
          Cxx_utils.obj_ptr { qualifier; plain_type }
        in
        let signature =
          match kind with
            | FKFunction  -> signature
            | FKDestructor _ | FKConstructor _ ->
              { signature with
                parameter = (class_type []) :: signature.parameter }
            | FKMethod cv | FKCastMethodOperator (cv,_) ->
              { signature with
                parameter = (class_type cv) :: signature.parameter }
        in
        let env, aux, args =
          convert_list_expr env aux args does_remove_virtual
        in
        let prm = remove_void signature.parameter in
        let args =
          convert_reference_parameters env signature.variadic prm args
        in
        env, aux, CALL(mk_var env cname,args,[])
      | Virtual_call(name,signature,_(*kind*),this,args,method_index, shift,
          shiftPvmt)
        ->
        let env, aux, this = convert_expr env aux this does_remove_virtual in
        let env, aux, args =
          convert_list_expr env aux args does_remove_virtual
        in
        let prm = remove_void signature.parameter in
        let args = convert_reference_parameters env false prm args in
        let var_name = virtual_var_name () in
        let qual_vmt_content_name =
          Cxx_utils.empty_qual "_frama_c_vmt_content"
        in
        let qual_vmt_name = Cxx_utils.empty_qual "_frama_c_vmt" in
        let env =
          Convert_env.add_local_var
            env var_name
            (Cxx_utils.plain_class_ptr (qual_vmt_content_name, TStandard))
        in
        let loc = Convert_env.get_loc env in
        let shift_expr this_expr { base; templated_kind } =
          let base_class_name, t =
            Convert_env.typedef_normalize env base templated_kind
          in
          mk_expr_l this_expr.expr_loc
            (UNARY
               (ADDROF,
                mk_expr_l this_expr.expr_loc
                  (MEMBEROFPTR
                     (this_expr,
                      "_frama_c_" ^ Mangling.mangle base_class_name t None))))
        in
        let thisPvmt =
          match shiftPvmt with
          | [] -> this
          | _ ->
            (mk_cast env
               ([SpecType Tchar], PTR ([], JUSTBASE))
               (List.fold_left shift_expr this shiftPvmt))
        in
        let qual_vmt_content_name, _ =
          Convert_env.typedef_normalize env qual_vmt_content_name TStandard
        in
        let qual_vmt_name, _ =
          Convert_env.typedef_normalize env qual_vmt_name TStandard
        in
        let vmt_content_base_type =
          [SpecType
             (Tstruct
                (Mangling.mangle qual_vmt_content_name TStandard None,
                 None, []))]
        in
        let vmt_base_type =
          [SpecType
             (Tstruct
                (Mangling.mangle qual_vmt_name TStandard None,
                 None, []))]
        in
        let vmt_access =
          mk_expr env
            (UNARY
               (MEMOF,
                mk_cast env
                  (vmt_base_type, PTR ([], PTR ([], JUSTBASE))) thisPvmt))
        in
        let tmp_decl =
          DECDEF(
            None,
            (vmt_content_base_type,
             [(var_name,PTR( [], JUSTBASE),[],loc),
              SINGLE_INIT
                (mk_expr env
                   (BINARY
                      (ADD,
                       (mk_expr env (MEMBEROFPTR (vmt_access, "table"))),
                       (mk_int64_cst env method_index))))]),
             loc)
        in
        let class_type =
          Convert_env.class_type_from_qualifications
            env name.prequalification
        in
        let proto_args =
          convert_signature
            env
            (Cxx_utils.(obj_ptr (unqual_type class_type))::signature.parameter)
            does_remove_virtual
        in
        let proto_rt, proto_rt_decl =
          convert_specifiers env signature.result does_remove_virtual
        in
        let proto_spec = List.map convert_cv signature.result.qualifier in
        let class_name, tc =
          let rev_name = (List.rev name.prequalification) in
          let declared_name, tc =
          begin
            match (List.hd rev_name) with
              | QStructOrClass name -> (name, TStandard)
              | QTemplateInstance (name, l) -> name, (TTemplateInstance l)
              | _ -> Convert_env.fatal env
                "Unexpected qualification for virtual call"
          end in
          ({ prequalification = (List.rev (List.tl rev_name));
            decl_name = declared_name
           }, tc)
        in
        let class_name, tc =
          Convert_env.typedef_normalize env class_name tc
        in
        env, add_local_aux_def aux tmp_decl,
        CALL(
          mk_expr env
            (UNARY
               (MEMOF,
                mk_cast env
                  (proto_rt,
                   proto_rt_decl
                     (PROTO
                        ((PTR(List.map cv_to_attr proto_spec,JUSTBASE)),
                         proto_args,[],false)))
                  (mk_expr
                     env
                     (MEMBEROFPTR (mk_var env var_name, "method_ptr"))))),
            (mk_cast env
               ([SpecType
                   (Tstruct
                      (Mangling.mangle class_name tc None, None, []))],
                PTR ([], JUSTBASE))
               (mk_expr env
                  (BINARY
                     (SUB, (* to keep positive shift by default
                              - concrete classes are before *)
                      (* could add downcast with shift *)
                      (mk_cast env
                         ([SpecType Tchar], PTR ([], JUSTBASE))
                         (List.fold_left shift_expr this shift)),
                      (mk_expr env
                         (MEMBEROFPTR (mk_var env var_name, "shift_this")))))))
            :: args,[])
      | Dynamic_call(_kind,ptr,args) ->
        (* NB: might be slightly different for virtual method *)
        let signature = Convert_env.get_dynamic_signature env ptr.econtent in
        let env, aux, f = convert_expr env aux ptr does_remove_virtual in
        let env, aux, args =
          convert_list_expr env aux args does_remove_virtual
        in
        let prm = remove_void signature.parameter in
        let args =
          convert_reference_parameters env signature.variadic prm args
        in
        env, aux, CALL(f,args,[])
      | Temporary(name, ctyp, init_exp, force) ->
        let env = Convert_env.add_local_var env name ctyp.plain_type in
        let typ, decl = convert_specifiers env ctyp does_remove_virtual in
        let attrs = add_fc_destructor_attr env ctyp [] in
        let res = if drop_temp then NOTHING else VARIABLE name in
        let is_const = Cxx_utils.is_const_type ctyp in
        let rec aux_e exp =
          match exp.econtent with
            | Static_call (n,t,(FKConstructor _ as kind),args,tm,_) ->
              (* clang seems to insert the temporary in the list
                 of arguments, but only randomly... 
                 Note that the parameter's list never contain the receiver
                 argument.
               *)
              let args = 
                if List.length args = List.length t.parameter then
                  { eloc = exp.eloc;
                    econtent =
                      Address {
                        eloc = exp.eloc;
                        econtent = Variable (Local(Cxx_utils.empty_qual name))}}
                  :: args
                else args
              in
              let env, aux, def =
                convert_constr_expr
                  env is_const aux n kind tm t args does_remove_virtual
              in
              let stmt = make_stmt env (COMPUTATION (def, def.expr_loc)) in
              let loc = Convert_env.get_loc env in
              let tmp_decl =
                DECDEF(None,(typ,[(name,decl JUSTBASE,attrs,loc), NO_INIT]),loc)
              in
              env, add_local_aux_def_init aux tmp_decl stmt, res
            | Unary_operator(UOCastNoEffect _,e) -> aux_e e
            | Assign({ econtent = Variable(Local{decl_name = n})}, e)
                when n = name ->
              aux_e e
            | _ ->
              let env, aux, def =
                convert_expr env aux exp does_remove_virtual
              in
              (match def.expr_node, force with
                | VARIABLE _ as v, false -> env, aux, v
                (* no need to waste a temporary here *)
                | _ ->
                  let loc = Convert_env.get_loc env in
                  let tmp_decl =
                    DECDEF(
                      None,
                      (typ,[(name,decl JUSTBASE,attrs,loc), SINGLE_INIT def]),
                      loc)
                  in
                  env, add_local_aux_def aux tmp_decl, res)
        in
        (match init_exp with
          | Single_init exp -> aux_e exp
          | _ ->
            let loc = Convert_env.get_loc env in
            let var = Local { prequalification = []; decl_name = name } in
            let env, aux', init, _ =
              convert_initializer env ctyp var init_exp does_remove_virtual
            in
            let aux = merge_aux aux' aux in
            let tmp_decl =
              DECDEF(
                None,
                (typ,[(name,decl JUSTBASE,attrs,loc), init]), loc)
            in
            env, add_local_aux_def aux tmp_decl, res)
      | VAArg(e,t) ->
        let env, aux', e = convert_expr env aux e does_remove_virtual in
        let typ, decl = convert_specifiers env t does_remove_virtual in
        (* implement the ugly comment in cabs.ml *)
        let builtin = mk_expr env (VARIABLE "__builtin_va_arg") in
        let typ_expr = mk_expr env (TYPE_SIZEOF (typ, decl JUSTBASE)) in
        env, merge_aux aux' aux, CALL (builtin,[e;typ_expr],[])
      | Throw None ->
        let stmt = make_stmt env (THROW (None, Convert_env.get_loc env)) in
        env, add_local_aux_init aux stmt, NOTHING
      | Throw (Some e) ->
        let loc = Convert_env.get_loc env in
        let env, aux, e = convert_expr env aux e does_remove_virtual in
        let aux = preserved_returned_object aux e in
        let stmt = make_stmt env (THROW(Some e, loc)) in
        env, add_local_aux_init aux stmt, NOTHING
      | GnuBody l ->
        let l, env = convert_stmt_list env l does_remove_virtual in
        env, aux, GNU_BODY (raw_block l)
      | InitializerList (elt_typ, (Compound_init l as init)) ->
           (* translated as:
             const T tmp[length l] = { compound_init };
             il_type<T> tmp1 (&a[0], length l);
             return tmp1 as expression
             This assumes that we are using Frama-Clang's own standard lib,
             which has such a constructor
          *)
       let loc = Convert_env.get_loc env in
        let il_size = List.length l in
        let dimension =
          Some
            { eloc = Convert_env.get_clang_loc env;
              econtent =
                Constant (IntCst (IULong, ICLiteral, Int64.of_int il_size)) }
        in
        let subtype = Cxx_utils.const_qual_type elt_typ in
        let array_type = Array { subtype; dimension } in
        let qarray_type = Cxx_utils.unqual_type array_type in
        let carr_type, carr_decl = convert_specifiers env qarray_type false in
        let array_name = Convert_env.temp_name env "init_array" in
        let old_env = env in
        let env = Convert_env.add_local_var env array_name array_type in
        let env, aux', init, e =
          convert_initializer env
            (Cxx_utils.unqual_type array_type)
            (Local (Cxx_utils.empty_qual array_name)) init false
        in
        let array_dec =
          DECDEF(
            None,
            (carr_type,
             [(array_name, carr_decl JUSTBASE, [], loc), init]),loc)
        in
        let aux = merge_aux aux' aux in
        let aux =  (Some array_dec, e) :: aux in
        let il_qual_name =
          { prequalification = [ QNamespace "std" ];
            decl_name = "initializer_list" }
        in
        let il_instance = TTemplateInstance [ TPTypename elt_typ ] in
        let il_type = Struct (il_qual_name, il_instance) in
        let il_name = Convert_env.temp_name env "init_list" in
        let env = Convert_env.add_local_var env il_name il_type in
        let il_cons_name =
          Cxx_utils.meth_name il_qual_name il_instance "initializer_list"
        in
        let il_cons_sig =
          { result = Cxx_utils.unqual_type Void;
            parameter =
              [ Cxx_utils.unqual_type
                  (Pointer
                    (PDataPointer (Cxx_utils.add_qualifiers [Const] elt_typ)));
                Cxx_utils.(unqual_type (Named (empty_qual "size_t", true)))
              ];
            variadic = false
          }
        in
        let il_cons_sig = Convert_env.signature_normalize env il_cons_sig in
        let mangled_name =
          Mangling.mangle
            il_cons_name TStandard (Some (FKConstructor true, il_cons_sig))
        in
        let init_stmt =
          make_stmt env
            (COMPUTATION(
                mk_expr env (
                  CALL(
                    mk_expr env (VARIABLE mangled_name),
                    [ mk_expr env
                        (UNARY (ADDROF, mk_expr env (VARIABLE il_name)));
                      mk_expr env (VARIABLE array_name);
                      mk_expr env
                        (CONSTANT (CONST_INT (string_of_int il_size)))
                    ],[])),loc))
        in
        let cil_type, cil_decl =
          convert_specifiers env (Cxx_utils.unqual_type il_type) false
        in
        let il_dec =
          DECDEF(
            None,
            (cil_type,
             [(il_name, cil_decl JUSTBASE, [], loc), NO_INIT]),loc)
        in
        let aux = add_local_aux_def_init aux il_dec init_stmt in
        Convert_env.unscope env old_env, aux, VARIABLE il_name
      | InitializerList _ ->
        Frama_Clang_option.not_yet_implemented
          "Initializer list without Compound initialization"
      | LambdaExpr(overloads, closures) ->
        let make_signature ovl =
          let params = List.map (fun arg -> arg.arg_type) ovl.arg_decls in
          mk_signature ovl.return_type params
        in
        let signatures = List.map make_signature overloads in
        let lam_type = Lambda (signatures, closures) in
        let lam_name = Convert_env.temp_name env "__fc_lambda_tmp" in
        let (env, aux) =
          create_lambda env aux lam_name lam_type overloads closures in
        let (env, aux) =
          init_lambda_overloads env aux lam_name lam_type overloads closures in
        env, aux, VARIABLE lam_name
  in
  env, aux, mk_expr env node

(* Helper: Create function pointer to the given lambda overload *)
and mk_lambda_fptr_type lam_type overload =
  let fn_ptr_param =
    Cxx_utils.(force_ptr_to_const (obj_ptr (unqual_type lam_type))) in
  let arg_types = (List.map (fun x -> x.arg_type) overload.arg_decls) in
  let fn_sig = mk_signature overload.return_type (fn_ptr_param :: arg_types) in
  Cxx_utils.unqual_type (Pointer (PFunctionPointer fn_sig))

(* Helper: Create function pointer to the given object type as an arg_decl *)
and mk_this_ptr_arg_decl env obj_type param_name =
  let cloc = Convert_env.get_clang_loc env in
  let ptr_type =
    Cxx_utils.(force_ptr_to_const (obj_ptr (unqual_type obj_type))) in
  mk_arg_decl ptr_type param_name cloc

(* Creates and initializes a lambda instance *)
and create_lambda env aux lam_name lam_type overloads closures =
  (* Create the definition of the struct that represents the lambda *)
  let define_struct env name =
    let loc = Convert_env.get_loc env in
    let field_of_capture cap =
      let s, t = capture_name_type env cap in
      let rt, decl = convert_specifiers env t false in
      FIELD (rt, [ (s, decl JUSTBASE, [], loc), None ])
    in
    let field_of_functions ovl =
      let fptr = mk_lambda_fptr_type lam_type ovl in
      let name = lambda_unique_overload_name ovl.id in
      let rt, decl = convert_specifiers env fptr false in
      FIELD (rt, [(name, decl JUSTBASE, [], loc), None])
    in
    let cap_fields = List.map field_of_capture closures in
    let fptr_fields = List.map field_of_functions overloads in
    ONLYTYPEDEF (
      [SpecType (Tstruct(name, Some (fptr_fields @ cap_fields),[]))],loc)
  in
  (* Create a local instance of the struct *)
  let instantiate_struct env name =
    let loc = Convert_env.get_loc env in
    DECDEF(
      None,
      ([ SpecCV CV_CONST; SpecType (Tstruct(name, None,[]))],
        [(lam_name, JUSTBASE, [], loc), NO_INIT ]),loc)
  in
  (* Initializes the lambda captures in the struct *)
  let define_init_fn env name =
    let loc = Convert_env.get_loc env in
    let make_arg_decl cap =
      let arg_loc = Convert_env.get_clang_loc env in
      let (arg_name, arg_type) = capture_name_type env cap in
      { arg_name; arg_type; arg_loc }
    in
    let this_ptr = mk_this_ptr_arg_decl env lam_type closure_name in
    let arg_decls = this_ptr :: (List.map make_arg_decl closures) in
    let env, proto =
      make_prototype loc env name (FKConstructor true)
        (Cxx_utils.unqual_type Void) arg_decls false false
    in
    let body = List.map (make_assign_cap env) closures in
    env, FUNDEF(None, proto, raw_block body, loc, loc)
  in
  (* Calls the function that initializes the lambda captures *)
  let call_init_fn env aux name =
    let mk_arg cap = mk_var env (fst (capture_name_type env cap)) in
    let lam = mk_addrof env (mk_var env lam_name) in
    let actual_args = lam :: (List.map mk_arg closures) in
    let f = mk_var env name in
    let call = mk_expr env (CALL(f,actual_args,[])) in
    let call_stmt = make_computation env call in
    add_local_aux_init aux call_stmt
  in

  let struct_name = Mangling.mangle_cc_type lam_type in
  let struct_def = define_struct env struct_name in
  let env = Convert_env.add_c_global env struct_def in
  let struct_inst = instantiate_struct env struct_name in
  let aux = add_local_aux_def aux struct_inst in
  let env = Convert_env.add_local_var env lam_name lam_type in

  let init_fn_name = struct_name ^ "_init_captures" in
  let env, init_fn = define_init_fn env init_fn_name in
  let env = Convert_env.add_c_global env init_fn in
  let aux = call_init_fn env aux init_fn_name in
  env, aux

and make_assign_cap env cap =
  let name, typ = capture_name_type env cap in
  let dst = mk_expr env (make_closure_access env name false) in
  let src = mk_var env name in
  let rec aux typ =
    match typ.plain_type with
    | Void -> Frama_Clang_option.fatal "Can't copy a value of type void"
    | Int _ | Enum _ | Float _ | Pointer _ | LVReference _ | RVReference _ ->
      make_computation env (mk_assign env dst src)
    | Array _ ->
      Frama_Clang_option.not_yet_implemented
        "capture an array in lambda expression"
    | Lambda _ ->
      Frama_Clang_option.not_yet_implemented
        "capture a lambda type in lambda expression"
    | Struct (name, tkind) ->
      let class_name = Convert_env.typedef_normalize env name tkind in
      (match Convert_env.get_option_copy_constructor env class_name with
       | Some (name, signature) ->
         let cname =
           Mangling.mangle name TStandard (Some (FKConstructor true, signature))
         in
         make_computation env
           (mk_expr env
              (CALL
                 (mk_var env cname, [mk_addrof env dst; mk_addrof env src],[])))
       | None ->
         make_computation env (mk_assign env dst src)
      )
    | Union (name, tkind) ->
      let name, tkind = Convert_env.typedef_normalize env name tkind in
      let ctyp = Tunion (Mangling.mangle name tkind None, None,[]) in
      make_computation env
        (mk_expr env
           (CALL(
               mk_var env "Frama_C_memcpy",
               [mk_addrof env dst; mk_addrof env src;
                mk_expr env (TYPE_SIZEOF([SpecType ctyp],JUSTBASE))],[])))
    | Named (name, _) ->
      aux (Convert_env.get_typedef env name)
  in
  aux typ

(* For a given lambda instance, initialize all overloaded call operators. *)
and init_lambda_overloads env aux lam_name lam_type overloads closures =
  match overloads with
  | [] -> (env, aux)
  | ovl::overloads ->
    let (env, aux) =
      init_lambda_single_overload env aux lam_name lam_type ovl closures in
      init_lambda_overloads env aux lam_name lam_type overloads closures

(* For a given lambda instance, initialize one overloaded call operator.
   This is called once for a C++11 lambda and once or more for a C++14 generic
   lambda. *)
and init_lambda_single_overload env aux lam_name lam_type ovl closures =
  (* Assigns the function pointer for the overload in the struct *)
  let define_init_fn env name =
    let loc = Convert_env.get_loc env in
    let cloc = Convert_env.get_clang_loc env in
    let fptr_type = mk_lambda_fptr_type lam_type ovl in
    let fptr_arg_decl = mk_arg_decl fptr_type "__fc_func" cloc in
    let this_ptr = mk_this_ptr_arg_decl env lam_type closure_name in
    let env, proto =
      make_prototype loc env name (FKConstructor true)
        (Cxx_utils.unqual_type Void) [this_ptr; fptr_arg_decl] false false
    in
    let fn_name = lambda_unique_overload_name ovl.id in
    let body_stmt =
      make_computation env
        (mk_assign env
          (mk_expr env (make_closure_access env fn_name false))
          (mk_var env "__fc_func"))
    in
    env, FUNDEF(None, proto, raw_block [body_stmt], loc, loc)
  in
  (* Contains the lambda's actual code for the overload *)
  let define_body_fn env name =
    let loc = Convert_env.get_loc env in
    let this_ptr = mk_this_ptr_arg_decl env lam_type closure_name in
    let arg_decls = this_ptr :: ovl.arg_decls in
    let env, full_name =
      make_prototype loc env name FKFunction
        ovl.return_type arg_decls false false
    in
    let benv = Convert_env.add_formal_parameters env arg_decls in
    let cbody, benv = convert_stmt_list benv ovl.impl false in
    let env = Convert_env.unscope benv env in
    env, FUNDEF (None, full_name, raw_block cbody, loc, loc)
  in
  (* Calls the init function with a pointer to the body function *)
  let call_init_fn env aux name body_fn_name =
    let f = mk_var env name in
    let lam = mk_addrof env (mk_var env lam_name) in
    let ptr = mk_var env body_fn_name in
    let call = mk_expr env (CALL(f,[lam; ptr],[])) in
    let call_stmt = make_computation env call in
    add_local_aux_init aux call_stmt
  in

  let init_fn_name = lambda_unique_name lam_type "_init_" ovl.id in
  let env, init_fn = define_init_fn env init_fn_name in
  let env = Convert_env.add_c_global env init_fn in
  let env = Convert_env.add_closure_info env closures in

  let body_fn_name = lambda_unique_name lam_type "_body_" ovl.id in
  let env, body_fn = define_body_fn env body_fn_name in
  let env = Convert_env.add_c_global env body_fn in
  let env = Convert_env.reset_closure env in
  let aux = call_init_fn env aux init_fn_name body_fn_name in
  env, aux

and convert_expr ?drop_temp env aux e =
  let env = Convert_env.set_loc env e.eloc in
  convert_expr_node ?drop_temp env aux e.econtent

and convert_list_expr env aux l does_remove_virtual =
  let env, aux, args =
    List.fold_left
      (fun (env, aux, acc) arg ->
        let arg = add_temporary (* env *) arg in
        let env, aux, arg = convert_expr env aux arg does_remove_virtual in
        env, aux, arg::acc)
      (env, aux, []) l
  in
  env, aux, List.rev args

and convert_constr_expr env is_const aux n kind tc t args does_remove_virtual =
  let n', tc'
    = Convert_env.typedef_normalize env n tc in
  let t' = Convert_env.signature_normalize env t in
  let cname = Mangling.mangle n' tc' (Some (kind,t')) in
  let class_type =
    Convert_env.class_type_from_qualifications env n.prequalification
  in
  let this_type =
    { qualifier = [];
      plain_type =
        Pointer (PDataPointer { qualifier = []; plain_type = class_type})}
  in
  let args =
    if is_const then begin
      match args with
      | [] -> Frama_Clang_option.fatal "constructor without `this' argument"
      | this :: args ->
        { eloc = this.eloc; econtent = PointerCast (this_type,RPKPointer,this) }
        :: args
    end else args
  in
  let signature = { t with parameter = this_type :: t.parameter} in
  let env, aux, args = convert_list_expr env aux args does_remove_virtual in
  let prm = remove_void signature.parameter in
  let args = convert_reference_parameters env t.variadic prm args in
  env, aux, mk_expr env (CALL(mk_var env cname,args,[]))

and convert_full_constr_expr env is_const n kind tc t args =
  convert_constr_expr env is_const empty_aux n kind tc t args

(* list of temp declaration is built backwards. Don't forget to revert it
   somewhere. *)
and convert_full_expr ?drop_temp env e = convert_expr ?drop_temp env empty_aux e

and combine_trunc l1 l2 =
  match l1,l2 with
    | [], _ | _,[] -> []
    | x::xs, y::ys -> (x,y) :: combine_trunc xs ys

and find_type_list env typ l =
  let rec aux typ =
    match typ with
      | Void | Int _ | Enum _ | Float _ | Pointer _ 
      | LVReference _ | RVReference _ | Lambda _ ->
        Convert_env.fatal env "Using compound initialization for a scalar value"
      | Array typ ->
        List.map (fun x -> (typ.subtype, x)) l
      | Struct (s,ts) ->
        let fields = Convert_env.get_struct env (s,ts) in
        combine_trunc (List.map snd fields) l
      | Union _ -> (* handled by Union_init, not Compound_init *)
        Convert_env.fatal env "Using compound initialization for an union"
      (* builtins are always scalar for now. *)
      | Named (ty,_) when Cxx_utils.is_builtin_qual_type ty ->
        Convert_env.fatal env
          "Using compound initialization for a builtin value"
      | Named (ty,_) -> aux (Convert_env.get_typedef env ty).plain_type
  in aux typ

and convert_initializer env typ var init_exp does_remove_virtual =
  let init_var_counter = ref 0 in
  let equal v1 v2 =
    match v1,v2 with
      | Local v1, Local v2
        -> Fclang_datatype.Qualified_name.equal (v1,TStandard) (v2,TStandard)
      | Global v1, Global v2
        -> Fclang_datatype.Qualified_name.equal (v1,TStandard) (v2,TStandard)
      | _ -> false
  in
  (* default 0-initialization. *)
  let rec mk_default_init typ =
    match typ.plain_type with
    | Int _ | Enum _ | Pointer _ -> SINGLE_INIT(mk_zero env)
    | Float _ -> SINGLE_INIT (mk_expr env (CONSTANT(CONST_FLOAT "0.")))

    | LVReference _ | RVReference _ ->
      Convert_env.fatal env "Unsupported: default initialization of reference"
    | Lambda _ -> (* could probably be directly assert false *)
      Convert_env.fatal env
        "Unsupported: default initialization of lambda object"

    (* initialize at least one element. *)
   | Array typ ->
      COMPOUND_INIT [ NEXT_INIT, mk_default_init typ.subtype ]
    | Struct (s,ts) | Union (s,ts) ->
      (match Convert_env.get_struct env (s,ts) with
       | [] -> NO_INIT
       | (field, typ) :: _ ->
         COMPOUND_INIT
           [ INFIELD_INIT(field,NEXT_INIT), mk_default_init typ ])

    | Named (ty,_) when Cxx_utils.is_builtin_qual_type ty -> NO_INIT
    | Named(ty,_) -> mk_default_init (Convert_env.get_typedef env ty)
    | Void -> assert false
  in
  let rec aux_init env typ var = function
    | Single_init init ->
      (match init.econtent with
        | Static_call(n,t, (FKConstructor _ as kind),args,tm,_) ->
          let is_const = Cxx_utils.is_const_type typ in
          let env, aux, def =
            convert_full_constr_expr
              env is_const n kind tm t args does_remove_virtual
          in
          env,
          aux, NO_INIT,
          Some (make_stmt env (COMPUTATION (def, def.expr_loc)))
        | Assign({ econtent = Variable v}, e) when equal v var ->
          aux_init env typ var (Single_init e)
        | _ ->
          let env, aux, def = convert_full_expr env init does_remove_virtual in
          let def = convert_ref env typ.plain_type def in
          env, aux, SINGLE_INIT def, None)
    | Implicit_init -> env, [], mk_default_init typ, None
    | Compound_init l ->
      let typed_l = find_type_list env typ.plain_type l in
      let env, aux, init =
        List.fold_left (convert_one_init NEXT_INIT) (env, empty_aux,[]) typed_l
      in
      let init =
        match init with
        | [] -> NO_INIT
        | _ -> COMPOUND_INIT (List.rev init)
      in
      env, aux, init, None
    | Array_init(idx, init) ->
      (match Convert_env.qual_type_normalize env typ with
       | { plain_type = Array { dimension } } ->
         (match dimension with
            | Some ({ econtent = Constant (IntCst (_,_,v))}) ->
              let idx = idx.decl_name in
              let loc = Convert_env.get_loc env in
              let lenv =
                Convert_env.add_local_var env idx (Int IULong)
              in
              let tmp =
                DECDEF(
                  None,
                  ([SpecType Tunsigned; SpecType Tlong],
                   [(idx, JUSTBASE, [], loc),
                    SINGLE_INIT(
                      {expr_loc = loc;
                       expr_node = CONSTANT (CONST_INT "0UL")})]),
                  loc)
              in
              let eidx = { expr_loc = loc; expr_node = VARIABLE idx } in
              let end_test =
                { expr_loc = loc;
                  expr_node =
                    BINARY(
                      LT,
                      eidx,
                      { expr_loc = loc;
                        expr_node =
                          CONSTANT (CONST_INT (Int64.to_string v)) }) }
              in
              let increment =
                { expr_loc = loc; expr_node = UNARY(POSINCR, eidx)}
              in
              let env, aux, body =
                convert_full_expr ~drop_temp:true lenv init does_remove_virtual in
              let stmt_node = computation_or_nop loc body in
              let body = make_stmt env stmt_node in
              env, aux, NO_INIT,
              Some(
                make_stmt env
                  (FOR([],FC_DECL tmp,end_test,increment,body,loc)))
            | _ ->
              Convert_env.fatal env
                "Implicit array initialization \
                 over a array of non-constant size"
         )
       | _ ->
         Convert_env.fatal env
           "Implicit array initialization on a non-array type")
    | Union_init(field,typ,init) ->
      let env, aux, init =
        convert_one_init
          (INFIELD_INIT (field,NEXT_INIT)) (env, empty_aux,[]) (typ, init)
      in
      assert (List.length init = 1);
      env, aux, COMPOUND_INIT init, None
  and convert_one_init what (env, aux, acc) (ty,i) =
    let tmp = "__init_tmp_" ^ (string_of_int !init_var_counter) in
    let var = Local { prequalification = []; decl_name = tmp } in
    let env, aux', def, cons = aux_init env ty var i in
    let aux = merge_aux aux' aux in
    match i, cons with
      | _, None -> env, aux, (what,def)::acc
      | Single_init e, Some _ ->
        incr init_var_counter;
        let spec, decl = convert_specifiers env ty does_remove_virtual in
        let attrs = add_fc_destructor_attr env ty [] in
        let cloc = Cil_datatype.Location.of_lexing_loc e.eloc in
        let decl =
          DECDEF
            (None,
             (spec, [(tmp, decl JUSTBASE,attrs,cloc), NO_INIT]), cloc)
        in
        let aux = (Some decl, cons)::aux in
        env, aux,
        (what, SINGLE_INIT { expr_loc = cloc; expr_node = VARIABLE tmp })
        :: acc
      | _, Some _ ->
        Convert_env.fatal env "unexpected initializer"
  in
  aux_init env typ var init_exp

and convert_init_statement env init does_remove_virtual =
  let loc = Convert_env.get_loc env in
  match init with
  | INop ->
    FC_EXP { expr_loc = loc; expr_node = NOTHING },[], env
  | IExpression e ->
    let env, aux, e =
      convert_full_expr ~drop_temp:true env e does_remove_virtual
    in
    FC_EXP e,
    List.fold_left (add_temp env) [] aux,
    env
  | IVarDecl init_declarator_list ->
    let env, aux, l, def, base =
      List.fold_right
        (fun {id_name; init_type=typ; init_val} (env,aux,l,def, base) ->
          let base', decl = convert_specifiers env typ does_remove_virtual in
          let base =
            match base with
             | None -> Some base'
             | Some b ->
               if b = base' then base
               else
                 Convert_env.fatal env
                   "list of declaration with different base types"
          in
          let attrs = add_fc_destructor_attr env typ [] in
          let env = Convert_env.add_local_var env id_name typ.plain_type in
          match init_val with
          | None ->
	    let init = (id_name, decl JUSTBASE,[],loc),NO_INIT in
	    (env, aux, init::l, def, base)
          | Some init ->
            let var = Local { prequalification = []; decl_name = id_name } in
            let env,aux',init, def' =
              convert_initializer env typ var init does_remove_virtual
            in
	    let def = match def' with
	      | None -> def
	      | Some stmt -> stmt::def
	    in
	    let init = (id_name, decl JUSTBASE,attrs,loc),init in
	    env, merge_aux aux' aux, init::l, def, base)
	init_declarator_list
	(env, empty_aux, [], [], None)
    in
    let l = List.rev l in
    if l = [] then
      Convert_env.fatal env "Empty list of local variable declarations";
    let base = Option.get base in
    let decl = DECDEF (None,(base,l),loc) in
    match def with
    | [] ->
      FC_DECL decl,
      List.fold_left (add_temp env) [] aux,
      env
    | l ->
      FC_EXP { expr_loc = loc; expr_node = NOTHING },
      List.fold_left (add_temp env) l ((Some decl,None)::aux),
      env

and convert_condition env cond does_remove_virtual =
  let loc = Convert_env.get_loc env in
  match cond with
  | CondExpression e -> convert_full_expr env e does_remove_virtual
  | CondVarDecl(name, typ, init) ->
    let attrs = add_fc_destructor_attr env typ [] in
    let env = Convert_env.add_local_var env name typ.plain_type in
    let base, decl = convert_specifiers env typ does_remove_virtual in
    let res = { expr_loc = loc; expr_node = VARIABLE name } in
    let var = Local { prequalification = []; decl_name = name } in
    let env, aux, init, e =
      convert_initializer env typ var init does_remove_virtual
    in
    let decl =
      DECDEF(None,(base,[(name, decl JUSTBASE,attrs,loc),init]),loc)
    in
    let aux =  (Some decl, e) :: aux in
    env, aux, res

and convert_incr_statement env incr does_remove_virtual =
  let loc = Convert_env.get_loc env in
  match incr with
    | CNop -> env, { expr_loc = loc; expr_node = NOTHING }
    | CExpression e ->
      let env, aux, e =
        convert_full_expr ~drop_temp:true env e does_remove_virtual
      in
      let stmt_node = computation_or_nop loc e in
      match aux with
      | [] -> env, e
      | _ ->
        let stmt = make_stmt env stmt_node in
        let stmts = List.fold_left (add_temp env) [stmt] aux in
        env, mk_expr_l loc (GNU_BODY { blabels=[]; battrs=[]; bstmts = stmts })

and convert_statement env st does_remove_virtual =
  let rec add_temps tmps stmt =
    match tmps with
    | [] -> stmt
    | (def,init) :: tl ->
      let loc = Convert_env.get_loc env in
      let stmt =
        match init with
          | None -> stmt
          | Some s ->
            SEQUENCE(s, make_stmt env stmt,loc)
      in
      let stmt =
        match def with
          | None -> stmt
          | Some def ->
            let def = make_stmt env (DEFINITION def) in
            let stmt = make_stmt env stmt in
            SEQUENCE(def,stmt,loc)
      in
      add_temps tl stmt
  in
  let add_temps_update tmps stmt =
    match tmps with
    | [] -> stmt
    | _ ->
      let block = List.fold_left (add_temp_update env) [] tmps in
      make_block_stmt env (stmt::block)
  in
  let raw, env =
    match st with
    | Nop l -> NOP (Cil_datatype.Location.of_lexing_loc l), env
    | Code_annot (l,annot) ->
      let env = Convert_env.set_loc env l in
      let cloc = Convert_env.get_loc env in
      let c_annot = Convert_acsl.convert_code_annot env annot in
      CODE_ANNOT(c_annot,cloc), env
    | Return (l,Some e) ->
      let e = add_temporary (* env *) e in
      let env, aux, e = convert_full_expr env e does_remove_virtual in
      let e = convert_ref env (Convert_env.get_current_return_type env) e in
      let aux = preserved_returned_object aux e in
      let stmt = RETURN(e,Cil_datatype.Location.of_lexing_loc l) in
      let stmts = add_temps aux stmt in
      stmts, env
    | Return(l, None) ->
      let cl = Cil_datatype.Location.of_lexing_loc l in
      RETURN({expr_loc = cl; expr_node = NOTHING},cl), env
    | Expression (loc,e) ->
      let env = Convert_env.set_loc env loc in
      let cloc = Cil_datatype.Location.of_lexing_loc loc in
      let env, aux, e =
        convert_full_expr ~drop_temp:true env e does_remove_virtual
      in
      add_temps aux (COMPUTATION(e,cloc)), env
    | VirtualExpression (loc,e) ->
      let cloc = Cil_datatype.Location.of_lexing_loc loc in
      if does_remove_virtual then NOP cloc, env
      else
        let env = Convert_env.set_loc env loc in
        let env, aux, e = convert_full_expr env e does_remove_virtual in
        add_temps aux (COMPUTATION(e,cloc)), env
    | Ghost_block(loc,stmts) ->
      let old_ghost = Convert_env.is_ghost env in
      let env = Convert_env.set_loc env loc in
      let env = Convert_env.set_ghost env true in
      let cloc = Cil_datatype.Location.of_lexing_loc loc in
      let b, env = convert_block env stmts does_remove_virtual in
      let env = Convert_env.set_ghost env old_ghost in
      BLOCK(b,cloc,cloc), env
    | Block(loc,stmts) ->
      let env = Convert_env.set_loc env loc in
      let cloc = Cil_datatype.Location.of_lexing_loc loc in
      let b, env = convert_block env stmts does_remove_virtual in
      BLOCK(b, cloc, cloc), env
    | Condition(loc,cond,true_action,false_action) ->
      let env = Convert_env.set_loc env loc in
      let cloc = Cil_datatype.Location.of_lexing_loc loc in
      let env, aux, cond = convert_condition env cond does_remove_virtual in
      let true_action, env =
        convert_statement env true_action does_remove_virtual
      in
      let false_action, env =
        convert_statement env false_action does_remove_virtual
      in
      add_temps aux (IF(cond,true_action,false_action,cloc)), env
    | Label(loc,lab) ->
      let env = Convert_env.set_loc env loc in
      let cloc = Cil_datatype.Location.of_lexing_loc loc in
      let stmt = make_stmt env (NOP cloc) in
      LABEL(lab,stmt,cloc), env
    | Goto(loc,lab) ->
      let env = Convert_env.set_loc env loc in
      let cloc = Cil_datatype.Location.of_lexing_loc loc in
      GOTO(lab,cloc), env
    | Switch(loc,cond,cases) ->
      let env = Convert_env.set_loc env loc in
      let cloc = Cil_datatype.Location.of_lexing_loc loc in
      let env, aux, cond = convert_condition env cond does_remove_virtual in
      let cases_loc = find_loc_case_stmt_list cases in
      let cases_loc = Cil_datatype.Location.of_lexing_loc cases_loc in
      let cases, env =
        List.fold_left
          (convert_case_statement does_remove_virtual) ([],env) cases
      in
      let cases = { blabels = []; battrs = []; bstmts = List.rev cases } in
      let cases = make_stmt env (BLOCK(cases,cases_loc,cases_loc)) in
      add_temps aux (SWITCH(cond,cases,cloc)), env
    | VarDecl (loc, name, typ, init) ->
      let env = Convert_env.set_loc env loc in
      let cloc = Cil_datatype.Location.of_lexing_loc loc in
      let base, decl = convert_specifiers env typ does_remove_virtual in
      let qual_name = { prequalification = []; decl_name = name } in
      let attrs = add_fc_destructor_attr env typ [] in
      let env =
        if List.mem Static typ.qualifier then
          let extern = Convert_env.is_extern_c env in
          let env = Convert_env.set_extern_c env true in
          let env = Convert_env.add_global_var env qual_name typ.plain_type in
          Convert_env.set_extern_c env extern
        else
          Convert_env.add_local_var env name typ.plain_type
      in
      let var = Local qual_name in
      let env, aux, init, e =
        match init with
        | None -> env, empty_aux, NO_INIT, None
        | Some e -> convert_initializer env typ var e does_remove_virtual
      in
      let decl init =
        DECDEF(None, (base,[(name, decl JUSTBASE,attrs,cloc),init]), cloc)
      in
      let stmt =
        match aux with
        | [] ->
          let def = DEFINITION (decl init) in
          (match e with
            | None -> def
            | Some stmt -> SEQUENCE (make_stmt env def, stmt, cloc))
        | _ ->
          (* We put all these declarations in a special block, 
             but the initial declaration itself need to stay out of it.
           *)
          let def = DEFINITION (decl NO_INIT) in
          let block =
            match e with
            | None ->
              let var_expr = { expr_loc = cloc; expr_node = VARIABLE name } in
              mk_compound_init env var_expr typ init
            | Some s -> s.stmt_node
          in
          let block = add_temps aux block in
          SEQUENCE (make_stmt env def, make_stmt env block, cloc)
      in
      stmt, env
    | Break l -> BREAK (Cil_datatype.Location.of_lexing_loc l), env
    | Continue l -> CONTINUE (Cil_datatype.Location.of_lexing_loc l), env
    | While (loc, cond, body, annot) ->
      let env = Convert_env.set_loc env loc in
      let cloc = Cil_datatype.Location.of_lexing_loc loc in
      let env, aux, cond = convert_full_expr env cond does_remove_virtual in
      let body,env = convert_statement env body does_remove_virtual in
      let body = add_temps_update aux body in
      let annot = List.map (Convert_acsl.convert_code_annot env) annot in
      add_temps aux (WHILE(annot,cond,body,cloc)), env
    | DoWhile (loc, cond, body,annot) ->
      let env = Convert_env.set_loc env loc in
      let cloc = Cil_datatype.Location.of_lexing_loc loc in
      let env, aux, cond = convert_full_expr env cond does_remove_virtual in
      let body, env = convert_statement env body does_remove_virtual in
      let body = add_temps_update aux body in
      let annot = List.map (Convert_acsl.convert_code_annot env) annot in
      add_temps aux (DOWHILE(annot, cond, body, cloc)), env
    | For(loc, init, cond, incr, body,annot) ->
      let env = Convert_env.set_loc env loc in
      let cloc = Cil_datatype.Location.of_lexing_loc loc in
      let init, stmts, ienv =
        convert_init_statement env init does_remove_virtual
      in
      let ienv, aux, cond = match cond with
        | None -> ienv, empty_aux, { expr_loc = cloc ; expr_node = NOTHING }
        | Some cond -> convert_full_expr ienv cond does_remove_virtual
      in
      let ienv, incr =
        convert_incr_statement ienv incr does_remove_virtual
      in
      let annot = List.map (Convert_acsl.convert_code_annot ienv) annot in
      let body, ienv = convert_statement ienv body does_remove_virtual in
      let body = add_temps_update aux body in
      let loop = FOR(annot,init,cond,incr,body,cloc) in
      let stmt =
        match stmts, aux with
          [], [] -> loop
        | [], l -> add_temps l loop
        | _,[] -> make_block ienv (stmts @ [make_stmt env loop])
        | _, l ->
          let block = List.fold_left (add_temp env) [make_stmt env loop] l in
          make_block ienv (stmts @ block)
      in
      stmt, Convert_env.unscope ienv env
    | TryCatch (loc, t, c) ->
      let env = Convert_env.set_loc env loc in
      let cloc = Cil_datatype.Location.of_lexing_loc loc in
      let t, env = convert_stmt_list env t does_remove_virtual in
      let t = make_block_stmt env t in
      let c, env =
        List.fold_left
          (convert_catch_clause does_remove_virtual) ([], env) c
      in
      let c = List.rev c in
      TRY_CATCH(t,c,cloc), env
    | GccInlineAsm(loc, qual, instr, details) ->
      let qual = List.map (fun x -> cv_to_attr (convert_cv x)) qual in
      let convert_asm_IO asm_io =
          List.map
            (fun {aIO_name=n;constraints=c;expr=e}->
             let (_,_,e)=convert_full_expr env e does_remove_virtual in (n,c,e))
            asm_io
      in
      let details = match details with
        | None -> None
        | Some {outputs=o; inputs=i; clobbers=c; ad_labels=l} ->
          Some
            { aoutputs=convert_asm_IO o;
              ainputs=convert_asm_IO i;
              aclobbers=c; alabels=l }
      in
      let cloc = Cil_datatype.Location.of_lexing_loc loc in
      ASM(qual, instr, details, cloc), env
  in
  make_stmt env raw, env

and convert_catch_clause does_remove_virtual (acc,env) { typed_arg; cbody } =
  let var, env =
    match typed_arg with
      | None -> None, env
      | Some v ->
        let qtype = Convert_env.qual_type_normalize env v.arg_type in
        let decl = convert_decl env does_remove_virtual v in
        Some decl,
        Convert_env.add_local_var env v.arg_name qtype.plain_type
  in
  let body, env =
    convert_stmt_list env cbody does_remove_virtual
  in
  let body = make_block_stmt env body in
  (var,body)::acc, env

and convert_case_statement does_remove_virtual (acc, env) case =
  match case with
    | Case(value,action) ->
        let loc = find_loc_list_stmt action in
        let cloc = Cil_datatype.Location.of_lexing_loc loc in
        let value = convert_constant env value does_remove_virtual in
        let value = mk_expr_l cloc value in
        let action, env =
          convert_stmt_block env action does_remove_virtual
        in
        make_stmt env (CASE(value,action,cloc)) :: acc, env
    | Default(action) ->
        let loc = find_loc_list_stmt action in
        let cloc = Cil_datatype.Location.of_lexing_loc loc in
        let action, env =
          convert_stmt_block env action does_remove_virtual
        in
        make_stmt env (DEFAULT(action,cloc))::acc, env

and convert_stmt_block env b does_remove_virtual =
  let loc = find_loc_list_stmt b in
  let cloc = Cil_datatype.Location.of_lexing_loc loc in
  let stmts, env = convert_stmt_list env b does_remove_virtual in
  let stmt =
    match stmts with
      [] -> make_stmt env (NOP cloc)
    | [ a ] -> a
    | l -> make_block_stmt env l
  in
  stmt, env

and convert_block env b does_remove_virtual =
  let stmts, env = convert_stmt_list env b does_remove_virtual in
  raw_block stmts, env

and convert_stmt_list env l does_remove_virtual =
  let (stmts, env) =
    List.fold_left
      (fun (acc, env) stmt ->
         let (s,env) = convert_statement env stmt does_remove_virtual in
         s::acc, env)
      ([],env) l
  in
  List.rev stmts, env

let convert_enum_constant env kind e =
  let loc = Convert_env.get_loc env in
  match e with
    | EnumCst(name,e,value) ->
        let name, t = Convert_env.typedef_normalize env name TStandard in
        let name =
          if e.ekind_is_extern_c then name.decl_name
          else Mangling.mangle name t None
        in
        (* If the value is negative, create an expression
           with a positive value. *)
        (name,mk_int64_cst env ~kind value,loc)
    | FloatCst _ | IntCst _ | TypeCst _ ->
        Frama_Clang_option.fatal "Enum constant has a wrong kind"

let convert_enum_constants env ikind l =
  List.map (convert_enum_constant env ikind) l

let convert_static_const env loc name ikind kind value does_remove_virtual =
  let env = Convert_env.set_loc env loc in
  let cloc = Cil_datatype.Location.of_lexing_loc loc in
  let qualified_name = Convert_env.qualify env name in
  let name =
    if Convert_env.is_extern_c env then name
    else
      let qualified_name, t
        = Convert_env.typedef_normalize env qualified_name TStandard in
      Mangling.mangle qualified_name t None
  in
  let plain = Int ikind in
  let spec, _ =
    convert_base_type env [SpecCV CV_CONST] id plain does_remove_virtual
  in
  let spec =
    match kind with
    | ICStaticConst -> SpecStorage STATIC :: spec
    | ICLiteral | ICExternConst -> spec
  in
  let init = { expr_loc = cloc;
               expr_node = CONSTANT (CONST_INT (Int64.to_string value))}
  in
  let env = Convert_env.add_global_var env qualified_name plain in
   DECDEF(None,(spec,[(name,JUSTBASE,[],cloc),SINGLE_INIT init]),cloc), env

let remove_this_parameter kind args =
  match kind with
  | FKFunction -> args
  | FKMethod _ | FKCastMethodOperator _ | FKConstructor _ | FKDestructor _
    -> List.tl args

let convert_bitfield_info env l =
  mk_expr env (CONSTANT (CONST_INT (string_of_int l)))

let make_qualified_name env = function
  | Declaration string_name -> (Convert_env.qualify env string_name)
  | Implementation qual_name -> qual_name

let make_class_env env name kind tc is_extern_c =
  let qualified_name = make_qualified_name env name in
  let env = Convert_env.add_aggregate env qualified_name kind tc is_extern_c in
  Convert_env.set_current_class env (qualified_name, tc)

let create_base_field_name env base tb =
  let base, tb = Convert_env.typedef_normalize env base tb in
  "_frama_c_" ^ (Mangling.mangle base tb None)

let bare_suf s = s ^ "_frama_c_bare"

let bare_qname name = { name with decl_name = bare_suf name.decl_name }

let bare_full_name (name,t) = (bare_qname name,t)

let bare_or_derived_type env most_derived n =
  let class_name = if most_derived then n else bare_full_name n in
  Convert_env.struct_or_union env class_name

let make_class_decl env name tkind kind inherits fields body has_virtual =
  let n, t = Convert_env.typedef_normalize env name tkind in
  let class_name = Mangling.mangle n t None in
  let loc = Convert_env.get_loc env in
  let create_class_type base tb =
    { qualifier = []; plain_type = (Struct (base,tb)) }
  in
  let fields, bare_fields, new_env =
    match body with
      | None -> None, None, Convert_env.add_struct env (name, tkind) []
      | Some _ ->
        let rec add_base_class (base, tb) result = match result with
          | [] -> [(base, tb)]
          | x :: l -> if (Fclang_datatype.Qualified_name.equal x (base, tb))
            then x :: l
            else x :: (add_base_class (base, tb) l)
        in
        let rec append_bases l result = match l with
          | [] -> result
          | x :: l' -> (append_bases l' (add_base_class x result))
        in
        let virtual_base_classes =
          match inherits with
            | None -> []
            | Some inherits ->
                List.fold_left
                  (fun result inherits -> match inherits.is_virtual with
                    | VStandard -> 
                      append_bases (Class.get_virtual_base_classes
                        (inherits.base, inherits.templated_kind)) result
                    | VVirtual ->
                      add_base_class (inherits.base, inherits.templated_kind)
                        (append_bases (Class.get_virtual_base_classes
                            (inherits.base, inherits.templated_kind)) result))
                [] inherits
        in
        let virtual_inherited_fields = List.fold_left
          (fun result (base,tb) ->
            let n, t = Convert_env.typedef_normalize env base tb in
            let n' = 
              if Class.has_virtual_base_class (base,tb) then bare_qname n else n
            in (FIELD
               ([SpecType
                   (Tstruct
                      (Mangling.mangle n' t None,
                       None, []))],
                [(create_base_field_name env n t,
                  JUSTBASE, [], loc),
                 None]),
              (create_class_type base tb))
            ::result)
          [] virtual_base_classes
        in
        let has_virtual, inherited_fields =
          match inherits with
            | None -> has_virtual, []
            | Some inherits ->
                List.fold_left
                  (fun (has_virtual,result) inherits ->
                     let n,t =
                       Convert_env.typedef_normalize
                         env inherits.base inherits.templated_kind
                     in
                     let has_virtual =
                       has_virtual || Convert_env.struct_has_virtual env (n,t)
                     in
                     match inherits.is_virtual with
                     | VStandard -> 
                       let n, t = Convert_env.typedef_normalize
                           env inherits.base inherits.templated_kind
                       in
                       let n' = 
                         if Class.has_virtual_base_class
                             (inherits.base,inherits.templated_kind)
                         then bare_qname n
                         else n
                       in
                       has_virtual,
                       (FIELD
                         ([SpecType
                             (Tstruct
                                (Mangling.mangle n' t None,
                                 None, []))],
                          [(create_base_field_name env n t,
                            JUSTBASE, [], loc),
                           None]),
                        (create_class_type
                          inherits.base inherits.templated_kind))
                      :: result
                    | VVirtual -> has_virtual, result)
                (has_virtual, [])
                inherits
        in
        let create_field (cfs, fts) (cf,ft) =
          cf::cfs, match cf with
            | FIELD (_, name_init_list)
              -> (List.fold_left
                 (fun l ((name,_,_,_),_) -> (name, ft)::l) fts name_init_list)
            | _ -> fts
        in
        let cfields, fields_typ =
          List.fold_left create_field ([],[])
            (List.append virtual_inherited_fields
              (List.append fields inherited_fields))
        in
        let env = Convert_env.add_struct env (name,tkind) fields_typ in
        let env =
          if has_virtual then Convert_env.virtual_struct env (name,tkind)
          else env
        in
        let bare_cfields, env =
          match virtual_base_classes with
          | [] -> None, env
          | _ ->
             let bcfields, bfields_typ = 
               (List.fold_left create_field ([],[])
                 (List.append fields inherited_fields))
             in
             let bare = bare_qname name in
             let env = Convert_env.add_aggregate env bare CClass tkind false in
             Some bcfields,
             Convert_env.add_struct env (bare,tkind) bfields_typ
        in
        Some cfields, bare_cfields, env
  in
  let type_decl =
    match kind with
      | CClass | CStruct -> Tstruct (class_name, fields,[])
      | CUnion -> Tunion(class_name, fields,[])
  in
  let bare_type_decl =
    match bare_fields, kind with
    | None, _ | Some _, CUnion -> None
    | Some fields, (CClass | CStruct) ->
      Some (Tstruct (Mangling.mangle (bare_qname n) t None, Some fields,[]))
  in
  let bare_class_decl = match bare_type_decl with
    | None -> None
    | Some tdecl -> Some (ONLYTYPEDEF([SpecType tdecl],loc))
  in
  new_env, (ONLYTYPEDEF([SpecType type_decl],loc)), bare_class_decl

let is_implicit_func = function
  | CMethod(_,_,_,_,_,_,_,b,_,_,_,_) -> b
  | _ -> false

let implicit_kind = function
  | CMethod(_,_,kind,_,args,_,_,_,_,_,_,_) ->
    (match kind, args with
     | FKConstructor false, [_] -> 1 (* default constructor, plain. *)
     | FKConstructor true, [_] -> 2 (* default constructor, derived. *)
     | FKConstructor false,
       [_; { arg_type = { plain_type = LVReference _; qualifier }}]
       when List.mem Const qualifier -> 3 (* copy constructor, const, plain. *)
     | FKConstructor false,
       [_; { arg_type = { plain_type = LVReference _; }}] ->
       (* copy constructor, non-const, plain. *)
       4
     | FKConstructor true,
       [_; { arg_type = { plain_type = LVReference _; qualifier }}]
       when List.mem Const qualifier -> 5 (* copy constructor, const,derived. *)
     | FKConstructor true,
       [_; { arg_type = { plain_type = LVReference _; }}] ->
       (* copy constructor, non-const, derived. *)
       6
     | FKConstructor false,
       [_; { arg_type = { plain_type = RVReference _; qualifier }}]
       when List.mem Const qualifier -> 7 (* move constructor, const, plain. *)
     | FKConstructor false,
       [_; { arg_type = { plain_type = RVReference _; }}] ->
       (* move constructor, non-const, plain. *)
       8
     | FKConstructor true,
       [_; { arg_type = { plain_type = RVReference _; qualifier }}]
       when List.mem Const qualifier -> 9 (* move constructor, const,derived. *)
     | FKConstructor true,
       [_; { arg_type = { plain_type = RVReference _; }}] ->
       (* move constructor, non-const, derived. *)
       10
     | FKMethod _,
       [ _; { arg_type = { plain_type = (Struct _ | Union _); qualifier } }]
       when List.mem Const qualifier -> 11 (*assign operator, const *)
     | FKMethod _,
       [ _; { arg_type = { plain_type = (Struct _ | Union _); } }] ->
       12 (*assign operator, non const *)
     | FKMethod _,
       [ _; { arg_type = { plain_type = LVReference _; qualifier } }]
       when List.mem Const qualifier -> 13 (* assign operator, const *)
     | FKMethod _,
       [ _; { arg_type = { plain_type = LVReference _; } }] ->
       14 (* assign operator, non-const *)
     | FKMethod _,
       [ _; { arg_type = { plain_type = RVReference _; qualifier } }]
       when List.mem Const qualifier -> 15 (* move operator, const *)
     | FKMethod _,
       [ _; { arg_type = { plain_type = RVReference _; } }] ->
       16 (* move operator, non-const *)
     | FKDestructor false, [ _ ] -> 17 (* destructor, plain. *)
     | FKDestructor true, [ _ ] -> 18 (* destructor, derived. *)
     | _ -> 0 (* unknown implicit operator, don't try to sort it. *)
    )
  | _ -> 0 (* unknown declaration, don't try to sort it. *)

let cmp_implicit i1 i2 =
  let n1 = implicit_kind i1 in
  let n2 = implicit_kind i2 in
  compare n1 n2

let reorder_implicit l =
  let implicit,others = List.partition is_implicit_func l in
  let implicit = List.stable_sort cmp_implicit implicit in
  implicit @ others

let iter_on_array ?(incr=true) env idx length mk_body =
  let loc = Convert_env.get_loc env in
  let idx_var = mk_expr env (VARIABLE idx) in
  let const_int i = CONSTANT(CONST_INT (string_of_int i)) in
  let init =
    if incr then const_int 0
    else BINARY(SUB, length,
		{expr_loc=loc;
		 expr_node=const_int 1})
  in
  let last = if incr then length.expr_node else const_int 0 in
  let last_test = if incr then LT else GE in
  let modif = if incr then POSINCR else POSDECR in
  let decl =
    DECDEF(
      None,(
        [SpecType Tunsigned],
        [(idx,JUSTBASE,[],loc),
         SINGLE_INIT (mk_expr env init)]),
      loc)
  in
  let body, def, env = mk_body env idx_var in
  make_stmt env
    (FOR([],FC_DECL decl,
         mk_expr env (BINARY(last_test,idx_var,mk_expr env last)),
         mk_expr env (UNARY(modif,idx_var)), body,loc)),
  def, env

let create_stmt_set_vmt env qualification_class inherits =
  let loc = Convert_env.get_loc env in
  let thisNode = mk_expr env (VARIABLE "this") in
  let vmt_type =
    Cxx_utils.
      (obj_ptr (class_ptr (Cxx_utils.empty_qual "_frama_c_vmt", TStandard)))
  in
  let rt, decl = convert_specifiers env vmt_type true in
  let cvmt_type = rt, decl JUSTBASE in
  let create_stmt_set_shift_vmt (l, previous_index)
      { base = base_class_name;
        templated_kind = t;
        is_virtual = _ (* is_base_virtual *);
        vmt_position = index;
      }
    =
    if (index = previous_index)
    then (l, previous_index)
    else begin
      (* *((_frama_c_vmt ** ) & this->_frama_c__Z1B)
               = & __::_frama_c_vmt_header_for_shift_...; *)
      let base_class_name, t =
        Convert_env.typedef_normalize env base_class_name t
      in
      let field_name =
        "_frama_c" ^ Mangling.mangle base_class_name t None
      in
      let dst =
        mk_expr env
          (UNARY(
              MEMOF,
               mk_cast env cvmt_type
                 (mk_expr env (MEMBEROFPTR (thisNode,field_name)))))
      in
      let vmt_header_for_shift =
        { prequalification = qualification_class;
          decl_name =
            "_frama_c_vmt_header_for_shift_" ^ (string_of_int index) }
      in
      let vmt_header_for_shift, _ =
        Convert_env.typedef_normalize env vmt_header_for_shift TStandard
      in
      let vmt_name =
        Mangling.mangle vmt_header_for_shift TStandard None in
      let src =
        mk_expr env (UNARY(ADDROF, mk_expr env (VARIABLE vmt_name)))
      in
      make_stmt env (COMPUTATION(mk_expr env (BINARY(ASSIGN, dst, src)), loc))
      :: l,
      index
    end
  in
  (* *((_frama_c_vmt ** )this) = & ...::_frama_c_vmt_header; *)
  let dst = mk_expr env (UNARY(MEMOF, mk_cast env cvmt_type thisNode)) in
  let vmt_header =
    { prequalification = qualification_class; decl_name = "_frama_c_vmt_header"}
  in
  let vmt_header, _ = Convert_env.typedef_normalize env vmt_header TStandard in
  let vmt_name = Mangling.mangle vmt_header TStandard None in
  let src = mk_expr env (UNARY(ADDROF, mk_expr env (VARIABLE vmt_name))) in
  List.rev
    (make_stmt env (COMPUTATION(mk_expr env (BINARY(ASSIGN, dst, src)), loc))
     :: (fst (List.fold_left create_stmt_set_shift_vmt ([], 0) inherits)))

let rec add_bare_to_qualification qualif = match qualif with
  | [] -> []
  | [QStructOrClass name] -> [QStructOrClass (bare_suf name)]
  | [QTemplateInstance (name,prms)] -> [QTemplateInstance (bare_suf name, prms)]
  | x::l -> x:: (add_bare_to_qualification l)

(* functions required by the generic implicit body builder to 
   create a given implicit member function. *)
type implicit_operation = 
  { is_copy: bool;
    (* is this a copy/move operation or default constructor or destructor *)
    get_op:
      Convert_env.env -> bool -> qualified_name * tkind -> 
      (qualified_name * signature) option;
    add_op:
      Convert_env.env -> bool -> qualified_name ->
      signature -> Convert_env.env;
    signature: bool -> (qualified_name * tkind) -> signature;
    class_field: expression -> expression -> expression list;
    (* class_field dst src returns the arguments given to the
       corresponding implicit operator (in particular, default
       constructor and destructor won't use the second argument). *)
    plain_field: expression -> expression -> statement;
    (* what to do with scalar fields. assignment or nothing *)
    kind: bool -> funkind;
    name: bool -> (qualified_name * tkind) -> qualified_name;
    return: unit -> statement
      (* what to return -- nothing for constructors, this for operators. *)
  }

let remove_inherited_fields env fields (s,t) =
  let virtual_bases = Class.get_virtual_base_classes (s,t) in
  let bases = Class.get_bases_list (s,t) in
  let non_inherited (name, _) =
    List.for_all
      (fun (qn,tk) -> create_base_field_name env qn tk <> name)
      virtual_bases
      &&
      List.for_all
        (fun i ->
           create_base_field_name env i.base i.templated_kind <> name)
        bases
  in
  List.filter non_inherited fields

let rec implicit_op_call op env most_derived (s, t) dst src =
  let loc = Convert_env.get_loc env in
  let most_derived =
    most_derived || not (Class.has_virtual_base_class (s,t))
  in
  let name, signature, defs, env =
    let class_name = Convert_env.typedef_normalize env s t in
    let opname = op.name most_derived class_name in
    (* Due to the way we translate base operators for classes with virtual
       bases, op_class_name may differ from class_name for those operators.
       Failing to get them would in turn result in duplicate definitions of
       this operators if they are used more than once (i.e. in their own class
       and in another class that inherits from it).
    *)
    let op_class_name =
      Option.get
        (Convert_env.class_name_from_qualifications env opname.prequalification)
    in
    match op.get_op env most_derived op_class_name with
    | None -> create_generic_op op env most_derived class_name
    | Some (name, signature) -> name, signature, [], env
  in
  let cname =
    Mangling.mangle name TStandard (Some (op.kind most_derived, signature))
  in
  let args =
    op.class_field
      (mk_expr env (UNARY (ADDROF, dst))) (mk_expr env (UNARY (ADDROF, src)))
  in
  make_stmt env
    (COMPUTATION(
        mk_expr env (CALL(mk_expr env (VARIABLE cname),args,[])), loc)),
  defs, env

and create_generic_op op env most_derived class_name =
  let loc = Convert_env.get_clang_loc env in
  let kind = op.kind most_derived in
  let is_union =
    match Convert_env.get_aggregate env class_name with
    | (CClass | CStruct),_ -> false
    | CUnion, _ -> true
  in
  let is_destructor =
    match op.kind most_derived with
    | FKDestructor _ -> true
    | _ -> false
  in
  let mytype = bare_or_derived_type env most_derived class_name in
  let has_virtual = Class.has_virtual_base_class class_name in
  let signature = op.signature most_derived class_name in
  let signature = Convert_env.signature_normalize env signature in
  let name = op.name most_derived class_name in
  let env = op.add_op env most_derived name signature in
  let cname =
    Mangling.mangle name TStandard (Some (op.kind most_derived, signature))
  in
  let mk_qual =
    match kind with
    | FKConstructor _ | FKDestructor _ -> Cxx_utils.const_type
    | _ -> Cxx_utils.unqual_type
  in
  let this_arg =
    { arg_type = Cxx_utils.obj_ptr (mk_qual mytype);
      arg_name = "this"; arg_loc = loc }
  in
  let arg_name = "__frama_c_arg_0" in
  let args =
    match signature.parameter with
    | [] -> (* default constructor or destructor. *) [ this_arg ]
    | [ arg_type ] -> (* copy/move constructor/assign operator *)
      [ this_arg;
        { arg_name; arg_type; arg_loc = loc } ]
    | _ ->
      Convert_env.fatal
        env "Unexpected number of arguments for an implicit member function"
  in
  let env, (rt, (n,dt,attrs,loc)) =
    make_prototype
      (Convert_env.get_loc env) env cname kind signature.result
      args signature.variadic false
  in
  let defname = (n,dt,(fc_implicit_attr,[])::attrs,loc) in
  let ret_stmt = op.return () in
  let body, defs, env =
    if is_union then begin
      (* for union, this is simply a memcopy of the whole object, see 12.8§17.*)
      if op.is_copy then begin
        let dst = mk_expr env (UNARY(MEMOF, mk_expr env (VARIABLE "this"))) in
        let src = mk_expr env (UNARY(MEMOF, mk_expr env (VARIABLE arg_name))) in
        let stmt, defs, env =
          create_assign_stmt_type op env (Cxx_utils.unqual_type mytype) dst src
        in
        raw_block [ stmt; ret_stmt ], defs, env
      end else begin
        (* non-scalar members have only trivial operations, otherwise
           the corresponding operation of the union would be deleted, as
           per 9.5§1. Hence, the operation is basically a no-op.
        *)
        raw_block [ ret_stmt ], [], env
      end
    end else if has_virtual && most_derived then begin
      let virtual_fields = Class.get_virtual_base_classes class_name in
      (* most derived operator for a class with virtual base(s): first
         call operators of virtual bases, then call operator of bare class.*)
      let virtual_base_op (stmts, defs, env) (qname, tkind) =
        let name, tkind = Convert_env.typedef_normalize env qname tkind in
        let field_name = create_base_field_name env name tkind in
        let dst =
          mk_expr env (MEMBEROFPTR(mk_expr env (VARIABLE "this"), field_name))
        in
        let src =
          mk_expr
            env (MEMBEROFPTR (mk_expr env (VARIABLE arg_name), field_name))
        in
        let stmt, defs', env =
          implicit_op_call op env true (name, tkind) dst src
        in
        stmt::stmts, defs @ defs', env
      in
      (* We first initialize the virtual bases, then the rest of the class
         as usual. See 12.6.2§10 *)
      let stmts, defs, env =
        List.fold_left virtual_base_op ([],[],env) virtual_fields
      in
      let bare_this = bare_or_derived_type env false class_name in
      let bare_this_ptr = Cxx_utils.(obj_ptr (unqual_type bare_this)) in
      let bare_sig = op.signature false class_name in
      let bare_prm =
        match bare_sig.parameter with
        | [] -> bare_this_ptr (* won't be used anyway *)
        | [ x ] -> x
        | _ :: _ :: _ ->
          Frama_Clang_option.fatal "unexpected signature for implicit operator"
      in
      let bt1,dt1 = convert_specifiers env bare_this_ptr (not most_derived) in
      let t1 = bt1, dt1 JUSTBASE in
      let bt2,dt2 = convert_specifiers env bare_prm (not most_derived) in
      let t2 = bt2, dt2 JUSTBASE in
      let mk_cast t e = mk_expr env (CAST (t, SINGLE_INIT e)) in
      let mk_mem e = mk_expr env (UNARY(MEMOF,e)) in
      let own_stmt, defs', env =
        implicit_op_call
          op env false class_name
          (mk_mem (mk_cast t1 (mk_expr env (VARIABLE "this"))))
          (mk_mem (mk_cast t2 (mk_expr env (VARIABLE arg_name))))
      in
      let stmts =
        (* For destructor, virtual bases are destroyed after
           the complete class. See 12.4§7. *)
        if is_destructor then own_stmt :: stmts @ [ret_stmt ]
        else List.rev_append stmts [ own_stmt; ret_stmt ]
      in
      raw_block stmts, defs @ defs', env
    end else begin
      let inherits = Class.get_bases_list class_name in
      let own_fields = Convert_env.get_struct env class_name in
      let own_fields = remove_inherited_fields env own_fields class_name in
      let dst fname =
        mk_expr env (MEMBEROFPTR (mk_expr env (VARIABLE "this"), fname))
      in
      let src fname =
        mk_expr env (MEMBEROFPTR (mk_expr env (VARIABLE arg_name), fname))
      in
      (* no virtual classes or not most derived operator: just do
           the inherited ops, vmt for current class, then own fields ops *)
      let base_op (stmts, defs, env as acc) inh =
        let field_name =
          create_base_field_name env inh.base inh.templated_kind
        in
        let src = src field_name in
        let dst = dst field_name in
        match inh.is_virtual with
        | VVirtual -> acc
        | VStandard ->
          let stmt, defs', env =
            implicit_op_call
              op env false (inh.base, inh.templated_kind) dst src
          in
          stmt :: stmts, defs @ defs', env
      in
      let stmts, defs, env =
        List.fold_left base_op ([], [], env) inherits
      in
      let stmts =
        (* For default constructor and destructor: position vmt accordingly. *)
        if not op.is_copy &&
           Convert_env.struct_has_virtual env class_name
        then begin
          let quals =
            Convert_env.get_namespace
              (Convert_env.set_namespace_from_class env class_name)
          in
          create_stmt_set_vmt env quals inherits @ stmts
        end else stmts
      in
      let stmts = if is_destructor then List.rev stmts else stmts in
      let field_op (stmts, defs, env) (fname, ftype) =
        let src = src fname in
        let dst = dst fname in
        let stmt, defs', env = create_assign_stmt_type op env ftype dst src in
        stmt::stmts, defs @ defs', env
      in
      let stmts, defs, env =
        List.fold_left field_op (stmts, defs, env) own_fields
      in
      raw_block (List.rev_append stmts [ret_stmt]), defs, env
    end
  in
  let loc = Convert_env.get_loc env in
  let def = FUNDEF(None, (rt, defname), body,loc,loc) in
  name, signature, def::defs, env

and create_assign_stmt_type op env typ dst src =
  let loc = Convert_env.get_loc env in
  match typ.plain_type with
    | Void | Int _ | Enum _ | Float _
    | Pointer _ | LVReference _ | RVReference _ ->
      op.plain_field dst src, [], env
    | Array { subtype; dimension = Some dim } ->
        let mk_subobj env idx_var =
          let src = mk_expr env (INDEX (src,idx_var)) in
          let dst = mk_expr env (INDEX (dst,idx_var)) in
          create_assign_stmt_type op env subtype dst src
        in
        let _,_,cdim = convert_expr env empty_aux dim false in
        let idx_name = Convert_env.temp_name env "idx" in
        let lenv = Convert_env.add_local_var env idx_name (Int IULong) in
        let stmt, defs, lenv =
          iter_on_array lenv idx_name cdim mk_subobj
        in
        stmt, defs, Convert_env.unscope lenv env
    | Array { dimension = None} ->
        (* GNU extension. Treat it as a an empty field. *)
        make_stmt env (NOP loc), [], env
    | Union (s,t) ->
      (* TODO: check whether the union has a user-provided copy constructor.
         Otherwise, the implicit default is to copy the object representation
         (C++11, [class.copy]§17)
      *)
      if op.is_copy then begin
        let s, t = Convert_env.typedef_normalize env s t in
        let ctyp = Tunion (Mangling.mangle s t None,None,[]) in
        make_stmt env
          (COMPUTATION
             (mk_expr env
                (CALL(
                    mk_expr env (VARIABLE "Frama_C_memcpy"),
                    [mk_expr env (UNARY(ADDROF,dst));
                     mk_expr env (UNARY(ADDROF,src));
                     mk_expr env (TYPE_SIZEOF([SpecType ctyp],JUSTBASE))],[])),
              loc)),
        [], env
      end else
        (* No initialization is performed by default constructor, cf 12.6.2§8.
           No destructor call for variant members, cf 12.4§7.
        *)
        make_stmt env (NOP loc), [], env
    | Struct (s,t) ->
      let class_name = Convert_env.typedef_normalize env s t in
      implicit_op_call op env true class_name dst src
    | Named (s,_) ->
      let typ = (Convert_env.get_typedef env s).plain_type in
      let qtyp = { qualifier = []; plain_type = typ } in
      create_assign_stmt_type op env qtyp dst src
    | Lambda _ -> op.plain_field dst src, [], env

let op_name opname most_derived (qname,tkind) =
  let qname = Cxx_utils.meth_name qname tkind opname in
  if most_derived then qname
  else
    { qname with
      prequalification = add_bare_to_qualification qname.prequalification }

let create_default_constructor env most_derived class_name =
  let loc = Convert_env.get_loc env in
  let get_op env most_derived =
    if most_derived then
      Convert_env.get_option_default_constructor env
    else
      Convert_env.get_option_default_constructor_base env
  in
  let add_op env most_derived =
    if most_derived then
      Convert_env.add_default_constructor env
    else
      Convert_env.add_default_constructor env
  in
  let class_field dst _ = [ dst ] in
  (* TODO: add in intermediate_format.ast information about initializer
     of corresponding fields. See 12.6.2§8 *)
  let plain_field _ _ = make_stmt env (NOP loc) in
  let kind most_derived = FKConstructor most_derived in
  let name _ (qname, tkind) =
    Cxx_utils.meth_name qname tkind qname.decl_name
  in
  let signature _ _ =
    { result = Cxx_utils.unqual_type Void; parameter = []; variadic = false }
  in
  let return () =
    make_stmt env (RETURN ({ expr_loc = loc; expr_node = NOTHING}, loc))
  in
  create_generic_op
    { is_copy = false;
      get_op; add_op; class_field; plain_field; kind; name; signature; return }
    env most_derived class_name

let create_copy_constructor env most_derived class_name =
  let loc = Convert_env.get_loc env in
  let get_op env most_derived =
    if most_derived then
      Convert_env.get_option_copy_constructor env
    else
      Convert_env.get_option_copy_constructor_base env
  in
  let add_op env most_derived =
    if most_derived then
      Convert_env.add_copy_constructor env
    else
      Convert_env.add_copy_constructor_base env
  in
  let kind most_derived = FKConstructor most_derived in
  let name _ (qname, tkind) =
    Cxx_utils.meth_name qname tkind qname.decl_name
  in
  let class_field dst src = [ dst; src ] in
  let plain_field dst src =
    make_stmt env (COMPUTATION(mk_expr env (BINARY(ASSIGN,dst,src)), loc))
  in
  let signature most_derived class_name =
    let result = Cxx_utils.unqual_type Void in
    let mytype = bare_or_derived_type env most_derived class_name in
    let parameter = [ Cxx_utils.(obj_lvref (const_type mytype)) ] in
    { result; parameter; variadic = false }
  in
  let return () =
    make_stmt env (RETURN ({ expr_loc = loc; expr_node = NOTHING}, loc))
  in
  create_generic_op
    { is_copy = true;
      get_op; add_op; kind; name; signature; class_field; plain_field; return }
    env most_derived class_name

let create_move_constructor env most_derived class_name =
  let loc = Convert_env.get_loc env in
  let get_op env most_derived =
    if most_derived then
      Convert_env.get_option_move_constructor env
    else
      Convert_env.get_option_move_constructor_base env
  in
  let add_op env most_derived =
    if most_derived then
      Convert_env.add_move_constructor env
    else
      Convert_env.add_move_constructor_base env
  in
  let kind most_derived = FKConstructor most_derived in
  let name _ (qname, tkind) =
    Cxx_utils.meth_name qname tkind qname.decl_name
  in
  let class_field dst src = [ dst; src ] in
  let plain_field dst src =
    make_stmt env (COMPUTATION(mk_expr env (BINARY(ASSIGN,dst,src)), loc))
  in
  let signature most_derived class_name =
    let result = Cxx_utils.unqual_type Void in
    let mytype = bare_or_derived_type env most_derived class_name in
    let parameter = [Cxx_utils.(obj_rvref (unqual_type mytype))] in
    { result; parameter; variadic = false }
  in
  let return () =
    make_stmt env (RETURN ({ expr_loc = loc; expr_node = NOTHING}, loc))
  in
  create_generic_op
    { is_copy = true;
      get_op; add_op; kind; name; signature; class_field; plain_field; return }
    env most_derived class_name

let create_assign_operator env most_derived class_name =
  let loc = Convert_env.get_loc env in
  let get_op env most_derived =
    if most_derived then
      Convert_env.get_option_assign_operator env
    else
      Convert_env.get_option_assign_operator_base env
  in
  let add_op env most_derived =
    if most_derived then
      Convert_env.add_assign_operator env
    else
      Convert_env.add_assign_operator_base env
  in
  let kind _ = FKMethod [] in
  let name = op_name "operator=" in
  let class_field dst src = [ dst; src ] in
  let plain_field dst src =
    make_stmt env (COMPUTATION(mk_expr env (BINARY(ASSIGN,dst,src)), loc))
  in
  let signature most_derived class_name =
    let mytype = bare_or_derived_type env most_derived class_name in
    let result = Cxx_utils.(obj_lvref (unqual_type mytype)) in
    let parameter = [Cxx_utils.(obj_lvref (const_type mytype))] in
    { result; parameter; variadic = false }
  in
  let return () =
    make_stmt env
      (RETURN ({expr_loc = loc; expr_node = VARIABLE "this"}, loc))
  in
  create_generic_op
    { is_copy = true;
      get_op; add_op; kind; name; signature; class_field; plain_field; return }
    env most_derived class_name

let create_move_operator env most_derived class_name =
  let loc = Convert_env.get_loc env in
  let get_op env most_derived =
    if most_derived then
      Convert_env.get_option_move_operator env
    else
      Convert_env.get_option_move_operator_base env
  in
  let add_op env most_derived =
    if most_derived then
      Convert_env.add_move_operator env
    else
      Convert_env.add_move_operator_base env
  in
  let kind _ = FKMethod [] in
  let name = op_name "operator=" in
  let class_field dst src = [ dst; src ] in
  let plain_field dst src =
    make_stmt env (COMPUTATION(mk_expr env (BINARY(ASSIGN,dst,src)), loc))
  in
  let signature most_derived class_name =
    let mytype = bare_or_derived_type env most_derived class_name in
    let result = Cxx_utils.(obj_lvref (unqual_type mytype)) in
    let parameter = [Cxx_utils.(obj_rvref (unqual_type mytype))] in
    { result; parameter; variadic = false }
  in
  let return () =
    make_stmt env (RETURN ({ expr_loc = loc; expr_node = VARIABLE "this"}, loc))
  in
  create_generic_op
    { is_copy = true;
      get_op; add_op; kind; name; signature; class_field; plain_field; return }
    env most_derived class_name

let create_destructor env most_derived class_name =
  let loc = Convert_env.get_loc env in
  let add_op env most_derived class_name _ =
    if most_derived then
      Convert_env.add_destructor env class_name.prequalification
    else
      Convert_env.add_destructor_base env class_name.prequalification
  in
  let name _ (s,t) = Cxx_utils.meth_name s t ("~" ^ s.decl_name) in
  let signature _ _ =
    { result = Cxx_utils.unqual_type Void; parameter = []; variadic = false }
  in
  (* TODO: Handle the case where the destructor is virtual *)
  let get_op env most_derived class_name =
    let has_dest =
      if most_derived then
        Convert_env.has_destructor env class_name
      else
        Convert_env.has_destructor_base env class_name
    in
    if has_dest then
      Some (name most_derived class_name, signature most_derived class_name)
    else None
  in
  let class_field dst _ = [ dst ] in
  let plain_field _ _ = make_stmt env (NOP loc) in
  let kind most_derived = FKDestructor most_derived in
  let return () =
    make_stmt env (RETURN ({ expr_loc = loc; expr_node = NOTHING}, loc))
  in
  create_generic_op
    { is_copy = false;
      add_op; name; signature; get_op; class_field; plain_field; kind; return }
    env most_derived class_name

let create_implicit_body env kind args class_name =
  (* NB: the this parameter is present in the args list. *)
  match kind, args with
  | FKConstructor derived, [ _ ] ->
    create_default_constructor env derived class_name
  | FKConstructor d, [ _; { arg_type = { plain_type = LVReference _ } } ] ->
    create_copy_constructor env d class_name
  | FKConstructor d, [ _; { arg_type = { plain_type = RVReference _ } } ] ->
    create_move_constructor env d class_name
  | FKMethod _, [ _; { arg_type = { plain_type = (Struct _ | Union _) } }] ->
    create_assign_operator env true class_name
  | FKMethod _, [ _; { arg_type = { plain_type = LVReference _ } }] ->
      create_assign_operator env true class_name
  | FKMethod _, [ _; { arg_type = { plain_type = RVReference _ } }] ->
    create_move_operator env true class_name
  | FKDestructor d, [ _ ] ->
    create_destructor env d class_name
  | _ ->
      Frama_Clang_option.not_yet_implemented
        "Don't know this kind of implicitly defined member function"

let has_default_value _arg = false
(* TODO: export this information from clang *)

let is_assign_operator s = s = "operator="

let add_special_member env name kind rt args =
  let (class_name, tc) =
    Option.get
      (Convert_env.class_name_from_qualifications env name.prequalification)
  in
  let signature args =
    { result = rt;
      parameter = List.map (fun a -> a.arg_type) args;
      variadic = false
    }
  in
  let rec is_own_class t =
    match t.plain_type with
      | Struct (s,ts)
      | Union (s,ts)
        -> Fclang_datatype.Qualified_name.equal (s,ts) (class_name, tc)
      | Named (s,_) when Cxx_utils.is_builtin_qual_type s -> false
      | Named (s,_) -> is_own_class { qualifier = [];
                       plain_type = (Convert_env.get_typedef env s).plain_type}
      | _ -> false
  in
  match kind, args with
    | FKConstructor d, _::l when List.for_all has_default_value l ->
      (if d then Convert_env.add_default_constructor
       else Convert_env.add_default_constructor_base)
        env name (signature l)
    | FKConstructor d, 
      _::({arg_type= { plain_type = LVReference (PDataPointer t) }}::l as args)
        when is_own_class t && List.for_all has_default_value l ->
      (if d then Convert_env.add_copy_constructor
       else Convert_env.add_copy_constructor_base)
        env name (signature args)
    | FKConstructor d,
      _::({arg_type= { plain_type = RVReference (PDataPointer t) }}::l as args)
        when is_own_class t && List.for_all has_default_value l ->
      (if d then Convert_env.add_move_constructor
       else Convert_env.add_move_constructor_base)
        env name (signature args)
    | FKMethod [],_::([{arg_type = t}] as args) when
        is_own_class t && is_assign_operator name.decl_name ->
      Convert_env.add_assign_operator env name (signature args)
    | FKMethod [],
          _::([{arg_type ={plain_type = LVReference (PDataPointer t)}}] as args)
            when is_own_class t && is_assign_operator name.decl_name ->
      Convert_env.add_assign_operator env name (signature args)
    | FKMethod [],
          _::([{arg_type ={plain_type = RVReference (PDataPointer t)}}] as args)
            when is_own_class t && is_assign_operator name.decl_name ->
      Convert_env.add_move_operator env name (signature args)
    | FKDestructor d, _ ->
      (if d then Convert_env.add_destructor
       else Convert_env.add_destructor_base)
        env name.prequalification
    | _ -> env

let add_arg_names l =
  let new_name idx = if idx = -1 then "x" else "x" ^ (string_of_int idx) in
  List.rev 
    (fst
       (List.fold_left
          (fun (acc,idx) arg ->
            if arg.arg_name = "" then
              { arg with arg_name = new_name idx }::acc, idx+1
            else arg::acc,idx)
          ([],(-1))
          l))

let convert_contract env spec =
  Convert_acsl.convert_function_contract env spec,
  Convert_env.get_loc env

let constify_receiver kind args =
  match kind, args with
  | (FKConstructor _ | FKDestructor _), this :: args ->
    let this =
      { this with arg_type = Cxx_utils.force_ptr_to_const this.arg_type }
    in
    this :: args
  | _ -> args

let is_pure_templated_decl kind body has_further_definition =
  kind <> TStandard && body = None && not has_further_definition

let rec collect_class_components env body =
  List.fold_left
    convert_class_component (env,[],[],[],[]) (reorder_implicit body)

(* Note: the list of others global definition must be built in reverse
   order, as it will be reverted by the callers. *)
and convert_class_component (env, implicits, types, fields, others) meth =
  match meth with
    | CMethod(loc,name,kind,return_type,all_args,variadic,body,implicit,tkind,
              has_further_definition,_(*throws*),spec) ->
      let qname = Convert_env.qualify env name in
      let class_name =
        Option.get
          (Convert_env.class_name_from_qualifications
             env qname.prequalification)
      in
      let env = Convert_env.set_loc env loc in
      let cloc = Cil_datatype.Location.of_lexing_loc loc in
      let env = add_special_member env qname kind return_type all_args in
      let all_args = if implicit then add_arg_names all_args else all_args in
      let args = remove_this_parameter kind all_args in
      let args_sig = List.map (fun x -> x.arg_type) args in
      let benv = Convert_env.add_formal_parameters env all_args in
      let benv = Convert_env.set_current_func_name benv qname in
      let benv =
        Convert_env.set_current_return_type benv return_type.plain_type
      in
      let qname,tkind= Convert_env.typedef_normalize env qname tkind in
      let signature = {result= return_type; parameter= args_sig; variadic } in
      let signature = Convert_env.signature_normalize env signature in
      let name = Mangling.mangle qname tkind (Some(kind,signature)) in
      let spec = Option.map (convert_contract benv) spec in
      let extern_c = false in
      let spec =
        if has_further_definition
        then spec
        else
          Generate_spec.add_contract ~env:benv ~kind ~return_type ~args
            ~variadic ~implicit ~extern_c spec
      in
      let all_args = constify_receiver kind all_args in
      let env, (rt,(n,dt,a,loc as name)) =
        make_prototype cloc benv name kind return_type all_args variadic false
      in
      let name =
        if implicit then
          (n,dt,(fc_implicit_attr,[])::a,loc)
        else if is_pure_templated_decl tkind body has_further_definition then
          (n,dt, (fc_pure_template_decl_attr,[])::a,loc)
        else name
      in
      let has_virtual_base = Class.has_virtual_base_class class_name in
      (match body with
        | None ->
          let implicits =
            if implicit && not has_further_definition
            then (kind,all_args)::implicits
            else implicits
          in
          let env = Convert_env.reset_func env in
          (env,implicits, types, fields,
           DECDEF(spec,(rt,[name,NO_INIT]),cloc)::others)
        | Some body ->
          if (not has_virtual_base)
            || Frama_Clang_option.Cxx_virtual_bare_methods_in_clang.get ()
          then
            let body, benv = convert_block benv body false in
            let env = Convert_env.reset_func benv in
              (env,implicits,types,fields,
               FUNDEF(spec,(rt,name),body,cloc,cloc) :: others)
          else
            let cbody, benv = convert_block benv body false in
            let cbody_bare, benv = convert_block benv body true in
            let benv, defname_bare =
              make_prototype cloc benv
                (Mangling.mangle
                  { qname with prequalification
                    = add_bare_to_qualification qname.prequalification }
                  tkind (Some(kind,signature)))
                kind return_type all_args variadic false
            in
            let env = Convert_env.reset_func benv in
              (env,implicits,types,fields,
               FUNDEF(spec,(rt,name),cbody,cloc,cloc)
               :: FUNDEF(spec,defname_bare,cbody_bare,cloc,cloc)
               :: others))
    | CCompound(loc,name,kind,inherits,body,tkind,has_virtual) ->
      let new_env = Convert_env.set_loc env loc in
      let qualified_name = Convert_env.qualify new_env name in
      let new_env =
        make_class_env new_env (Declaration name) kind tkind false
      in
      let new_env,new_implicits,subtypes,subfields,subothers =
        match body with
          | None -> new_env, [], [], [], []
          | Some body -> collect_class_components new_env body
      in
      let new_env, class_decl, bare_class_decl =
        make_class_decl
          new_env qualified_name tkind kind inherits subfields body has_virtual
      in
      let qualified_name, tkind =
        Convert_env.typedef_normalize env qualified_name tkind
      in
      let new_env, my_implicits =
        List.fold_left
          (fun (env, acc) (kind, args) ->
             let _, _, defs, env =
               create_implicit_body env kind args (qualified_name, tkind)
             in
             env, acc @ defs)
          (new_env, []) new_implicits
      in
      let subothers = my_implicits @ subothers in
      Class.add_class (qualified_name,tkind);
      Option.iter
        (List.iter (Class.add_inheritance_relation(qualified_name, tkind)))
        inherits;
      Convert_env.reset_current_class new_env,
      implicits,
      (match bare_class_decl with
        | None -> class_decl::(List.append subtypes types)
        | Some bare_class_decl -> bare_class_decl::(class_decl
            ::(List.append subtypes types))),
      fields,
      List.append subothers others
    | CFieldDecl(loc, name, typ, bf_info, is_mutable) ->
      let env = Convert_env.set_loc env loc in
      let cloc = Cil_datatype.Location.of_lexing_loc loc in
      let base,decl = convert_specifiers env typ false in
      (* We remove static qualifier to avoid confusion with the C's static. *)
      let base =
        List.filter (function SpecStorage(STATIC)-> false | _ -> true) base
      in
      let base =
        if is_mutable then
          SpecAttr (add_attr env Cil.frama_c_mutable []) :: base
        else base
      in
      if is_static typ.qualifier then begin
        let attrs = add_fc_destructor_attr env typ [] in
        (* we have actually an extern declaration in C sense: its definition
           might reside in another translation unit. *)
        let base = SpecStorage EXTERN :: base in
        let name = Convert_env.qualify env name in
        let cname,_= Convert_env.typedef_normalize env name TStandard in
        let cname = Mangling.mangle cname TStandard None in
        Convert_env.add_global_var env name typ.plain_type,
        implicits,
        types,
        fields,
        DECDEF(
          None,
          (base, [(cname, decl JUSTBASE, attrs,cloc),NO_INIT]), cloc)
        ::others
      end else begin
        (* no need to mangle names: they can be shared by various structures *)
        let bf_length = Option.map (convert_bitfield_info env) bf_info in
        (env,implicits,
         types,
         (FIELD(base,[(name,decl JUSTBASE,[],cloc),bf_length]), typ) ::fields,
         others)
      end
    | CTypedef (loc,name,typ) ->
      let env = Convert_env.set_loc env loc in
      let cloc = Cil_datatype.Location.of_lexing_loc loc in
      let qual_name = Convert_env.qualify env name in
      let env = Convert_env.add_typedef env qual_name typ in
      let name,_= Convert_env.typedef_normalize env qual_name TStandard in
      let name = Mangling.mangle name TStandard None in
      let base,decl = convert_specifiers env typ false in
      (env,implicits,
       TYPEDEF((SpecTypedef::base,[(name,decl JUSTBASE,[],cloc)]),cloc)
       ::types,
       fields,
       others)
    | CStaticConst(loc,name, ikind,_,value) ->
      (* static in the case of a class does not mean internal storage,
         but static data member. The resulting variable should not be tagged
         with static storage qualifier in C. *)
      let decl, env =
        convert_static_const env loc name ikind ICLiteral value false
      in
      (env,implicits,types,fields,decl :: others)
    | CEnum(loc,name,ikind, body) ->
      let env = Convert_env.set_loc env loc in
      let cloc = Cil_datatype.Location.of_lexing_loc loc in
      let name, _ = Convert_env.typedef_normalize env
            (Convert_env.qualify env name) TStandard in
      let name = Mangling.mangle name TStandard None
      in
      let tags = Option.map (convert_enum_constants env ikind) body in
      (env, implicits,
       ONLYTYPEDEF([SpecType (Tenum(name,tags,[]))],cloc) :: types,
       fields, others)
    | Class_annot(loc,annot) ->
      let env = Convert_env.set_loc env loc in
      let annot = Convert_acsl.convert_annot env annot in
      (env,implicits,types,fields,GLOBANNOT [annot]:: others)

and convert_class env name tkind kind inherits body has_virtual =
  let qualified_name = make_qualified_name env name in
  let this_env = make_class_env env name kind tkind false in
  let new_env, implicits, types, fields, others =
    match body with
    | None -> this_env, [], [], [], []
    | Some body -> collect_class_components this_env body
  in
  let new_env, decl, bare_decl =
    make_class_decl
      new_env qualified_name tkind kind inherits fields body has_virtual
  in
  let new_env, my_implicits =
    List.fold_left
      (fun (env, acc) (kind, args) ->
         let _,_,defs,env =
           create_implicit_body env kind args (qualified_name, tkind)
         in
         env, acc @ defs)
      (new_env, [])
      implicits
  in
  (* implicit definitions might depend on internal defs, in particular in
     presence of nested classes that occur as data member of the current class.
  *)
  let add_glob = Extlib.swap Convert_env.add_c_global in
  new_env |>
  List.fold_right add_glob types |>
  Extlib.opt_fold add_glob bare_decl |>
  add_glob decl |>
  List.fold_right add_glob others |>
  List.fold_right add_glob my_implicits |>
  Convert_env.reset_current_class

let rec convert_pod_field (cfields, typs, env) field =
  match field with
  | CFieldDecl(loc, name, typ, bf_info,is_mutable) ->
    let env = Convert_env.set_loc env loc in
    let cloc = Cil_datatype.Location.of_lexing_loc loc in
    let base,decl = convert_specifiers env typ false in
    let base =
      if is_mutable then
        SpecAttr (add_attr env Cil.frama_c_mutable []) :: base
      else base
    in
    let bf_length = Option.map (convert_bitfield_info env) bf_info in
    FIELD(base, [(name,decl JUSTBASE,[],cloc),bf_length])::cfields,
    (name, typ) :: typs, env
  | CCompound(_, name, kind, _, body, tn, _) ->
      let dname = Declaration name in
      let env = convert_pod env dname kind tn body in
      cfields, typs, env
  | _ ->
    Convert_env.fatal env "Unknown declaration in extern C structure definition"

and convert_pod env name kind tn body =
  let loc = Convert_env.get_loc env in
  let name =
    match name with
    | Declaration name -> name
    | Implementation name -> name.decl_name
  in
  let env =
    Convert_env.add_aggregate env (Cxx_utils.empty_qual name) kind tn true
  in
  let fields, env =
    match body with
      | None -> None, env
      | Some body ->
        let fields, typs, env =
          List.fold_left convert_pod_field ([], [], env) body
        in
        Some (List.rev fields),
        Convert_env.add_struct
          env (Cxx_utils.empty_qual name,tn) (List.rev typs)
  in
  let type_decl =
    match kind with
      | CClass | CStruct -> Tstruct (name, fields, [])
      | CUnion -> Tunion(name, fields,[])
  in
  Convert_env.add_c_global
    env (ONLYTYPEDEF ([SpecType type_decl], loc))

let convert_class env name tkind kind inherits body has_virtual =
  if Convert_env.is_extern_c env then convert_pod env name kind tkind body
  else convert_class env name tkind kind inherits body has_virtual

let make_global_cons_init env name init =
  let loc = Convert_env.get_loc env in
  FUNDEF(None,([SpecType Tvoid; SpecAttr("__constructor__",[])],
               ("__fc_init" ^ name, PROTO(JUSTBASE,[],[],false),[],loc)),
         { blabels = []; battrs = []; bstmts = init }, loc, loc)

let builtins = [ "__builtin_va_start" ]

let do_not_translate name =
  let id =
    match name with
      | Declaration name -> name
      | Implementation name -> name.decl_name
  in
  List.mem id builtins

let extract_name = Reorder_defs.name_of_glob

let add_cons_init env d body =
  match d with
  | DECDEF (spec,
            (t, [(name, dt, attrs, loc),
                 SINGLE_INIT ({expr_node = CALL _} as call)]),
            loc1)
    ->
    let expr =
      mk_expr_l loc1 (BINARY (ASSIGN, mk_var_l loc1 name, call))
    in
    let env =
      Convert_env.add_c_global env
        (DECDEF(spec, (t,[(name,dt,attrs,loc),NO_INIT]),loc1))
    in
    Convert_env.add_c_global env
      (make_global_cons_init env name
         (body @ [make_stmt env (COMPUTATION (expr, loc))]))
  | DECDEF (spec,
            (t, [(name, dt, attrs, loc),
                 SINGLE_INIT ({expr_node = GNU_BODY b})]),
            loc1)
    ->
    let env =
      Convert_env.add_c_global env
        (DECDEF(spec, (t,[(name,dt,attrs,loc),NO_INIT]),loc1))
    in
    Convert_env.add_c_global env
      (make_global_cons_init env name
         (body @ [make_stmt env (BLOCK (b, loc,loc))]))
  | _ ->
    (match body with
       | [] -> Convert_env.add_c_global env d
       | _ ->
         let name = extract_name d in
         let env = Convert_env.add_c_global env d in
         Convert_env.add_c_global env (make_global_cons_init env name body))

let add_glob_temp env defs (def,init_stmt) =
  let defs =
    match init_stmt with
    | None -> defs
    | Some { stmt_node } -> make_stmt env stmt_node :: defs
  in
  match def with
  | None -> defs
  | Some def -> make_stmt env (DEFINITION def) :: defs

let is_frama_clang_array_init_name = function
  | Implementation { decl_name } ->
    let prefix = "__fc_init_array" in
    let l = String.length prefix in 
    l <= String.length decl_name && String.sub decl_name 0 l = prefix
  | Declaration _ -> false 
(* NB: we should have a loc for the declaration itself
   as well as for the body*)
let rec convert_global env glob =
  match glob with
    | GlobalAnnotation(loc,annot) ->
      let env = Convert_env.set_loc env loc in
      let annot = Convert_acsl.convert_annot env annot in
      Convert_env.add_c_global env (GLOBANNOT [annot])
    | Function (name, _, _, _, _, _, _, _, _, _, _, _, _)
        when do_not_translate name
      -> env
    | Function(name, kind, loc, return_type,all_args,
               body, extern_c, ghost, variadic, tkind, has_further_definition,
               _ (* throws *), spec) ->
      let attrs =
        if is_frama_clang_array_init_name name then
          [ SpecAttr("__constructor__", [])]
        else []
      in
      let all_args = constify_receiver kind all_args in
      let env = Convert_env.set_loc env loc in
      let cloc = Cil_datatype.Location.of_lexing_loc loc in
      let benv = Convert_env.set_extern_c env extern_c in
      let benv = Convert_env.set_ghost benv ghost in
      let args = remove_this_parameter kind all_args in
      let args_sig = List.map (fun x -> x.arg_type) args in
      let benv = Convert_env.add_formal_parameters benv all_args in
      let qualified_name = make_qualified_name benv name in
      let benv = Convert_env.set_current_func_name benv qualified_name in
      let benv =
        Convert_env.set_current_return_type benv return_type.plain_type
      in
      let qname =
        if extern_c then qualified_name.decl_name
        else
          let qualified_name, tkind = Convert_env.typedef_normalize env
                qualified_name tkind in
          let signature
            = { result = return_type; parameter = args_sig; variadic } in
          let signature = Convert_env.signature_normalize env signature in
          Mangling.mangle qualified_name tkind (Some (kind, signature))
      in
      let spec = Option.map (convert_contract benv) spec in
      let implicit = false in
      let spec =
        if has_further_definition then spec
        else
          Generate_spec.add_contract
            ~env:benv ~kind ~return_type ~args ~variadic ~implicit ~extern_c spec
      in
      let benv, (rt, name) =
        make_prototype cloc benv qname kind return_type all_args variadic false
      in
      let get_class_from_this_type t =
        match t.plain_type with
        | Pointer (PDataPointer { plain_type = Struct (s,ts) | Union(s,ts) }) ->
          (s,ts)
        | _ -> Frama_Clang_option.fatal "bad type for this"
      in let has_virtual_base =
        match kind with
          | FKConstructor _ -> Class.has_virtual_base_class
              (get_class_from_this_type (List.hd all_args).arg_type)
          | FKDestructor _ -> Class.has_virtual_base_class
              (get_class_from_this_type (List.hd all_args).arg_type)
          | _ -> false
      in
      let rt = rt @ attrs in
      (match body with
        | None ->
          let glob = DECDEF(spec,(rt,[name,NO_INIT]), cloc) in
          let env = Convert_env.add_c_global benv glob in
          Convert_env.reset_func env
        | Some body ->
          if (not has_virtual_base)
            || Frama_Clang_option.Cxx_virtual_bare_methods_in_clang.get ()
          then
            let body, benv = convert_block benv body false in
            let glob = FUNDEF(spec,(rt,name),body,cloc,cloc) in
            let env = Convert_env.add_c_global benv glob in
            Convert_env.reset_func env
          else
            let cbody, benv = convert_block benv body false in
            let cbody_bare, benv = convert_block benv body true in
            let qname_bare =
              let qualified_name, tkind = Convert_env.typedef_normalize env
                    qualified_name tkind in
              let signature
                = { result = return_type; parameter = args_sig; variadic } in
              let signature = Convert_env.signature_normalize env signature in
              Mangling.mangle
                { qualified_name with prequalification
                  = add_bare_to_qualification qualified_name.prequalification }
                tkind (Some (kind, signature))
            in let benv, (rt_bare, name_bare) =
              make_prototype
                cloc benv qname_bare kind return_type all_args variadic false
            in
            let gbare = FUNDEF(spec,(rt_bare,name_bare),cbody_bare,cloc,cloc) in
            let glob = FUNDEF(spec,(rt,name),cbody,cloc,cloc) in
            let env = Convert_env.add_c_global benv gbare in
            let env = Convert_env.add_c_global env glob in
            Convert_env.reset_func env
           )
    | Compound(loc,name,kind,inherits,body,has_virtual,tc, is_extern_c,ghost) ->
      let old_ghost = Convert_env.is_ghost env in
      let env = Convert_env.set_loc env loc in
      let env = Convert_env.set_extern_c env is_extern_c in
      let env = Convert_env.set_ghost env ghost in
      let qualified_name =
        match name with
          | Declaration n -> Convert_env.qualify env n
          | Implementation n -> n
      in
      let qualified_name, tc =
        Convert_env.typedef_normalize env qualified_name tc
      in
      Class.add_class (qualified_name,tc);
      Option.iter
        (List.iter (Class.add_inheritance_relation(qualified_name,tc)))
        inherits;
      let env = convert_class env name tc kind inherits body has_virtual in
      Convert_env.set_ghost env old_ghost
    | GlobalVarDecl(loc,name,typ,init,is_extern_c, ghost) ->
      let env = Convert_env.set_loc env loc in
      let cloc = Cil_datatype.Location.of_lexing_loc loc in
      let env = Convert_env.set_extern_c env is_extern_c in
      let qualified_name = make_qualified_name env name in
      let name =
        if is_extern_c
        then qualified_name.decl_name
        else
          let n', t' = Convert_env.typedef_normalize env
                qualified_name TStandard in
          Mangling.mangle n' t' None
      in
      let rt, decl = convert_specifiers env typ false in
      let attrs = add_fc_destructor_attr env typ [] in
      let env = Convert_env.add_global_var env qualified_name typ.plain_type in
      let old_ghost = Convert_env.is_ghost env in
      let env = Convert_env.set_ghost env ghost in
      let init, init_func, env =
        match init with
        | None -> NO_INIT, [], env
        | Some init ->
          let var = Global qualified_name in
          let env, aux, init, e = convert_initializer env typ var init false in
          (match aux, e with
           | [], None -> init, [], env
           | [], Some stmt -> NO_INIT, [ stmt ], env
           | tmps, Some stmt  ->
             assert (init = NO_INIT);
             let init_body = List.fold_left (add_glob_temp env) [ stmt ] tmps in
             NO_INIT, init_body, env
           | tmps, None ->
             let var = { expr_loc = cloc; expr_node = VARIABLE name } in
             let init_body = mk_compound_init env var typ init in
             let init_func =
               match init_body with
               | NOP _ -> []
               | BLOCK({ bstmts }, _,_) -> bstmts
               | _ -> [make_stmt env init_body]
             in
             let init_all =
               List.fold_left (add_glob_temp env) init_func tmps
             in
             NO_INIT, init_all, env
          )
      in
      let my_def =
        DECDEF(None,(rt,[(name,decl JUSTBASE,attrs,cloc),init]),cloc)
      in
      let env = add_cons_init env my_def init_func in
      Convert_env.set_ghost env old_ghost
    (* Just don't pollute the C file with these types. *)
    | Typedef(_,Declaration(t),_,_, _) when Cxx_utils.is_builtin_type t -> env
    | Typedef(loc,name,typ,is_extern_c_context, ghost) ->
      let old_ghost = Convert_env.is_ghost env in
      let env = Convert_env.set_ghost env ghost in
      let env = Convert_env.set_loc env loc in
      let cloc = Cil_datatype.Location.of_lexing_loc loc in
      let qual_name = make_qualified_name env name in
      let env = Convert_env.add_typedef env qual_name typ in
      let env =
        if is_extern_c_context then begin
          match name with
            | Declaration decl_name ->
                (* also add the unqualified version of the type
                   in the environment as it is also possible to use it
                   without qualification. This is in particular the case
                   for the typed imported from the C standard library
                   by the STL through the <c...> headers *)
                Convert_env.add_typedef
                  env { prequalification = []; decl_name} typ
            | _ ->
                Convert_env.fatal env
                  "extern C typedef with a fully qualified name"
        end else env
      in
      let name =
        if is_extern_c_context
        then qual_name.decl_name
        else
          let qual_name, t = Convert_env.typedef_normalize env
                qual_name TStandard in
          Mangling.mangle qual_name t None
      in
      let base,decl = convert_specifiers env typ false in
      let env = Convert_env.set_ghost env old_ghost in
      Convert_env.add_c_global
        env (TYPEDEF((SpecTypedef::base,[(name,decl JUSTBASE,[],cloc)]), cloc))
    | Namespace (_,name,body) ->
      let new_env = Convert_env.add_namespace env (QNamespace name) in
      let new_env = List.fold_left convert_global new_env body in
      Convert_env.reset_namespace new_env
    | StaticConst(loc,name,ikind,kind,value, is_extern_c, ghost) ->
        let old_ghost = Convert_env.is_ghost env in
        let env = Convert_env.set_ghost env ghost in
        let old_extern_c = Convert_env.is_extern_c env in
        let env = Convert_env.set_extern_c env is_extern_c in
        let decl, env =
          convert_static_const env loc name ikind kind value false
        in
        let env = Convert_env.add_c_global env decl in
        let env = Convert_env.set_ghost env old_ghost in
        Convert_env.set_extern_c env old_extern_c
     | EnumDecl(loc,name,ikind, body,is_extern_c_context,ghost) ->
      let old_ghost = Convert_env.is_ghost env in
      let env = Convert_env.set_loc env loc in
      let env = Convert_env.set_ghost env ghost in
      let cloc = Cil_datatype.Location.of_lexing_loc loc in
      let env = Convert_env.set_extern_c env is_extern_c_context in
      let qualified_name = make_qualified_name env name in
      let name =
        if is_extern_c_context
        then qualified_name.decl_name
        else
          let qualified_name, t = Convert_env.typedef_normalize env
                qualified_name TStandard in
          Mangling.mangle qualified_name t None
      in
      let tags = Option.map (convert_enum_constants env ikind) body in
      let glob = ONLYTYPEDEF([SpecType (Tenum(name,tags,[]))],cloc) in
      let env = Convert_env.add_c_global env glob in
      let env = Convert_env.set_ghost env old_ghost in
      env

let convert_ast file =
  let env = List.fold_left convert_global Convert_env.empty_env file.globals in
  let globs = Convert_env.get_c_globals env in
  let basic_pos =
    { Filepath.pos_path = Filepath.Normalized.of_string "<builtin>";
      pos_lnum = 0; pos_bol = 0; pos_cnum = 0; }
  in
  let basic_loc = basic_pos, basic_pos in
  let sizeof_t = spec_of_ikind Cil.theMachine.kindOfSizeOf in
  let res =
    (Datatype.Filepath.of_string file.filename,
     (false,
      DECDEF
        (None,
         ([SpecType Tvoid],
          [(("malloc",
             PTR (
               [],
               PROTO (
                 JUSTBASE ,
                 [(sizeof_t, ("size", JUSTBASE, [], basic_loc))], [], false)),
             [], basic_loc), NO_INIT)]), basic_loc))
     ::
     ((false,
       DECDEF
         (None,
          ([SpecType Tvoid],
           [(("free",
              PROTO (
                JUSTBASE ,
                [([SpecType Tvoid],
                  ("ptr", PTR ([], JUSTBASE), [], basic_loc))], [], false),
              [], basic_loc), NO_INIT)]), basic_loc))
      ::
      ((false,
        DECDEF
          (None,
           ([SpecType Tvoid],
            [(("Frama_C_memcpy",
               PTR (
                 [],
                 PROTO (
                   JUSTBASE ,
                   [([SpecType Tvoid],
                     ("dest", PTR ([], JUSTBASE), [], basic_loc));
                    ([SpecCV CV_CONST; SpecType Tvoid],
                     ("src", PTR ([], JUSTBASE), [], basic_loc));
                    (sizeof_t, ("size", JUSTBASE, [], basic_loc))], [], false)),
               [], basic_loc), NO_INIT)]), basic_loc))
       :: globs)))
  in
  let dkey = Frama_Clang_option.dkey_reorder in
  Frama_Clang_option.debug ~dkey "Before reordering:@\n%a" Cprint.printFile res;
  Reorder_defs.reorder res

let remove_unneeded file =
  let open Cil_types in
  let destructors = ref Datatype.String.Set.empty in
  let rec add_name = function
    | AAddrOf a -> add_name a
    | AStr f -> destructors:= Datatype.String.Set.add f !destructors
    | ACons(f,_) -> destructors:=Datatype.String.Set.add f !destructors
    | _ -> ()
  in
  let collect_destructors = object
    inherit Cil.nopCilVisitor
    method! vattr = function
      | Attr(s,[d]) when s = Cabs2cil.frama_c_destructor ->
        add_name d; Cil.SkipChildren
      | _ -> Cil.SkipChildren
  end
  in
  Cil.visitCilFileSameGlobals collect_destructors file;
  let isRoot = function
    | GFunDecl(_,v,_) | GFun ({svar = v},_) ->
      not (Cil.hasAttribute fc_pure_template_decl_attr v.vattr) &&
      (not (Cil.hasAttribute fc_implicit_attr v.vattr)
       || Datatype.String.Set.mem v.vname !destructors)
    | _ -> true
  in
  Rmtmps.removeUnused ~isRoot file
