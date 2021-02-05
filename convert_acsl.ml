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
open Logic_ptree

let convert_var env is_extern_c vi =
  match vi.logic_var_lv_kind with
    | LVGlobal | LVCGlobal ->
      if is_extern_c then vi.logic_var_lv_name.decl_name
      else
        let n, tk
          = Convert_env.typedef_normalize env vi.logic_var_lv_name TStandard
        in Mangling.mangle n tk None
    | LVFormal | LVQuant | LVLocal | LVCLocal | LVBuiltin ->
      vi.logic_var_lv_name.decl_name

let convert_logic_label = function
  | StmtLabel s -> s
  | LogicLabel s -> s

let convert_logic_label_opt = function
  | Some lab -> Some (convert_logic_label lab)
  | None -> None

let convert_ikind = function
  | IBool -> Cil_types.IBool
  | IChar_u -> Cil_types.IChar
  | IChar_s -> Cil_types.IChar
  | IUChar -> Cil_types.IUChar
  | ISChar -> Cil_types.ISChar
  | IChar16 -> Cil.intKindForSize 2 true
  | IChar32 -> Cil.intKindForSize 4 true
  | IWChar_u
  | IWChar_s
  | IWUChar
  | IWSChar -> Cil.theMachine.Cil.wcharKind
  | IChar -> Cil_types.IChar
  | IWChar -> Cil.theMachine.Cil.wcharKind
  | IShort -> Cil_types.IShort
  | IUShort -> Cil_types.IUShort
  | IInt -> Cil_types.IInt
  | IUInt -> Cil_types.IUInt
  | ILong -> Cil_types.ILong
  | IULong -> Cil_types.IULong
  | ILongLong -> Cil_types.ILongLong
  | IULongLong -> Cil_types.IULongLong

let convert_fkind = function
  | FFloat -> Cil_types.FFloat
  | FDouble -> Cil_types.FDouble
  | FLongDouble -> Cil_types.FLongDouble

let convert_logic_constant = function
  | LCInt v -> IntConstant v
  | LStr s -> StringConstant s
  | LWStr _s ->
    Frama_Clang_option.not_yet_implemented "Wide string support in logic"
  | LChr c -> IntConstant (string_of_int c)
  | LWChr c -> IntConstant (string_of_int c)
  | LCReal s -> FloatConstant s
  | LCEnum (v,_) -> IntConstant (Int64.to_string v)
    (* TODO: add support into ACSL for that? *)

let convert_cst_array_size env = function
  | LCInt v -> ASinteger v
  | LChr c | LWChr c -> ASinteger (string_of_int c)
  | LCEnum (_,s) ->
    let n, tk = Convert_env.typedef_normalize env s TStandard in
    let cname = Mangling.mangle n tk None in
    ASidentifier cname
  | LStr _ | LWStr _ | LCReal _ ->
    Frama_Clang_option.fatal "Unexpected value as array dimension"

let rec convert_logic_type env = function
  | Lvoid -> LTvoid
  | Lint ik -> LTint (convert_ikind ik)
  | Lfloat fk -> LTfloat (convert_fkind fk)
  | Larray (t,dim) ->
    let t = convert_logic_type env t in
    let dim =
      match dim with
      | Some dim -> convert_cst_array_size env dim
      | None -> ASnone
    in
    LTarray(t,dim)
  | Lpointer t | Lreference t ->
    let t = convert_logic_type env t in
    LTpointer t
  | Lenum e ->
    let e, tk = Convert_env.typedef_normalize env e TStandard
    in LTenum (Mangling.mangle e tk None)
  | Lstruct (s,t) ->
    let s,t = Convert_env.typedef_normalize env s t in
    let cname =
      if Convert_env.is_extern_c_aggregate env s t then s.decl_name
      else Mangling.mangle s t None
    in
    LTstruct cname
  | Lunion (u,t) ->
    let u, t = Convert_env.typedef_normalize env u t in
    let cname =
      if Convert_env.is_extern_c_aggregate env u t then u.decl_name
      else Mangling.mangle u t None
    in
    LTunion cname
  | LCnamed (n,extern_c) ->
      let name = if extern_c then n.decl_name
      else (* change only the template parameters in the qualification *)
        let n, tk = Convert_env.typedef_normalize env n TStandard
        in Mangling.mangle n tk None
      in
      LTnamed (name,[])
  | Lnamed({ prequalification = [QNamespace "Utf8_logic"];
             decl_name = "boolean"},_,[]) ->
      LTnamed (Utf8_logic.boolean,[])
  | Lnamed(t,extern_c,args) ->
    let name =
      if extern_c then t.decl_name
      else
        let t, tk = Convert_env.typedef_normalize env t TStandard
        in Mangling.mangle t tk None
    in
    let args = List.map (convert_logic_type env) args in
    LTnamed(name,args)
  | Lvariable s -> LTnamed(s.decl_name,[])
  | Linteger -> LTinteger
  | Lreal -> LTreal
  | Larrow(args,rt) ->
    let args = List.map (convert_logic_type env) args in
    let rt = convert_logic_type env rt in
    LTarrow(args, rt)

let convert_logic_param env p = (convert_logic_type env p.la_type, p.la_name)

type bkind = Relation | Logic | Arithmetic

let bo_kind = function
  | BOPlus | BOMinus | BOTimes | BODivide | BOModulo | BOBitOr | BOBitAnd
  | BOBitExclusiveOr | BOLeftShift | BORightShift
      -> Arithmetic
  | BOLess | BOLessOrEqual | BOEqual | BODifferent
  | BOGreaterOrEqual | BOGreater
      -> Relation
  | BOLogicalAnd | BOLogicalOr -> Logic
  | BOComma -> Frama_Clang_option.fatal "Comma operator in ACSL++ expression"

let convert_bop_arith = function
  | BOPlus -> Badd
  | BOMinus -> Bsub
  | BOTimes -> Bmul
  | BODivide -> Bdiv
  | BOModulo -> Bmod
  | BOBitOr -> Bbw_or
  | BOBitAnd -> Bbw_and
  | BOBitExclusiveOr -> Bbw_xor
  | BOLeftShift -> Blshift
  | BORightShift -> Brshift
  | _ -> Frama_Clang_option.fatal "not a binary arithmetic operation"

let convert_bop_relation = function
  | BOLess -> Lt
  | BOLessOrEqual -> Le
  | BOEqual -> Eq
  | BODifferent -> Neq
  | BOGreater -> Gt
  | BOGreaterOrEqual -> Ge
  | _ -> Frama_Clang_option.fatal "not a relation"

let convert_rel = function
  | Rlt -> Lt
  | Rgt -> Gt
  | Rle -> Le
  | Rge -> Ge
  | Req -> Eq
  | Rneq -> Neq

let convert_var_decl env v =
  let typ = convert_logic_type env v.lv_type in
  let name = v.logic_var_def_lv_name.decl_name in
  (typ, name)

let convert_reference env typ e =
  match typ with
    | LVReference _ | RVReference _ ->
      let full_e = { lexpr_loc = Convert_env.get_loc env; lexpr_node = e } in
      PLunop(Ustar,full_e)
    | _ -> e

let convert_logic_reference env typ e =
  match typ with
    | Lreference _ ->
      let full_e = { lexpr_loc = Convert_env.get_loc env; lexpr_node = e } in
      PLunop(Ustar, full_e)
    | _ -> e

let rec convert_logic_expr env e =
  let env = Convert_env.set_loc env e.loc in
  let lexpr_loc = Convert_env.get_loc env in
  let anonymous =
    { lexpr_loc; lexpr_node = convert_logic_expr_node env e.node }
  in
  List.fold_right
    (fun s res -> { lexpr_loc; lexpr_node = PLnamed(s,res) })
    e.names anonymous
and convert_logic_expr_node env = function
  | TConst c -> PLconstant(convert_logic_constant c)
  | TLval lv -> convert_logic_lval env lv
  | TSizeOf t -> PLsizeof(convert_logic_type env t)
  | TSizeOfStr s ->
    let cs =
      { lexpr_loc = Convert_env.get_loc env;
        lexpr_node = PLconstant(StringConstant s) }
    in
    PLsizeofE(cs)
  | TUnOp((UOPostInc|UOPostDec|UOPreInc|UOPreDec),_) ->
    Convert_env.fatal env "Side effect operation in ACSL++ expression"
  | TUnOp((UOCastNoEffect _ | UOCastDeref | UOCastToVoid | UOCastInteger _
          | UOCastDerefInit | UOCastEnum _ | UOCastFloat _ | UOCastC _),_) ->
    Convert_env.fatal env
      "Logic casts are not supposed to use TUnOp but TCastE"
  | TUnOp(UOOpposite,e) -> PLunop(Uminus,convert_logic_expr env e)
  | TUnOp(UOBitNegate,e) -> PLunop(Ubw_not,convert_logic_expr env e)
  | TUnOp(UOLogicalNegate,e) -> PLnot (convert_logic_expr env e)
  | TBinOp(bo,e1,e2) when bo_kind bo = Arithmetic ->
    let cbo = convert_bop_arith bo in
    let ce1 = convert_logic_expr env e1 in
    let ce2 = convert_logic_expr env e2 in
    PLbinop(ce1,cbo,ce2)
  | TBinOp(bo,e1,e2) when bo_kind bo = Relation ->
    let cbo = convert_bop_relation bo in
    let ce1 = convert_logic_expr env e1 in
    let ce2 = convert_logic_expr env e2 in
    PLrel(ce1,cbo,ce2)
  | TBinOp(BOLogicalAnd,e1,e2) ->
    let ce1 = convert_logic_expr env e1 in
    let ce2 = convert_logic_expr env e2 in
    PLand(ce1,ce2)
  | TBinOp(BOLogicalOr,e1,e2) ->
    let ce1 = convert_logic_expr env e1 in
    let ce2 = convert_logic_expr env e2 in
    PLor(ce1,ce2)
  | TBinOp _ -> Convert_env.fatal env "Unknown binary operator in logic"
  | TCastE(typ,e) ->
    let ctyp = convert_logic_type env typ in
    let ce = convert_logic_expr env e in
    PLcast(ctyp,ce)
  | TAddrOf lv | TStartOf lv ->
    let e = convert_logic_lval env lv in
    (* simplify memory accesses introduced by handling of references *)
    (match e with
      | PLunop(Ustar,t) -> t.lexpr_node
      | _ ->
        let e = { lexpr_node = e; lexpr_loc = Convert_env.get_loc env } in
        PLunop(Uamp,e))
  | TFieldAccess (e,(TField(f,TNoOffset)|TModel(f,TNoOffset))) ->
    let ce = convert_logic_expr env e in PLdot(ce,f)
  | TFieldAccess _ ->
    Convert_env.fatal env "Unexpected offset in field access"
  | TFalse -> PLfalse
  | TTrue -> PLtrue
  | TApp(f,l,args,extern_c) ->
    (* TODO: if f is an extern C (or built-in), do not mangle it *)
    let fname = if extern_c then f.decl_name
      else
        let f, t = Convert_env.typedef_normalize env f TStandard
        in Mangling.mangle f t None in
    let labels = List.map (fun l -> convert_logic_label l.snd) l in
    let args = List.map (convert_logic_expr env) args in
    PLapp(fname,labels,args)
  | TLambda (vars,t) ->
    let quants = List.map (convert_var_decl env) vars in
    let e = convert_logic_expr env t in
    PLlambda(quants,e)
  | TDataCons(name,args) ->
    let name, t = Convert_env.typedef_normalize env name TStandard in
    let name = Mangling.mangle name t None in
    let args = List.map (convert_logic_expr env) args in
    PLapp(name,[],args)
  | TIf(cond,etrue,efalse) ->
    let ccond = convert_logic_expr env cond in
    let cetrue = convert_logic_expr env etrue in
    let cefalse = convert_logic_expr env efalse in
    PLif(ccond,cetrue,cefalse)
  | TAt(t,l) ->
    let t = convert_logic_expr env t in
    let l = convert_logic_label l in
    PLat(t,l)
  | TBase_addr(l,t) ->
    let l = convert_logic_label_opt l in
    let t = convert_logic_expr env t in
    PLbase_addr(l,t)
  | TOffset(l,t) ->
    let l = convert_logic_label_opt l in
    let t = convert_logic_expr env t in
    PLoffset(l,t)
  | TBlock_length(l,t) ->
    let l = convert_logic_label_opt l in
    let t = convert_logic_expr env t in
    PLblock_length(l,t)
  | TNull -> PLnull
  | TLogic_coerce(_,t) ->
    (* should be transparent at the parsed logic tree level. *)
    (convert_logic_expr env t).lexpr_node
  | TUpdate(obj,off,t) ->
    let obj = convert_logic_expr env obj in
    let path = path_of_offset env off in
    let value = convert_logic_expr env t in
    PLupdate(obj,path,PLupdateTerm value)
  | TEmpty_set -> PLempty
  | TUnion l ->
    let l = List.map (convert_logic_expr env) l in
    PLunion l
  | TInter l ->
    let l = List.map (convert_logic_expr env) l in
    PLinter l
  | TComprehension (t,quants,pred) ->
    let quants = List.map (convert_var_decl env) quants in
    let t = convert_logic_expr env t in
    let pred = Option.map (convert_pred_named env) pred in
    PLcomprehension (t,quants,pred)
  | TRange(l,h) ->
    let l = Option.map (convert_logic_expr env) l in
    let h = Option.map (convert_logic_expr env) h in
    PLrange(l,h)
  | TLet(info,t) ->
    let body = convert_inner_body env info in
    let name = info.li_name.decl_name in
    let rest = convert_logic_expr env t in
    PLlet(name,body,rest)
  | TCoerce _ | TCoerceE _ ->
    Frama_Clang_option.not_yet_implemented "coercions"

and convert_logic_lval env lv =
  let base = convert_logic_lhost env lv.base_support in
  convert_logic_offset env base lv.offset

and convert_logic_lhost env = function
  | TVar v ->
    (match v.logic_var_lv_kind with
      | LVCGlobal ->
        let is_extern_c, typ =
          Convert_env.get_global_var env v.logic_var_lv_name
        in
        let var = PLvar (convert_var env is_extern_c v) in
        convert_reference env typ var
      | LVCLocal ->
        let var = PLvar v.logic_var_lv_name.decl_name in
        let typ = Convert_env.get_local_var env v.logic_var_lv_name.decl_name in
        convert_reference env typ var
      | _ ->
        PLvar v.logic_var_lv_name.decl_name
    )
  | TCFun(n,s) ->
    let n, t = Convert_env.typedef_normalize env n TStandard
    in PLvar (Mangling.mangle n t (Some (FKFunction,s)))
  | TResult typ -> convert_logic_reference env typ PLresult
  | TMem t -> let t = convert_logic_expr env t in PLunop(Ustar,t)

and convert_logic_offset env base = function
  | TNoOffset -> base
  | TField(s,o) | TModel(s,o) ->
    let e = { lexpr_loc = Convert_env.get_loc env; lexpr_node = base } in
    let base = PLdot(e,s) in
    convert_logic_offset env base o
  | TBase(b,t,o) ->
    let e = { lexpr_loc = Convert_env.get_loc env; lexpr_node = base } in
    let b, t = Convert_env.typedef_normalize env b t in
    let base = PLdot(e,("_frama_c_" ^ Mangling.mangle b t None)) in
    convert_logic_offset env base o
  | TVirtualBase(b,t,o) ->
    let e = { lexpr_loc = Convert_env.get_loc env; lexpr_node = base } in
    let b, t = Convert_env.typedef_normalize env b t in
    let base = PLdot(e,("_frama_c_" ^ Mangling.mangle b t None)) in
    convert_logic_offset env base o
  | TDerived(_ (* d *),_ (* td *),_ (* b *),_ (* tb *),_ (* o *)) ->
    Convert_env.fatal env
      "casts to derived classes are not supported for the moment"
  | TIndex(t,o) ->
    let e = { lexpr_loc = Convert_env.get_loc env; lexpr_node = base } in
    let i = convert_logic_expr env t in
    let base = PLarrget(e,i) in
    convert_logic_offset env base o

and path_of_offset env = function
  | TNoOffset -> []
  | TField(s,o) | TModel(s,o) ->
    let path = path_of_offset env o in
    PLpathField s :: path
  | TBase(b,t,o) ->
    let path = path_of_offset env o in
    let b, t = Convert_env.typedef_normalize env b t in
    PLpathField ("_frama_c_" ^ Mangling.mangle b t None) :: path
  | TVirtualBase(b,t,o) ->
    let path = path_of_offset env o in
    let b, t = Convert_env.typedef_normalize env b t in
    PLpathField ("_frama_c_" ^ Mangling.mangle b t None) :: path
  | TDerived(_ (* d *),_ (* td *),_ (* b *),_ (* tb *),_ (* o *)) ->
    Convert_env.fatal env
      "casts to derived classes are not supported for the moment"
  | TIndex(t,o) ->
    let i = convert_logic_expr env t in
    let path = path_of_offset env o in
    PLpathIndex(i) :: path

and convert_pred_named env p =
  let env = Convert_env.set_loc env p.pred_loc in
  let pred_loc = Convert_env.get_loc env in
  let cp = convert_pred env p.pred_content in
  let cp =
    List.fold_right
      (fun s acc -> PLnamed(s,{ lexpr_node = acc; lexpr_loc = pred_loc }))
      p.pred_name cp
  in
  { lexpr_node = cp; lexpr_loc = pred_loc }

and convert_pred env = function
  | Pfalse -> PLfalse
  | Ptrue -> PLtrue
  | PApp(p,labs,args,is_extern_c) ->
    let pname = if is_extern_c then p.decl_name
    else
      let p, t = Convert_env.typedef_normalize env p TStandard in
      Mangling.mangle p t None
    in let clabs = List.map (fun l -> convert_logic_label l.snd) labs in
    let cargs = List.map (convert_logic_expr env) args in
    PLapp(pname,clabs,cargs)
  | Pseparated l ->
    let l = List.map (convert_logic_expr env) l in
    PLseparated l
  | Prel(rel,t1,t2) ->
    let rel = convert_rel rel in
    let t1 = convert_logic_expr env t1 in
    let t2 = convert_logic_expr env t2 in
    PLrel(t1,rel,t2)
  | Pand(p1,p2) ->
    let p1 = convert_pred_named env p1 in
    let p2 = convert_pred_named env p2 in
    PLand(p1,p2)
  | Por(p1,p2) ->
    let p1 = convert_pred_named env p1 in
    let p2 = convert_pred_named env p2 in
    PLor(p1,p2)
  | Pxor(p1,p2) ->
    let p1 = convert_pred_named env p1 in
    let p2 = convert_pred_named env p2 in
    PLxor(p1,p2)
  | Pimplies(p1,p2) ->
    let p1 = convert_pred_named env p1 in
    let p2 = convert_pred_named env p2 in
    PLimplies(p1,p2)
  | Piff(p1,p2) ->
    let p1 = convert_pred_named env p1 in
    let p2 = convert_pred_named env p2 in
    PLiff(p1,p2)
  | Pnot p ->
    let p = convert_pred_named env p in
    PLnot p
  | Pif(cond,ptrue,pfalse) ->
    let cond = convert_logic_expr env cond in
    let ptrue = convert_pred_named env ptrue in
    let pfalse = convert_pred_named env pfalse in
    PLif(cond,ptrue,pfalse)
  | Plet(li,p) ->
    let body = convert_inner_body env li in
    let p = convert_pred_named env p in
    PLlet(li.li_name.decl_name,body,p)
  | Pforall (x,p) ->
    let quants = List.map (convert_var_decl env) x in
    let p = convert_pred_named env p in
    PLforall(quants,p)
  | Pexists(x,p) ->
    let quants = List.map (convert_var_decl env) x in
    let p = convert_pred_named env p in
    PLexists(quants,p)
  | Pat(l,p) ->
    let l = convert_logic_label l in
    let p = convert_pred_named env p in
    PLat(p,l)
  | Pvalid_function(t) ->
    let t = convert_logic_expr env t in
    PLvalid_function(t)
  | Pvalid_read(l,t) ->
    let l = convert_logic_label_opt l in
    let t = convert_logic_expr env t in
    PLvalid_read(l,t)
  | Pvalid(l,t) ->
    let l = convert_logic_label_opt l in
    let t = convert_logic_expr env t in
    PLvalid(l,t)
  | Pinitialized(l,t) ->
    let l = convert_logic_label_opt l in
    let t = convert_logic_expr env t in
    PLinitialized(l,t)
  | Pallocable(l,t) ->
    let l = convert_logic_label_opt l in
    let t = convert_logic_expr env t in
    PLallocable(l,t)
  | Pfreeable(l,t) ->
    let l = convert_logic_label_opt l in
    let t = convert_logic_expr env t in
    PLfreeable(l,t)
  | Pfresh(Some l1, Some l2,t1,t2) ->
    let l1 = convert_logic_label l1 in
    let l2 = convert_logic_label l2 in
    let t1 = convert_logic_expr env t1 in
    let t2 = convert_logic_expr env t2 in
    PLfresh (Some(l1,l2),t1,t2)
  | Pfresh(None,None,t1,t2) ->
    let t1 = convert_logic_expr env t1 in
    let t2 = convert_logic_expr env t2 in
    PLfresh (None,t1,t2)
  | Pfresh(_,_,_,_) -> Frama_Clang_option.fatal
      "zero or two labels needed in fresh construct"
  | Psubtype _ -> Frama_Clang_option.not_yet_implemented "subtyping relation"

and convert_inner_body env li =
  let body =
    match li.fun_body with
      | LBnone -> Convert_env.fatal env "local binding without body"
      | LBreads _ -> Convert_env.fatal env "local binding with read clause"
      | LBinductive _ -> Convert_env.fatal env "local inductive definition"
      | LBterm t -> convert_logic_expr env t
      | LBpred p -> convert_pred_named env p
  in
  match li.profile with
    | [] -> body
    | prms ->
      let convert_arg_decl a =
        let typ = convert_logic_type env a.la_type in
        let v = a.la_name in
        typ, v
      in
      let prms = List.map convert_arg_decl prms in
      { lexpr_node = PLlambda(prms,body); lexpr_loc = Convert_env.get_loc env }

let convert_logic_ctor env ctor =
  (* NB: we can't rely on ACSL overloading for constructor. Maybe we
     should get the whole signature? *)
  let name =
    if ctor.logic_ctor_info_is_extern_c then
      ctor.ctor_name.decl_name
    else
      let ctor_name, t
        = Convert_env.typedef_normalize env ctor.ctor_name TStandard in
      Mangling.mangle ctor_name t None
  in
  let prms = List.map (convert_logic_type env) ctor.ctor_params in
  (name,prms)

let convert_logic_type_def env = function
  | LTsum ctors -> TDsum (List.map (convert_logic_ctor env) ctors)
  | LTsyn t -> TDsyn (convert_logic_type env t)

let convert_extended env e =
  (e.ext_name, List.map (convert_pred_named env) e.predicates)

let convert_allocation env = function
  | Intermediate_format.FreeAlloc(f,a) ->
    Logic_ptree.FreeAlloc
      (List.map (convert_logic_expr env) f, List.map (convert_logic_expr env) a)
  | Intermediate_format.FreeAllocAny -> Logic_ptree.FreeAllocAny

let convert_deps env = function
  | Intermediate_format.From l ->
      Logic_ptree.From (List.map (convert_logic_expr env) l)
  | Intermediate_format.FromAny -> Logic_ptree.FromAny

let convert_from env f =
  convert_logic_expr env f.floc, convert_deps env f.vars

let convert_assigns env = function
  | Intermediate_format.WritesAny -> Logic_ptree.WritesAny
  | Intermediate_format.Writes l ->
      Logic_ptree.Writes (List.map (convert_from env) l)

let convert_pred_tp env ?(kind=Cil_types.Assert) p =
  (* TODO: support check and admit in ACSL++. *)
  let tp_statement = convert_pred_named env p in
  { tp_kind = kind; tp_statement }

let convert_termination_kind = function
  | Intermediate_format.Normal -> Cil_types.Normal
  | Intermediate_format.Exits -> Cil_types.Exits
  | Intermediate_format.Breaks -> Cil_types.Breaks
  | Intermediate_format.Continues -> Cil_types.Continues
  | Intermediate_format.Returns -> Cil_types.Returns

let convert_post_cond env p =
  convert_termination_kind p.tkind, convert_pred_tp env p.pred

let convert_behavior env bhv =
  let b_name = bhv.beh_name in
  let b_requires = List.map (convert_pred_tp env) bhv.requires in
  let b_assumes = List.map (convert_pred_named env) bhv.assumes in
  let b_post_cond = List.map (convert_post_cond env) bhv.post_cond in
  let b_assigns = convert_assigns env bhv.assignements in
  let b_allocation = convert_allocation env bhv.alloc in
  let b_extended = List.map (convert_extended env) bhv.extended in
  { b_name; b_requires; b_assumes; b_post_cond;
    b_assigns; b_allocation; b_extended }

let convert_variant env v = convert_logic_expr env v.vbody, v.vname

let convert_function_contract env contract =
  let spec_behavior = List.map (convert_behavior env) contract.behavior in
  let spec_variant = Option.map (convert_variant env) contract.variant in
  let spec_terminates =
    Option.map (convert_pred_named env) contract.terminates
  in
  let spec_complete_behaviors =
    List.map (fun c -> c.behaviors) contract.complete_behaviors
  in
  let spec_disjoint_behaviors =
    List.map (fun c -> c.behaviors) contract.disjoint_behaviors
  in
  { spec_behavior; spec_variant; spec_terminates; spec_complete_behaviors;
    spec_disjoint_behaviors }

let convert_inv_kind = function
  | InvariantAsAssertion -> false
  | NormalLoop -> true

let convert_loop_pragma env = function
  | Intermediate_format.Unroll_specs l ->
    Logic_ptree.Unroll_specs (List.map (convert_logic_expr env) l)
  | Intermediate_format.Widen_hints l ->
    Logic_ptree.Unroll_specs (List.map(convert_logic_expr env) l)
  | Intermediate_format.Widen_variables l ->
    Logic_ptree.Widen_variables (List.map (convert_logic_expr env) l)

let convert_slice_pragma env = function
  | Intermediate_format.SPexpr e ->
      Logic_ptree.SPexpr (convert_logic_expr env e)
  | Intermediate_format.SPctrl -> Logic_ptree.SPctrl
  | Intermediate_format.SPstmt -> Logic_ptree.SPstmt

let convert_impact_pragma env = function
  | Intermediate_format.IPexpr e ->
      Logic_ptree.IPexpr (convert_logic_expr env e)
  | Intermediate_format.IPstmt -> Logic_ptree.IPstmt

let convert_pragma env = function
  | Intermediate_format.Loop_pragma p ->
      Logic_ptree.Loop_pragma (convert_loop_pragma env p)
  | Intermediate_format.Slice_pragma p ->
      Logic_ptree.Slice_pragma (convert_slice_pragma env p)
  | Intermediate_format.Impact_pragma p ->
      Logic_ptree.Impact_pragma (convert_impact_pragma env p)

let convert_code_annot env = function
  | Intermediate_format.Assert(bhvs,pred) ->
    AAssert(bhvs, convert_pred_tp env pred)
  | StmtSpec(bhvs,spec) -> AStmtSpec(bhvs,convert_function_contract env spec)
  | Invariant(bhvs,kind,inv) ->
    let kind = convert_inv_kind kind in
    let inv = convert_pred_tp env inv in
    AInvariant(bhvs,kind,inv)
  | Variant v -> AVariant (convert_variant env v)
  | Assigns (bhvs,a) -> AAssigns(bhvs,convert_assigns env a)
  | Allocation(bhvs,a) -> AAllocation(bhvs,convert_allocation env a)
  | Pragma p -> APragma (convert_pragma env p)

let rec convert_annot env annot =
  let annot, env =
    match annot with
      | Dfun_or_pred (loc,info) ->
        let env = Convert_env.set_loc env loc in
        (* we don't necessarily need to mangle according to the signature,
           as ACSL itself feature overloading. If we decide to have unique
           names, we'll need to adapt mangling to accomodate for logic types.
         *)
        let name =
          if info.li_extern_c then
            info.li_name.decl_name
          else
            let info_name, t
              = Convert_env.typedef_normalize env info.li_name TStandard in
            Mangling.mangle info_name t None
        in
        let labels = List.map convert_logic_label info.arg_labels in
        let rt = Option.map (convert_logic_type env) info.returned_type in
        let params = List.map (convert_logic_param env) info.profile in
        (match info.fun_body,rt with
          | LBnone, None ->
            LDpredicate_reads(name,labels,info.tparams,params,None)
          | LBnone, Some rt ->
            LDlogic_reads(name,labels,info.tparams,rt,params,None)
          | LBreads l, None ->
            let reads = List.map (convert_logic_expr env) l in
            LDpredicate_reads(name,labels,info.tparams,params,Some reads)
          | LBreads l, Some rt ->
            let reads = List.map (convert_logic_expr env) l in
            LDlogic_reads(name,labels,info.tparams,rt,params,Some reads)
          | LBterm _, None ->
            Convert_env.fatal env "predicate definition with a term as body"
          | LBterm body, Some rt ->
            let body = convert_logic_expr env body in
            LDlogic_def(name,labels,info.tparams,rt,params,body)
          | LBpred _, Some _ ->
            Convert_env.fatal env
              "logic function definition with a predicate as body"
          | LBpred body, None ->
            let body = convert_pred_named env body in
            LDpredicate_def(name,labels,info.tparams,params,body)
          | LBinductive _, Some _ ->
            Convert_env.fatal env
              "logic function definition with inductive body"
          | LBinductive body, None ->
            let inductive_case ind =
              let labs = List.map convert_logic_label ind.labels in
              let def = convert_pred_named env ind.def in
              (ind.def_name,labs,ind.arguments,def)
            in
            let body = List.map inductive_case body in
            LDinductive_def(name,labels,info.tparams,params,body)
        ), env
      | Dvolatile(loc,mem,read,write) ->
        let env = Convert_env.set_loc env loc in
        let mem = List.map (convert_logic_expr env) mem in
        (* NB: should we have the real type of the arguments of the functions?*)
        let mangle name signature =
          let name, t = Convert_env.typedef_normalize env name TStandard in
          Mangling.mangle name t signature in
        let read = Option.map (Extlib.swap mangle None)
                   read in
        let write = Option.map (Extlib.swap mangle None)
                    write in
        LDvolatile(mem,(read,write)), env
      | Daxiomatic(loc,s,annots) ->
        let env = Convert_env.set_loc env loc in
        let annots = List.map (convert_annot env) annots in
        LDaxiomatic(s,annots), env
      | Dtype(loc,lt_info) ->
        let env = Convert_env.set_loc env loc in
        let name =
          if lt_info.logic_type_info_is_extern_c then
            lt_info.type_name.decl_name
          else
            let info_name, t = Convert_env.typedef_normalize
                  env lt_info.type_name TStandard in
            Mangling.mangle info_name t None
        in
        let def = Option.map (convert_logic_type_def env)
                    lt_info.definition in
        LDtype(name, lt_info.params, def), env
      | Dlemma(loc,name,is_axiom,labs,params,body) ->
        let env = Convert_env.set_loc env loc in
        let labs = List.map convert_logic_label labs in
        let kind = if is_axiom then Cil_types.Admit else Assert in
        let body = convert_pred_tp env ~kind body in
        LDlemma(name,labs,params,body), env
      | Dinvariant(loc,body) ->
        let env = Convert_env.set_loc env loc in
        let name =
          if body.li_extern_c then
            body.li_name.decl_name
          else
            let body_name, t = Convert_env.typedef_normalize
                  env body.li_name TStandard in
            Mangling.mangle body_name t None
        in
        let body =
          match body.fun_body with
            | LBpred p ->
              convert_pred_named env p
            | _ ->
              Convert_env.fatal env "unexpected body for a global invariant"
        in
        LDinvariant(name, body), env
      | Dtype_annot (loc, body) ->
        let env = Convert_env.set_loc env loc in
        let inv_name =
          if body.li_extern_c then
            body.li_name.decl_name
          else
            let body_name, t = Convert_env.typedef_normalize
                  env body.li_name TStandard in
            Mangling.mangle body_name t None
        in
        let this_type, this_name =
          match body.profile with
            | [ { la_type = t; la_name = s } ] -> convert_logic_type env t, s
            | _ ->
              Convert_env.fatal env
                "unexpected number of parameters \
                 in definition of type invariant"
        in
        let inv =
          match body.fun_body with
            | LBpred p -> convert_pred_named env p
            | _ -> Convert_env.fatal env "unexpected body for a type invariant"
        in
        LDtype_annot { inv_name; this_type; this_name; inv }, env
      | Dmodel_annot(loc,model) ->
        let env = Convert_env.set_loc env loc in
        let model_name = model.Intermediate_format.model_name in
        let model_type = convert_logic_type env model.field_type in
        let model_for_type = convert_logic_type env model.base_type in
        LDmodel_annot { model_for_type; model_type; model_name }, env
  in
  { decl_node = annot; decl_loc = Convert_env.get_loc env; }
