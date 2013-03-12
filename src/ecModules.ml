(* -------------------------------------------------------------------- *)
open EcUtils
open EcSymbols

(* -------------------------------------------------------------------- *)
module Sp = EcPath.Sp

(* -------------------------------------------------------------------- *)
type lvalue =
  | LvVar   of (EcTypes.prog_var * EcTypes.ty)
  | LvTuple of (EcTypes.prog_var * EcTypes.ty) list
  | LvMap   of (EcPath.path * EcTypes.ty list) * 
                  EcTypes.prog_var * EcTypes.tyexpr * EcTypes.ty

let lv_equal lv1 lv2 =
  match lv1, lv2 with
  | LvVar (pv1, ty1), LvVar (pv2, ty2) ->
         (EcTypes.pv_equal pv1 pv2)
      && (EcTypes.ty_equal ty1 ty2)

  | LvTuple tu1, LvTuple tu2 ->
      List.all2
        (fun (pv1, ty1) (pv2, ty2) ->
             (EcTypes.pv_equal pv1 pv2)
          && (EcTypes.ty_equal ty1 ty2))
        tu1 tu2

  | LvMap ((p1, tys1), pv1, e1, ty1),
    LvMap ((p2, tys2), pv2, e2, ty2) ->

         (EcPath.p_equal   p1  p2 )
      && (EcTypes.pv_equal pv1 pv2)
      && (EcTypes.e_equal  e1  e2 )
      && (EcTypes.ty_equal ty1 ty2)
      && (List.all2 EcTypes.ty_equal tys1 tys2)

  | _, _ -> false

let lv_fv = function
  | LvVar (pv,_) -> EcTypes.pv_fv pv 
  | LvTuple pvs -> 
      let add s (pv,_) = EcIdent.fv_union s (EcTypes.pv_fv pv) in
      List.fold_left add EcIdent.Mid.empty pvs 
  | LvMap(_,pv,e,_) -> EcIdent.fv_union (EcTypes.pv_fv pv) (EcTypes.e_fv e)

(* -------------------------------------------------------------------- *)
type instr = {
  i_node : instr_node;
  i_fv : int EcIdent.Mid.t;
  i_tag  : int;
}

and instr_node =
  | Sasgn   of lvalue * EcTypes.tyexpr
  | Srnd    of lvalue * EcTypes.tyexpr
  | Scall   of lvalue option * EcPath.mpath * EcTypes.tyexpr list
  | Sif     of EcTypes.tyexpr * stmt * stmt
  | Swhile  of EcTypes.tyexpr * stmt
  | Sassert of EcTypes.tyexpr

and stmt = {
  s_node : instr list;
  s_fv   : int EcIdent.Mid.t;
  s_tag  : int;
}

(* -------------------------------------------------------------------- *)
let i_equal   = ((==) : instr -> instr -> bool)
let i_hash    = fun i -> i.i_tag
let i_compare = fun i1 i2 -> i_hash i1 - i_hash i2
let i_fv i    = i.i_fv

let s_equal   = ((==) : stmt -> stmt -> bool)
let s_hash    = fun s -> s.s_tag
let s_compare = fun s1 s2 -> s_hash s1 - s_hash s2
let s_fv s = s.s_fv 

(* -------------------------------------------------------------------- *)
module Hinstr = Why3.Hashcons.Make (struct 
  type t = instr

  let equal_node i1 i2 = 
    match i1, i2 with
    | Sasgn (lv1, e1), Sasgn (lv2, e2) ->
        (lv_equal lv1 lv2) && (EcTypes.e_equal e1 e2)

    | Srnd (lv1, e1), Srnd (lv2, e2) ->
        (lv_equal lv1 lv2) && (EcTypes.e_equal e1 e2)

    | Scall (lv1, m1, es1), Scall (lv2, m2, es2) ->
           (EcUtils.opt_equal lv_equal lv1 lv2)
        && (EcPath.m_equal m1 m2)
        && (List.all2 EcTypes.e_equal es1 es2)

    | Sif (c1, s1, r1), Sif (c2, s2, r2) ->
           (EcTypes.e_equal c1 c2)
        && (s_equal s1 s2)
        && (s_equal r1 r2)

    | Swhile (c1, s1), Swhile (c2, s2) ->
           (EcTypes.e_equal c1 c2)
        && (s_equal s1 s2)

    | Sassert e1, Sassert e2 ->
        (EcTypes.e_equal e1 e2)

    | _, _ -> false

  let equal i1 i2 = equal_node i1.i_node i2.i_node

  let hash p = 
    match p.i_node with
    | Sasgn (lv, e) ->
        Why3.Hashcons.combine
          (Hashtbl.hash lv) (EcTypes.e_hash e)

    | Srnd (lv, e) ->
        Why3.Hashcons.combine
          (Hashtbl.hash lv) (EcTypes.e_hash e)

    | Scall (lv, m, tys) ->
        Why3.Hashcons.combine_list EcTypes.e_hash
          (Why3.Hashcons.combine
             (Hashtbl.hash lv) (EcPath.m_hash m))
          tys

    | Sif (c, s1, s2) ->
        Why3.Hashcons.combine2
          (EcTypes.e_hash c) (s_hash s1) (s_hash s2)

    | Swhile (c, s) ->
        Why3.Hashcons.combine (EcTypes.e_hash c) (s_hash s)

    | Sassert e -> EcTypes.e_hash e

  let i_fv   = function
    | Sasgn(lv,e) -> 
        EcIdent.fv_union (lv_fv lv) (EcTypes.e_fv e)
    | Srnd (lv,e) -> 
        EcIdent.fv_union (lv_fv lv) (EcTypes.e_fv e)
    | Scall(olv,f,args) ->
        let ffv = EcPath.m_fv EcIdent.Mid.empty f in
        let ofv = ofold olv (fun lv s -> EcIdent.fv_union s (lv_fv lv)) ffv in
        List.fold_left
          (fun s a -> EcIdent.fv_union s (EcTypes.e_fv a)) ofv args
    | Sif(e,s1,s2) -> 
        EcIdent.fv_union (EcTypes.e_fv e) 
          (EcIdent.fv_union (s_fv s1) (s_fv s2))
    | Swhile(e,s)  -> 
        EcIdent.fv_union (EcTypes.e_fv e) (s_fv s)
    | Sassert e    -> 
        EcTypes.e_fv e 
          
  let tag n p = { p with i_tag = n; i_fv = i_fv p.i_node }
end)

(* -------------------------------------------------------------------- *)
module Hstmt = Why3.Hashcons.Make (struct 
  type t = stmt

  let equal_node s1 s2 =
    List.all2 i_equal s1 s2

  let equal s1 s2 = equal_node s1.s_node s2.s_node

  let hash p =
    Why3.Hashcons.combine_list i_hash 0 p.s_node
          
  let tag n p = { p with s_tag = n;
                  s_fv = 
                  List.fold_left (fun s i -> EcIdent.fv_union s (i_fv i))
                    EcIdent.Mid.empty p.s_node
                }
end)

(* -------------------------------------------------------------------- *)
let mk_instr i = 
  Hinstr.hashcons { i_node = i; i_tag = -1; i_fv = EcIdent.Mid.empty }

let asgn   (lv, e)      = mk_instr (Sasgn (lv, e))
let rnd    (lv, e)      = mk_instr (Srnd (lv, e))
let call   (lv, m, tys) = mk_instr (Scall (lv, m, tys))
let if_    (c, s1, s2)  = mk_instr (Sif (c, s1, s2))
let while_ (c, s)       = mk_instr (Swhile (c, s))
let assert_ e           = mk_instr (Sassert e)

let stmt s = 
  Hstmt.hashcons { s_node = s; s_tag = -1; s_fv = EcIdent.Mid.empty}

module MSHi = EcMaps.MakeMSH(struct type t = instr let tag i = i.i_tag end)
module Hi = MSHi.H

let i_subst_ids s = 
  let e_subst = EcTypes.Esubst.subst_ids s in
  let lv_subst lv = 
    match lv with 
    | LvVar(pv,ty) ->
        let pv' = EcTypes.PVsubst.subst_ids s pv in
        if pv == pv' then lv else LvVar(pv',ty)
    | LvTuple pvs ->
        let pvs' = List.smart_map (fun (pv,ty as lv) ->
          let pv' = EcTypes.PVsubst.subst_ids s pv in
          if pv == pv' then lv else (pv',ty)) pvs in
        if pvs == pvs' then lv else LvTuple pvs'
    | LvMap(p, pv, e, ty) ->
        let pv' = EcTypes.PVsubst.subst_ids s pv in
        let e'  = e_subst e in
        if pv == pv' && e == e' then lv else LvMap(p,pv',e',ty) in
  Hi.memo_rec 107 (fun aux i ->
    match i.i_node with
    | Sasgn(lv,e) ->
        let lv' = lv_subst lv in
        let e'  = e_subst e in
        if lv == lv' && e == e' then i else 
        asgn(lv',e')
    | Srnd(lv,e) ->
        let lv' = lv_subst lv in
        let e'  = e_subst e in
        if lv == lv' && e == e' then i else 
        rnd(lv',e')
    | Scall(olv,mp,args) ->
        let olv' = osmart_map olv lv_subst in
        let mp'  = EcPath.m_subst_ids s mp in
        let args' = List.smart_map e_subst args in
        if olv == olv' && mp == mp' && args == args' then i else 
        call(olv',mp',args')
    | Sif(e,s1,s2) ->
        let e' = e_subst e in
        let s1' = List.smart_map aux s1.s_node in
        let s2' = List.smart_map aux s2.s_node in
        if e == e' && s1.s_node == s1' && s2.s_node == s2' then i else
        if_(e',stmt s1', stmt s2')
    | Swhile(e,s1) ->
        let e' = e_subst e in
        let s1' = List.smart_map aux s1.s_node in
        if e == e' && s1.s_node == s1' then i else
        while_(e',stmt s1')
    | Sassert e -> 
        let e' = e_subst e in
        if e == e' then i else
        assert_ e') 

let s_subst_ids s = 
  let i_subst = i_subst_ids s in
  fun st -> 
  let st' = List.smart_map i_subst st.s_node in
  if st.s_node == st' then st else stmt st'

(* -------------------------------------------------------------------- *)
module UM = struct
  (* TODO: to be rewritten using -pxp OCaml 4.0 feature *)

  type flag  = [`Call | `Read | `Write]
  type flags = UseFlags of int

  let iflag = function 
    | `Call  -> 0
    | `Read  -> 1
    | `Write -> 2

  let empty = UseFlags 0

  let add (UseFlags f : flags) (e : flag) =
    UseFlags (f lor (1 lsl (iflag e)))

  let have (UseFlags f : flags) (e : flag) =
    (f land (1 lsl (iflag e))) != 0

  let singleton (e : flag) =
    add empty e

  let equal (UseFlags fin) (UseFlags fout) =
    fin == fout

  let included (UseFlags fin) (UseFlags fout) =
    (lnot fin) land fout == 0
end

type use_flags = UM.flags

(* -------------------------------------------------------------------- *)
type module_type = EcPath.path

type module_sig = {
  mt_params : (EcIdent.t * module_type) list;
  mt_body   : module_sig_body;
  mt_mforb  : EcPath.Sp.t;
}

and module_sig_body = module_sig_body_item list

and module_sig_body_item =
  | Tys_variable of (symbol * EcTypes.ty)
  | Tys_function of funsig

and funsig = {
  fs_name : symbol;
  fs_sig  : (symbol * EcTypes.ty) list * EcTypes.ty;
  fs_uses : use_flags EcPath.Mp.t;
}

(* -------------------------------------------------------------------- *)
type module_expr = {
  me_name  : symbol;
  me_body  : module_body;
  me_comps : module_comps;
  me_sig   : module_sig;
  me_uses  : EcPath.Sp.t;
  me_types : module_type list;
}

and module_body =
  | ME_Alias       of EcPath.mpath
  | ME_Structure   of module_structure
  | ME_Decl        of module_type

and module_structure = {
  ms_params : (EcIdent.t * module_type) list;
  ms_body   : module_item list;
}

and module_item =
  | MI_Module   of module_expr
  | MI_Variable of variable
  | MI_Function of function_

and module_comps = module_comps_item list

and module_comps_item = module_item

and function_ = {
  f_name   : symbol;
  f_sig    : funsig;
  f_def    : function_def option;
}

and function_def = {
  f_locals : (symbol * EcTypes.ty) list;
  f_body   : stmt;
  f_ret    : EcTypes.tyexpr option;
}

and variable = {
  v_name : symbol;
  v_type : EcTypes.ty;
}

(* -------------------------------------------------------------------- *)
let fd_equal f1 f2 =
  let lc_equal (x1, ty1) (x2, ty2) =
    (x1 = x2) && (EcTypes.ty_equal ty1 ty2)
  in
     (s_equal f1.f_body f2.f_body)
  && (EcUtils.opt_equal EcTypes.e_equal f1.f_ret f2.f_ret)
  && (List.all2 lc_equal f1.f_locals f2.f_locals)

let fd_hash f =
  let lc_hash (x, ty) =
    Why3.Hashcons.combine (Hashtbl.hash x) (EcTypes.ty_hash ty)
  in
    Why3.Hashcons.combine2
      (s_hash f.f_body)
      (Why3.Hashcons.combine_option EcTypes.e_hash f.f_ret)
      (Why3.Hashcons.combine_list lc_hash 0 f.f_locals)
