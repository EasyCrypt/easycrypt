(* -------------------------------------------------------------------- *)
open EcUtils
open EcSymbols
open EcPath

(* -------------------------------------------------------------------- *)
type lvalue =
  | LvVar   of (EcTypes.prog_var * EcTypes.ty)
  | LvTuple of (EcTypes.prog_var * EcTypes.ty) list
  | LvMap   of (EcPath.path * EcTypes.ty list) * 
                  EcTypes.prog_var * EcTypes.expr * EcTypes.ty

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
  | Sasgn   of lvalue * EcTypes.expr
  | Srnd    of lvalue * EcTypes.expr
  | Scall   of lvalue option * EcPath.xpath * EcTypes.expr list
  | Sif     of EcTypes.expr * stmt * stmt
  | Swhile  of EcTypes.expr * stmt
  | Sassert of EcTypes.expr

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

    | Scall (lv1, f1, es1), Scall (lv2, f2, es2) ->
           (EcUtils.opt_equal lv_equal lv1 lv2)
        && (EcPath.x_equal f1 f2)
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

    | Scall (lv, f, tys) ->
        Why3.Hashcons.combine_list EcTypes.e_hash
          (Why3.Hashcons.combine
             (Hashtbl.hash lv) (EcPath.x_hash f))
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
        let ffv = EcPath.x_fv EcIdent.Mid.empty f in
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

let i_asgn   (lv, e)      = mk_instr (Sasgn (lv, e))
let i_rnd    (lv, e)      = mk_instr (Srnd (lv, e))
let i_call   (lv, m, tys) = mk_instr (Scall (lv, m, tys))
let i_if     (c, s1, s2)  = mk_instr (Sif (c, s1, s2))
let i_while  (c, s)       = mk_instr (Swhile (c, s))
let i_assert e            = mk_instr (Sassert e)

let stmt s = 
  Hstmt.hashcons { s_node = s; s_tag = -1; s_fv = EcIdent.Mid.empty}

let rstmt s = stmt (List.rev s)

let s_split n s = List.take_n n s.s_node

let destr_asgn i = 
  match i.i_node with
  | Sasgn(lv,e) -> (lv,e)
  | _ -> raise Not_found

let destr_rnd i = 
  match i.i_node with
  | Srnd(lv,e) -> (lv,e)
  | _ -> raise Not_found

let destr_call i = 
  match i.i_node with
  | Scall(lv,f,es) -> (lv,f,es)
  | _ -> raise Not_found

let destr_if i = 
  match i.i_node with
  | Sif(e,s1,s2) -> (e,s1,s2)
  | _ -> raise Not_found

let destr_while i = 
  match i.i_node with
  | Swhile(e,s) -> (e,s)
  | _ -> raise Not_found

let destr_assert i = 
  match i.i_node with
  | Sassert e -> e
  | _ -> raise Not_found

(* -------------------------------------------------------------------- *)
module MSHi = EcMaps.MakeMSH(struct type t = instr let tag i = i.i_tag end)
module Hi = MSHi.H

let s_subst (s: EcTypes.e_subst) = 

  let e_subst = EcTypes.e_subst s in
  if e_subst == identity then identity 
  else

    let pvt_subst (pv,ty as p) = 
      let pv' = EcTypes.pv_subst s.EcTypes.es_xp pv in
      let ty' = s.EcTypes.es_ty ty in
      if pv == pv' && ty == ty' then p else 
        (pv',ty') in
    
    let lv_subst lv = 
      match lv with 
      | LvVar pvt ->
        let pvt' = pvt_subst pvt in
        if pvt == pvt' then lv else
          LvVar pvt'
      | LvTuple pvs ->
        let pvs' = List.smart_map pvt_subst pvs in
        if pvs == pvs' then lv else LvTuple pvs'
      | LvMap((p,tys), pv, e, ty) ->
        let p'   = s.EcTypes.es_p p in
        let tys' = List.smart_map s.EcTypes.es_ty tys in
        let pv'  = EcTypes.pv_subst s.EcTypes.es_xp pv in
        let e'   = e_subst e in
        let ty'  = s.EcTypes.es_ty ty in
        if p==p' && tys==tys' && pv==pv' && e==e' && ty==ty' then lv else
          LvMap((p',tys'),pv',e',ty') in
    
    let rec i_subst i = 
      match i.i_node with
      | Sasgn(lv,e) ->
        let lv' = lv_subst lv in
        let e'  = e_subst e in
        if lv == lv' && e == e' then i else 
          i_asgn(lv',e')
      | Srnd(lv,e) ->
        let lv' = lv_subst lv in
        let e'  = e_subst e in
        if lv == lv' && e == e' then i else 
          i_rnd(lv',e')
      | Scall(olv,mp,args) ->
        let olv' = osmart_map olv lv_subst in
        let mp'  = s.EcTypes.es_xp mp in
        let args' = List.smart_map e_subst args in
        if olv == olv' && mp == mp' && args == args' then i else 
          i_call(olv',mp',args')
      | Sif(e,s1,s2) ->
        let e' = e_subst e in
        let s1' = s_subst s1 in
        let s2' = s_subst s2 in
        if e == e' && s1 == s1' && s2 == s2' then i else
          i_if(e', s1', s2')
      | Swhile(e,s1) ->
        let e' = e_subst e in
        let s1' = s_subst s1 in
        if e == e' && s1 == s1' then i else
          i_while(e', s1')
      | Sassert e -> 
        let e' = e_subst e in
        if e == e' then i else
          i_assert e'
            
    and s_subst s = 
      let is = s.s_node in
      let is' = List.smart_map i_subst is in
      if is == is' then s else stmt is' in

    s_subst 

(* -------------------------------------------------------------------- *)
type variable = {
  v_name : symbol;
  v_type : EcTypes.ty;
}

type funsig = {
  fs_name   : symbol;
  fs_params : variable list;
  fs_ret    : EcTypes.ty;
}

(* -------------------------------------------------------------------- *)

type oracle_info = {
  oi_calls  : xpath list; (* The list of oracle that can be called *)
(*  oi_reads  : Sx.t;    (* The list of global prog var of the outside word *)
  oi_writes : Sx.t;      (* that can be read only or read and write *) *)
}

type module_type = {
  mt_params : (EcIdent.t * module_type) list;
  mt_name   : EcPath.path;
  mt_args   : EcPath.mpath list;
}

type module_sig_body_item =
(*  | Tys_variable of variable *)
  | Tys_function of funsig * oracle_info

type module_sig_body = module_sig_body_item list

type module_sig = {
  mis_params : (EcIdent.t * module_type) list;
  mis_body   : module_sig_body;
}

(* -------------------------------------------------------------------- *)
type uses = {
  us_calls  : xpath list;
  us_reads  : Sx.t;
  us_writes : Sx.t;
}

type function_def = {
  f_locals : variable list;
  f_body   : stmt;
  f_ret    : EcTypes.expr option;
  f_uses   : uses;
}

type function_body =
| FBdef of function_def
| FBabs of oracle_info

type function_ = {
  f_name   : symbol;
  f_sig    : funsig;
  f_def    : function_body;
}

(* -------------------------------------------------------------------- *)
type module_expr = {
  me_name      : symbol;
  me_body      : module_body;
  me_comps     : module_comps;
  me_sig       : module_sig; 
(*  me_types     : module_type list; *)
}

and module_body =
  | ME_Alias       of EcPath.mpath
  | ME_Structure   of module_structure
  | ME_Decl        of module_type * EcPath.Sm.t 

and module_structure = {
  ms_body : module_item list;
  ms_vars : EcTypes.ty Mx.t; (* The set of global variables declared by the
                                module and it submodules *)
  ms_uses : Sm.t; (* The set of external top-level modules used by the module.
                     It is an invariant that those modules are defined 
                     (i.e are ME_structure). *)
}

and module_item =
  | MI_Module   of module_expr
  | MI_Variable of variable
  | MI_Function of function_

and module_comps = module_comps_item list

and module_comps_item = module_item

(* -------------------------------------------------------------------- *)
let vd_equal vd1 vd2 = 
  vd1.v_name = vd2.v_name && 
  EcTypes.ty_equal vd1.v_type vd2.v_type

let vd_hash vd =
  Why3.Hashcons.combine (Hashtbl.hash vd.v_name) (EcTypes.ty_hash vd.v_type)

let fd_equal f1 f2 =
     (s_equal f1.f_body f2.f_body)
  && (EcUtils.opt_equal EcTypes.e_equal f1.f_ret f2.f_ret)
  && (List.all2 vd_equal f1.f_locals f2.f_locals)

let fd_hash f =
  Why3.Hashcons.combine2
    (s_hash f.f_body)
    (Why3.Hashcons.combine_option EcTypes.e_hash f.f_ret)
    (Why3.Hashcons.combine_list vd_hash 0 f.f_locals)

(* -------------------------------------------------------------------- *)
let rec mty_subst sp sm mty =
  let mt_params = List.map (sndmap (mty_subst sp sm)) mty.mt_params in
  let mt_name   = sp mty.mt_name in
  let mt_args   = List.map sm mty.mt_args in
  { mt_params; mt_name; mt_args; }

let mty_hash mty =
  Why3.Hashcons.combine2
    (EcPath.p_hash mty.mt_name)
    (Why3.Hashcons.combine_list
       (fun (x, _) -> EcIdent.id_hash x)
       0 mty.mt_params)
    (Why3.Hashcons.combine_list EcPath.m_hash 0 mty.mt_args)

let rec mty_equal mty1 mty2 =
     (EcPath.p_equal mty1.mt_name mty2.mt_name)
  && (List.all2 EcPath.m_equal mty1.mt_args mty2.mt_args)
  && (List.all2 (pair_equal EcIdent.id_equal mty_equal) mty1.mt_params mty2.mt_params)

