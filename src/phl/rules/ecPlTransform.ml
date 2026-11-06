(* -------------------------------------------------------------------- *)
open EcAst
open EcEnv

(* -------------------------------------------------------------------- *)
(* Program transformations: an open catalogue of pure statement-level
   transformations, each registered with the function computing it, and a
   closed set of abstract obligations that each logic's transformation
   rule states in its own terms. *)
type transform = ..

type obligation =
  | OPrefixPost of prefix_post
  | OLossless   of stmt
  | OExprEq     of expr_eq
  | OLocalEquiv of local_equiv

and prefix_post = {
  opp_prefix : stmt;
  opp_cond   : ss_inv;
}

and expr_eq = {
  oee_locals : (EcIdent.t * ty) list;
  oee_lhs    : expr;
  oee_rhs    : expr;
}

and local_equiv = {
  ole_locals : (EcIdent.t * ty) list;
  ole_orig   : stmt;
  ole_new    : stmt;
  ole_reads  : EcPV.PV.t;
  ole_writes : EcPV.PV.t;
  ole_modi   : EcPV.PV.t;
}

type tr_ctxt = {
  trc_hyps : LDecl.hyps;
  trc_env  : env;
  trc_me   : memenv;
  trc_post : EcPV.PV.t Lazy.t;
  trc_exn  : bool;
}

type tr_result = {
  trr_me  : memenv;
  trr_s   : stmt;
  trr_obl : obligation list;
}

exception InvalidTransform of string

(* -------------------------------------------------------------------- *)
(* The registry: partial handlers over the open [transform] type, as for
   the rule checkers ([EcCoreGoal.register_rule_checker]). *)
let entries : (transform -> (tr_ctxt -> stmt -> tr_result) option) list ref =
  ref []

let register f =
  entries := f :: !entries

let apply (ctxt : tr_ctxt) (t : transform) (s : stmt) =
  match List.find_map (fun f -> f t) !entries with
  | None     -> raise (InvalidTransform "unknown program transformation")
  | Some run -> run ctxt s

(* -------------------------------------------------------------------- *)
(* The frame of a local equivalence: the top-level conjuncts of the
   precondition that only talk about the memory [m] and are independent
   from [modi], i.e. that still hold when the fragment runs. *)
let frame (env : env) (m : memory) (modi : EcPV.PV.t) (pre : form) =
  let filter (f : form) =
    let pvs    = EcPV.form_read env EcPV.PMVS.empty f in
    let pvs_me = EcIdent.Mid.find_def EcPV.PV.empty m pvs in
    let pvs    = EcIdent.Mid.remove m pvs in

       EcIdent.Mid.is_empty pvs
    && EcPV.PV.indep env modi pvs_me in

  EcFol.filter_topand_form filter pre

(* -------------------------------------------------------------------- *)
let f_expr_eq (me : memenv) (o : expr_eq) =
  let m  = fst me in
  let f  = EcFol.ss_inv_of_expr m o.oee_lhs in
  let f' = EcFol.ss_inv_of_expr m o.oee_rhs in
  let bd = List.map (fun (x, ty) -> (x, GTty ty)) o.oee_locals in
  EcSubst.f_forall_mems_ss_inv me
    (map_ss_inv1 (EcFol.f_forall bd) (map_ss_inv2 EcFol.f_eq f f'))

(* -------------------------------------------------------------------- *)
(* The original fragment runs in [&1], over the memory type of [me], the
   new one in [&2], over [mt']; the frame is read on [&1]. *)
let f_local_equiv
    (env : env) (me : memenv) (mt' : memtype) (pre : form option)
    (o : local_equiv)
=
  let ml = EcIdent.create "&1" in
  let mr = EcIdent.create "&2" in

  let frame =
    EcUtils.obind (frame env (fst me) o.ole_modi) pre
    |> EcUtils.omap (fun frame ->
         let subst = EcSubst.add_memory EcSubst.empty (fst me) ml in
         EcSubst.subst_form subst frame) in

  let eqs (pvs : EcPV.PV.t) =
    let pvs, globs = EcPV.PV.elements pvs in
    List.map (fun (pv, ty) -> EcFol.f_eq (EcFol.f_pvar pv ty ml).inv (EcFol.f_pvar pv ty mr).inv) pvs
    @ List.map (fun mp -> EcFol.f_eqglob mp ml mp mr) globs in

  EcFol.f_forall
    (List.map (fun (x, ty) -> (x, GTty ty)) o.ole_locals)
    (EcFol.f_equivS (snd me) mt'
       { ml; mr; inv = EcUtils.ofold EcFol.f_and (EcFol.f_ands (eqs o.ole_reads)) frame; }
       o.ole_orig o.ole_new
       { ml; mr; inv = EcFol.f_ands (eqs o.ole_writes); })
