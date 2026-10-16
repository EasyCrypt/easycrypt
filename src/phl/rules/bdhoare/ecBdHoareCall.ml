(* -------------------------------------------------------------------- *)
open EcUtils
open EcParsetree
open EcAst
open EcTypes
open EcModules
open EcFol
open EcEnv
open EcPV
open EcSubst

open EcCoreGoal
open EcLowGoal
open EcLowPhlGoal

module TTC = EcProofTyping

(* -------------------------------------------------------------------- *)
(* Parameters of the bdhoare [call] rule: the specification of the called
   procedure and the optional bound of that specification. *)
type bdhoare_call = {
  bhcall_pre  : ss_inv;          (* precondition P of the procedure *)
  bhcall_post : ss_inv;          (* postcondition Q of the procedure *)
  bhcall_bd   : ss_inv option;   (* bound of the procedure, if not d *)
}

type EcCoreGoal.rule += RBdHoareCall of bdhoare_call

(* -------------------------------------------------------------------- *)
(* The specification [phoare [f : P ==> Q] cmp bd] of the called
   procedure, [bd] being [opt_bd] when given, the bound [d] of the goal
   otherwise. Fails when [opt_bd] is given for an upper bound. *)
let bdhoare_call_spec fpre fpost f cmp bd opt_bd =
  let msg =
    "optional bound parameter not allowed for upper-bounded judgements" in

  match cmp, opt_bd with
  | FHle, Some _  -> failwith msg
  | FHle, None    -> f_bdHoareF fpre f fpost FHle bd
  | FHeq, Some bd -> f_bdHoareF fpre f fpost FHeq bd
  | FHeq, None    -> f_bdHoareF fpre f fpost FHeq bd
  | FHge, Some bd -> f_bdHoareF fpre f fpost FHge bd
  | FHge, None    -> f_bdHoareF fpre f fpost FHge bd

(* -------------------------------------------------------------------- *)
(* Pure core shared by the rule and its checker. Its side conditions (the
   last instruction is a call, the bound given to the procedure depends
   neither on local variables nor on variables written before the call, no
   optional bound for an upper bound) are part of it, so the checker
   re-validates them. Their failures are the user-facing messages. *)
let bdhoare_call_subgoals (hyps : LDecl.hyps) (bhs : bdHoareS) (n : bdhoare_call) =
  let env = LDecl.toenv hyps in
  let (lp,f,args),s =
    match s_last destr_call bhs.bhs_s with
    | None   -> failwith "invalid last instruction"
    | Some x -> x in
  let fpre, fpost, opt_bd = n.bhcall_pre, n.bhcall_post, n.bhcall_bd in
  let m =  fpre.m in
  let fsig = (Fun.by_xpath f env).f_sig in
  let bhs_bd = ss_inv_rebind (bhs_bd bhs) m in
  let bhs_po = ss_inv_rebind (bhs_po bhs) m in
  let bhs_pr = ss_inv_rebind (bhs_pr bhs) m in

  (* The bound of the specification of the called procedure (the bound of
     the conclusion, or [opt_bd]) is interpreted in the memory the procedure
     starts from: after [s], and with the local variables of the callee.
     The bound of the conclusion is interpreted in the initial memory, with
     the local variables of the caller. The two coincide only if this bound
     depends neither on local variables nor on variables written by [s]. *)
  let callee_bd = odfl bhs_bd opt_bd in
  let fv_bd = PV.fv env callee_bd.m callee_bd.inv in

  if List.exists (fun (pv, _) -> is_loc pv) (fst (PV.elements fv_bd)) then
    failwith "The bound cannot depend on local variables";

  if not (PV.indep env (s_write env s) fv_bd) then
    failwith
      "The bound cannot depend on variables written by the \
       statements preceding the call";

  (* The function satisfies the specification *)
  let f_concl =
    bdhoare_call_spec fpre fpost f bhs.bhs_cmp bhs_bd opt_bd in

  (* The wp *)
  let pvres = pv_res in
  let vres = EcIdent.create "result" in
  let fres = {m;inv=f_local vres fsig.fs_ret} in
  let post = EcPlCall.wp_asgn_call env lp fres bhs_po in
  let fpost = map_ss_inv2 (PVM.subst1 env pvres m) fres fpost in
  let modi = f_write env f in
  let post =
    match bhs.bhs_cmp with
    | FHle -> map_ss_inv2 f_imp_simpl   post fpost
    | FHge -> map_ss_inv2 f_imp_simpl  fpost  post

    | FHeq when f_equal bhs_bd.inv f_r0 ->
        map_ss_inv2 f_imp_simpl post fpost

    | FHeq when f_equal bhs_bd.inv f_r1 ->
        map_ss_inv2 f_imp_simpl  fpost post

    | FHeq -> map_ss_inv2 f_iff_simpl fpost  post in

  let post = generalize_mod_ss_inv env modi post in
  let post = map_ss_inv1 (f_forall_simpl [(vres, GTty fsig.fs_ret)]) post in
  let spre = EcPlCall.subst_args_call env m (e_tuple args) PVM.empty in
  let post = map_ss_inv2 f_anda_simpl (map_ss_inv1 (PVM.subst env spre) fpre) post in

  let concl =
    let _,mt = bhs.bhs_m in
    match bhs.bhs_cmp, opt_bd with
    | FHle, None ->
        let post =empty_hs post in
        f_hoareS mt bhs_pr s post
    | FHeq, Some bd ->
        f_bdHoareS mt bhs_pr s post bhs.bhs_cmp (map_ss_inv2 f_real_div bhs_bd bd)
    | FHeq, None ->
        f_bdHoareS mt bhs_pr s post bhs.bhs_cmp {m;inv=f_r1}
    | FHge, Some bd ->
        f_bdHoareS mt bhs_pr s post bhs.bhs_cmp (map_ss_inv2 f_real_div bhs_bd bd)
    | FHge, None ->
        f_bdHoareS mt bhs_pr s post FHeq {m;inv=f_r1}
    | _, _ -> assert false
  in

  [f_concl; concl]

(* -------------------------------------------------------------------- *)
(* Rule (TCB). *)
let t_bdhoare_call (n : bdhoare_call) (tc : tcenv1) =
  let bhs = tc1_as_bdhoareS tc in
  ignore (tc1_last_call tc bhs.bhs_s : _ * _);
  let sg =
    try  bdhoare_call_subgoals (FApi.tc1_hyps tc) bhs n
    with Failure msg -> tc_error !!tc "%s" msg in
  FApi.xrule1 tc (RBdHoareCall n) sg

(* -------------------------------------------------------------------- *)
let () =
  register_rule_checker
    (function
     | RBdHoareCall n ->
         Some (EcPlRecheck.checker_of "bdhoare-call" pf_as_bdhoareS
                 (fun hyps bhs -> bdhoare_call_subgoals hyps bhs n))
     | _ -> None)

(* -------------------------------------------------------------------- *)
(* Elaboration: the goal is known to be a [bdHoareS]. Types the cut of
   [call]: the specification of the last call. *)
let process_bdhoare_call_cut (side : oside) (info : call_info) (tc : tcenv1) =
  let hyps, concl = FApi.tc1_flat tc in
  let bhs = destr_bdHoareS concl in
  let last_f () = proj3_2 (fst (tc1_last_call tc bhs.bhs_s)) in
  (* No optional bound: the specification is built without failure. *)
  let spec fpre fpost f =
    bdhoare_call_spec fpre fpost f bhs.bhs_cmp
      (ss_inv_rebind (bhs_bd bhs) fpre.m) None in

  match info with
  | CI_spec (pre, epost) ->
    if not (is_none side) then
      tc_error !!tc "side can only be given for prhl judgements";
    let f = last_f () in
    let m = EcIdent.create "&hr" in
    let penv, qenv = LDecl.hoareF m f hyps in
    let pre  = TTC.pf_process_form !!tc penv tbool pre  in
    let post = TTC.pf_process_form !!tc qenv tbool epost.pnormal in
    (spec {m;inv=pre} {m;inv=post} f, t_id)

  | CI_inv inv ->
    if not (is_none side) then
      tc_error !!tc "cannot specify side for call with invariants";
    let m    = fst bhs.bhs_m in
    let f    = last_f () in
    let hyps = LDecl.push_active_ss (EcMemory.abstract m) hyps in
    let inv  = TTC.pf_process_form !!tc hyps tbool inv in
    let inv  = {m; inv} in
    let t_spec tc =
      FApi.t_firsts t_trivial 2 (EcPhlFun.t_fun (Inv_ss inv) tc) in
    (spec inv inv f, t_spec)

  | CI_upto _ ->
    if not (is_none side) then
      tc_error !!tc "cannot specify side for call with invariants";
    tc_error !!tc "the conclusion is not an equiv"
