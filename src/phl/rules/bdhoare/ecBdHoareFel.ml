(* -------------------------------------------------------------------- *)
open EcUtils
open EcParsetree
open EcPath
open EcAst
open EcTypes
open EcModules
open EcFol
open EcEnv
open EcPV

open EcCoreGoal

module TTC = EcProofTyping

(* -------------------------------------------------------------------- *)
(* The bound of the rule is a sum over [range 0 q], built with the
   operators of the [FelTactic] theory (and of the theories it requires). *)
module IFEL : sig
  val loaded : env -> bool
  val felsum : form -> (form * form) -> form
end = struct
  open EcCoreLib

  let i_Fel  = "FelTactic"
  let p_Fel  = EcPath.pqname EcCoreLib.p_top i_Fel
  let p_List = [i_top; "List"]
  let p_BRA  = [i_top; "StdBigop"; "Bigreal"; "BRA"]

  let tlist =
    let tlist = EcPath.fromqsymbol (p_List, "list") in
    fun ty -> EcTypes.tconstr tlist [ty]

  let range =
    let rg = EcPath.fromqsymbol (p_List @ ["Range"], "range") in
    let rg = f_op rg [] (toarrow [tint; tint] (tlist tint)) in
    fun m n -> f_app rg [m; n] (tlist tint)

  let felsum =
    let bgty = [tpred tint; tfun tint treal; tlist tint] in
    let bg   = EcPath.fromqsymbol (p_BRA, "big") in
    let bg   = f_op bg [tint] (toarrow bgty treal) in
    let prT  = EcPath.fromqsymbol ([i_top; "Logic"], "predT") in
    let prT  = f_op prT [tint] (tpred tint) in
    fun f (m, n) -> f_app bg [prT; f; range m n] treal

  let loaded (env : env) =
    is_some (EcEnv.Theory.by_path_opt p_Fel env)
end

(* -------------------------------------------------------------------- *)
(* Parameters of the [fel] rule as supplied by the caller: high level, the
   split position is still a symbolic code gap that must be resolved. The
   counter, event, invariant and oracle preconditions share one memory. *)
type fel_rule = {
  felr_at    : EcMatching.Position.codegap1;   (* end of the initialization *)
  felr_cntr  : ss_inv;                         (* counter *)
  felr_asg   : form;                           (* bound of a step, int -> real *)
  felr_q     : form;                           (* maximal counter value *)
  felr_event : ss_inv;                         (* failure event *)
  felr_specs : (xpath * ss_inv) list;          (* oracle preconditions *)
  felr_inv   : ss_inv;                         (* invariant *)
}

(* Low-level parameters recorded in the proof-node: the split position is the
   RESOLVED integer index. The oracles are not recorded: the builder
   recomputes them from the program. *)
type fel_node = {
  feln_at    : EcMatching.Position.nm_codegap1;
  feln_cntr  : ss_inv;
  feln_asg   : form;
  feln_q     : form;
  feln_event : ss_inv;
  feln_specs : (xpath * ss_inv) list;
  feln_inv   : ss_inv;
}

type EcCoreGoal.rule += RBdHoareFel of fel_node

(* -------------------------------------------------------------------- *)
(* The oracles of [s] that may write [modv]: the procedures called by [s]
   (transitively, through the procedures that do not write [modv]
   themselves) writing [modv] outside of their own calls. *)
let rec callable_oracles_f env modv os f =
  let f'   = NormMp.norm_xfun env f in
  let func = Fun.by_xpath f' env in

  match func.f_def with
  | FBalias _ ->
      assert false (* normal form *)

  | FBabs oi ->
    let called_fs =
      List.fold_left
        (fun s o ->
           if   PV.indep env modv (f_write env o)
           then s
           else EcPath.Sx.add o s)
        EcPath.Sx.empty (OI.allowed oi)
    in

    List.fold_left
      (callable_oracles_f env modv)
      os (EcPath.Sx.elements called_fs)

  | FBdef fdef ->
      let called_fs =
        List.fold_left
          (fun s o ->
            if   PV.indep env modv (f_write env o)
            then s
            else EcPath.Sx.add o s)
          EcPath.Sx.empty fdef.f_uses.us_calls in

      let f_written = f_write ~except:called_fs env f in

      if PV.indep env f_written modv then
        List.fold_left
          (callable_oracles_f env modv)
          os (EcPath.Sx.elements called_fs)
      else
        EcPath.Sx.add f os

and callable_oracles_s env modv os s =
  callable_oracles_is env modv os s.s_node

and callable_oracles_is env modv os is =
  List.fold_left (callable_oracles_i env modv) os is

and callable_oracles_sx env modv os ss =
  List.fold_left (callable_oracles_s env modv) os ss

and callable_oracles_i env modv os i =
  match i.i_node with
    | Scall  (_, f, _)   -> callable_oracles_f  env modv os f
    | Swhile (_, s)      -> callable_oracles_s  env modv os s
    | Smatch (_, b)      -> callable_oracles_sx env modv os (List.map snd b)
    | Sif    (_, s1, s2) -> callable_oracles_sx env modv os [s1; s2]

    | Sasgn _ | Srnd _ | Sraise _ -> os

    | Sabstract _ -> assert false (* FIXME *)

let callable_oracles_stmt env modv =
  callable_oracles_s env modv EcPath.Sx.empty

(* -------------------------------------------------------------------- *)
(* The goal of the rule: [Pr[f(args) @ &m : ev] <= bd]. *)
let destr_pr_le (f : form) : (pr * form) option =
  match f.f_node with
  | Fapp ({ f_node = Fop (op, _) }, [pr; bd])
      when is_pr pr && EcPath.p_equal op EcCoreLib.CI_Real.p_real_le
    -> Some (destr_pr pr, bd)
  | _ -> None

let pf_as_pr_le (pe : proofenv) (f : form) =
  match destr_pr_le f with
  | Some x -> x
  | None   -> tc_error pe "a goal of the form Pr[ _ ] <= _ is required"

(* -------------------------------------------------------------------- *)
(* Raised by the builder when the counter, the event or the invariant is
   written by the program after the initialization outside of the oracles
   (what is written there, and the variables of the three). *)
exception FelModified of PV.t * PV.t

(* Pure core shared by the rule and its checker. Its side condition (after
   the initialization, the counter, the event and the invariant are only
   written by the oracles) is part of it, so the checker re-validates it;
   the oracles are recomputed from the program. The binders [c] and [b] of
   the oracle premises are fresh at each call: the checker compares up to
   alpha-conversion. *)
let fel_subgoals (hyps : LDecl.hyps) ((pr, bd) : pr * form) (n : fel_node) =
  let env = LDecl.toenv hyps in
  let { feln_cntr = cntr; feln_asg = ash; feln_q = q;
        feln_event = f_event; feln_inv = inv; } = n in

  let f  = NormMp.norm_xfun env pr.pr_fun in
  let ev = pr.pr_event in

  let memenv, (fsig, fdef), _ = Fun.hoareS ev.m f env in

  let s_hd, s_tl = EcMatching.Position.split_at_nmcgap1 n.feln_at fdef.f_body in
  let fve        = PV.fv env f_event.m f_event.inv in
  let fvc        = PV.fv env cntr.m cntr.inv in
  let fvi        = PV.fv env inv.m inv.inv in
  let fv         = PV.union (PV.union fve fvc) fvi in
  let os         = callable_oracles_stmt env fv (stmt s_tl) in

  (* check that bad event, cntr and inv are only modified in oracles *)
  let written_except_os = s_write ~except:os env (stmt s_tl) in

  if not (PV.indep env written_except_os fv) then
    raise (FelModified (written_except_os, fv));

  (* subgoal on the bounds *)
  let bound_goal =
    let v = IFEL.felsum ash (f_i0, q) in
    f_real_le v bd
  in

  (* we must quantify over memories *)
  let post_goal =
    let lev = map_ss_inv2 f_and f_event (map_ss_inv1 (fun cnt -> f_int_le cnt q) cntr) in
    let m = EcEnv.Fun.prF_memenv ev.m f env in
    let lev = EcSubst.ss_inv_rebind lev (fst m) in
    let ev = EcSubst.ss_inv_rebind ev (fst m) in
    let inv = EcSubst.ss_inv_rebind inv (fst m) in
    let f_imps' l = f_imps (List.tl l) (List.hd l) in
    let p = map_ss_inv f_imps' [lev;ev;inv] in
    EcSubst.f_forall_mems_ss_inv m p
  in

  (* not fail and cntr=0 and invariant holds at designated program point,
     under the pre that the initial parameter values correspond to arguments,
     and that the initial values of global read variables
     are equal to the initial memory *)
  let init_goal =
    let xs,gs = PV.ntr_elements (f_read env f) in
    let m = fst memenv in
    let pr_m = pr.pr_mem in
    let f_xeq (x,ty) = map_ss_inv2 f_eq (f_pvar x ty m) {m;inv=(f_pvar x ty pr_m).inv} in
    let eqxs = List.map f_xeq xs in
    let eqgs = List.map (fun m' -> {m;inv=f_eqglob m' m m' pr_m}) gs in
    let eqparams =
      let vs = fsig.fs_anames in
      let var_of_ovar ov = { v_name = oget ov.ov_name; v_type = ov.ov_type } in
      let f_x x = assert (is_some x.ov_name); (f_pvloc (var_of_ovar x) m) in
      map_ss_inv2 f_eq (map_ss_inv ~m f_tuple (List.map f_x vs)) {m;inv=pr.pr_args} in
    let pre = map_ss_inv f_ands (eqparams :: (eqxs@eqgs)) in
    let p = map_ss_inv2 f_and (map_ss_inv1 f_not f_event) (map_ss_inv2 f_eq cntr {m=cntr.m;inv=f_i0}) in
    let p = map_ss_inv2 f_and_simpl p inv in
    let p = { hsi_m = p.m; hsi_inv = (POE.empty p.inv); } in
    let p = EcSubst.hs_inv_rebind p pre.m in
    f_hoareS (snd memenv) pre (stmt s_hd) p
  in

  let oracle_goal o =
    let some_p =
      n.feln_specs
        |> List.ofind (fun (o', _) -> o = o')
        |> omap snd
        |> odfl {m=f_event.m; inv=f_true}
    in

    let not_F_to_F_goal =
      let bound = map_ss_inv1 (fun cn -> f_app_simpl ash [cn] treal) cntr in
      let pre = map_ss_inv1 (fun cn -> f_and (f_int_le f_i0 cn) (f_int_lt cn q)) cntr in
      let pre = map_ss_inv2 f_and pre (map_ss_inv1 f_not f_event) in
      let pre = map_ss_inv2 f_and_simpl pre inv in
      let pre = map_ss_inv2 f_and_simpl pre some_p in
      let post = f_event in
      f_bdHoareF pre o post FHle bound
    in
    let old_cntr_id = EcIdent.create "c" in
    let old_b_id = EcIdent.create "b" in
    let old_cntr = f_local old_cntr_id tint in
    let old_b = f_local old_b_id tbool in

    let cntr_decr_goal =
      let old_cntr = {m=cntr.m;inv=old_cntr} in
      let pre  = map_ss_inv2 f_and some_p (map_ss_inv2 f_eq old_cntr cntr) in
      let pre = map_ss_inv2 f_and_simpl pre inv in
      let post = map_ss_inv2 f_int_lt old_cntr cntr in
      let post = map_ss_inv2 f_and_simpl post inv in
      let post = { hsi_m = post.m; hsi_inv = POE.empty post.inv; } in
      f_forall_simpl [old_cntr_id,GTty tint] (f_hoareF pre o post)
    in
    let cntr_stable_goal =
      let old_cntr = {m=cntr.m;inv=old_cntr} in
      let old_b = {m=cntr.m;inv=old_b} in
      let pre  = map_ss_inv f_ands [
        map_ss_inv1 f_not some_p;
        map_ss_inv2 f_eq f_event old_b;
        map_ss_inv2 f_eq cntr old_cntr] in
      let pre  = map_ss_inv2 f_and_simpl pre inv in
      let post = map_ss_inv f_ands [map_ss_inv2 f_eq f_event old_b; map_ss_inv2 f_int_le old_cntr cntr] in
      let post = map_ss_inv2 f_and_simpl post inv in
      let post = { hsi_m = post.m; hsi_inv = POE.empty post.inv; } in
        f_forall_simpl
          [old_b_id,GTty tbool; old_cntr_id,GTty tint]
          (f_hoareF pre o post)
    in
    [not_F_to_F_goal;cntr_decr_goal;cntr_stable_goal]
  in

  let os_goals =
    List.concat (List.map oracle_goal (Sx.ntr_elements os)) in

  bound_goal :: post_goal :: init_goal :: os_goals

(* -------------------------------------------------------------------- *)
(* Rule (TCB): check the shape of the goal and that the procedure is
   defined, resolve the code gap to an index (the env-dependent step),
   record the resolved node, and build its subgoals through the shared
   core, whose side condition is reported with the tactic's message. *)
let t_bdhoare_fel (r : fel_rule) (tc : tcenv1) =
  let env, hyps, concl = FApi.tc1_eflat tc in

  let (pr, bd) = pf_as_pr_le !!tc concl in

  let f = NormMp.norm_xfun env pr.pr_fun in

  let _, (_, fdef), _ =
    try  Fun.hoareS pr.pr_event.m f env
    with _ -> tc_error !!tc "not applicable to abstract functions"
  in

  let n =
    { feln_at    = EcLowPhlGoal.s_split_index env r.felr_at fdef.f_body;
      feln_cntr  = r.felr_cntr;
      feln_asg   = r.felr_asg;
      feln_q     = r.felr_q;
      feln_event = r.felr_event;
      feln_specs = r.felr_specs;
      feln_inv   = r.felr_inv; } in

  let subgoals =
    try  fel_subgoals hyps (pr, bd) n
    with FelModified (written, fv) ->
      tc_error_lazy !!tc (fun fmt ->
        Format.fprintf fmt
          "%s@. @[%a@] is not disjoint from @[%a@]@."
          "after initialization fail-event or invariant or counter is modified outside oracles"
          (PV.pp env) written (PV.pp env) fv)
  in

  FApi.xrule1 tc (RBdHoareFel n) subgoals

(* -------------------------------------------------------------------- *)
(* Checker: rerun the core on the recorded node and on the goal's own
   program; it never redoes code resolution. *)
let () =
  register_rule_checker
    (function
     | RBdHoareFel n ->
         Some (EcPlRecheck.checker_of "bdhoare-fel" pf_as_pr_le
                 (fun hyps prbd -> fel_subgoals hyps prbd n))
     | _ -> None)

(* -------------------------------------------------------------------- *)
(* Elaboration: the [FelTactic] theory must be loaded and the goal must be
   [Pr[f(args) @ &m : ev] <= bd]. The counter, the event, the invariant and
   the oracle preconditions are typed in a fresh memory [&hr] (the oracle
   preconditions in the memory of their oracle), the step bound and [q] in
   the memory [&m] of the probability. Applies [t_bdhoare_fel]. *)
let process_bdhoare_fel (at_pos : pcodegap1) (infos : fel_info) (tc : tcenv1) =
  let env, hyps1, concl = FApi.tc1_eflat tc in

  if not (IFEL.loaded env) then
    tacuerror "fel: load the `FelTactic' theory first";

  let (pr, _) = pf_as_pr_le !!tc concl in

  let m = EcIdent.create "&hr" in
  let at_pos  = EcTyping.trans_codegap1 env at_pos in
  let hyps    = LDecl.inv_memenv1 m hyps1 in
  let cntr    = {m;inv=TTC.pf_process_form !!tc hyps tint infos.pfel_cntr} in
  let hypsq   = LDecl.push_active_ss (EcMemory.abstract pr.pr_mem) hyps1 in
  let ash     = TTC.pf_process_form !!tc hypsq (tfun tint treal) infos.pfel_asg in
  let q       = TTC.pf_process_form !!tc hypsq tint infos.pfel_q in
  let f_event = {m;inv=TTC.pf_process_form !!tc hyps tbool infos.pfel_event} in
  let inv     =
    infos.pfel_inv
      |> omap (fun inv -> {m;inv=TTC.pf_process_form !!tc hyps tbool inv})
      |> odfl {m;inv=f_true}
  in

  let process_pred (f,pre) =
    let env  = LDecl.toenv hyps in
    let f    = EcTyping.trans_gamepath env f in
    let penv = fst (LDecl.hoareF m f hyps) in
      (f, {m;inv=TTC.pf_process_form !!tc penv tbool pre})
  in

  let pred_specs = List.map process_pred infos.pfel_specs in

  t_bdhoare_fel
    { felr_at    = at_pos;
      felr_cntr  = cntr;
      felr_asg   = ash;
      felr_q     = q;
      felr_event = f_event;
      felr_specs = pred_specs;
      felr_inv   = inv; }
    tc
