(* -------------------------------------------------------------------- *)
open EcUtils
open EcParsetree
open EcTypes
open EcFol
open EcAst
open EcModules
open EcEnv

open EcCoreGoal
open EcLowGoal
open EcLowPhlGoal

(* -------------------------------------------------------------------- *)
(* The one-sided equiv [match] rule is parameterized by its side, nothing
   to resolve: the same record is the rule argument and the node payload.
   The two-sided rules have no parameters: the statements are the
   [match]es. *)
type equiv_match_onesided = {
  emo_side : side;
}

type EcCoreGoal.rule +=
  | REquivMatchOneSided of equiv_match_onesided
  | REquivMatchSynced
  | REquivMatchEq

(* -------------------------------------------------------------------- *)
(* The statement [s], a single [match]. *)
let single_match (who : string) (s : stmt) =
  match s.s_node with
  | [{ i_node = Smatch (e, bs) }] -> (e, bs)
  | _ -> failwith (who ^ ": the statement is not a single match")

(* -------------------------------------------------------------------- *)
(* Pure core of the one-sided rule, shared by the rule and its checker. Its
   side condition (the statement of that side is a single [match]) is part
   of it, so the checker re-validates it. The constructors are read from
   the environment. *)
let equiv_match_onesided_subgoals
    (hyps : LDecl.hyps) (es : equivS) (n : equiv_match_onesided)
=
  let side = n.emo_side in
  let m, mo = sideif side (es.es_ml, es.es_mr) (es.es_mr, es.es_ml) in
  let e, bs =
    single_match "equiv-match-onesided" (sideif side es.es_sl es.es_sr) in
  let generalize_other inv =
    sideif side
      (ss_inv_generalize_right inv (fst mo))
      (ss_inv_generalize_left  inv (fst mo)) in

  let concl (mb : EcPlMatch.match_branch) =
    let cond = generalize_other mb.mb_cond in
    let (ml, mr), (sl, sr) =
      sideif side
        ((mb.mb_mem, es.es_mr), (mb.mb_body, es.es_sr))
        ((es.es_ml, mb.mb_mem), (es.es_sl, mb.mb_body)) in
    f_equivS (snd ml) (snd mr) (map_ts_inv2 f_and cond (es_pr es))
      sl sr (es_po es) in

  List.map concl (EcPlMatch.match_branches (LDecl.toenv hyps) m e bs)

(* -------------------------------------------------------------------- *)
(* The two-sided rules: the [match]es of both sides, and the datatype
   (path, declaration, type instance of each side) they are on. *)
let single_matches (who : string) (env : env) (es : equivS) =
  let el, bsl = single_match who es.es_sl in
  let er, bsr = single_match who es.es_sr in
  let pl, dt, tyl = oget (EcEnv.Ty.get_top_decl el.e_ty env) in
  let pr, _ , tyr = oget (EcEnv.Ty.get_top_decl er.e_ty env) in
  if not (EcPath.p_equal pl pr) then
    failwith (who ^ ": matches on different inductive types");
  let dt = oget (EcDecl.tydecl_as_datatype dt) in
  ((el, bsl), (er, bsr)), (pl, dt, tyl, tyr)

(* The constructor [c] of the datatype [p], at type instance [tys], with
   arguments of types [atys] and result type [rty]. *)
let f_ctor (p : EcPath.path) (tys : ty list) c (atys : ty list) (rty : ty) =
  f_op (EcPath.pqoname (EcPath.prefix p) c) tys (toarrow atys rty)

(* [f = cop xs]. *)
let f_eq_app (cop : form) (xs : (EcIdent.t * ty) list) (f : ts_inv) =
  map_ts_inv1
    (fun f -> f_eq f (f_app cop (List.map (curry f_local) xs) f.f_ty)) f

(* The precondition of a branch premise: [eql /\ eqr /\ P], simplifying. *)
let branch_pre (es : equivS) (eql : ts_inv) (eqr : ts_inv) =
  map_ts_inv3 (fun p l r -> f_ands_simpl [l; r] p) (es_pr es) eql eqr

(* Pure core of the synchronized rule, shared by the rule and its checker.
   Its side conditions are part of it. The logical variables bound in the
   premises are fresh at each call: the checker compares up to
   alpha-conversion. *)
let equiv_match_synced_subgoals (hyps : LDecl.hyps) (es : equivS) =
  let env = LDecl.toenv hyps in
  let ml, mr = fst es.es_ml, fst es.es_mr in
  let ((el, bsl), (er, bsr)), (p, dt, tyl, tyr) =
    single_matches "equiv-match-synced" env es in

  let fl = ss_inv_generalize_right (ss_inv_of_expr ml el) mr in
  let fr = ss_inv_generalize_left  (ss_inv_of_expr mr er) ml in

  let copl c cl = f_ctor p tyl c (List.snd cl) fl.inv.f_ty in
  let copr c cr = f_ctor p tyr c (List.snd cr) fr.inv.f_ty in

  (* forall &1 &2, P => ((exists xs, el = C xs) <=> (exists xs', er = C xs')) *)
  let cond ((c, _), ((cl, _), (cr, _))) =
    let xl  = List.map (fst_map EcIdent.fresh) cl in
    let xr  = List.map (fst_map EcIdent.fresh) cr in
    let ex xs = map_ts_inv1 (f_exists (List.map (snd_map gtty) xs)) in
    let lhs = ex xl (f_eq_app (copl c cl) xl fl) in
    let rhs = ex xr (f_eq_app (copr c cr) xr fr) in
    EcSubst.f_forall_mems_ts_inv es.es_ml es.es_mr
      (map_ts_inv2 f_imp_simpl (es_pr es) (map_ts_inv2 f_iff lhs rhs)) in

  (* forall xs xs',
       equiv [bl ~ br : el = C xs /\ er = C xs' /\ P ==> Q]
     (simplifying conjunction) *)
  let goal ((c, _), ((cl, bl), (cr, br))) =
    let sb      = Fsubst.f_subst_id in
    let sb, xl  = add_elocals sb cl in
    let sb, xr  = add_elocals sb cr in
    let pre =
      branch_pre es (f_eq_app (copl c cl) xl fl) (f_eq_app (copr c cr) xr fr) in
    f_forall (List.map (snd_map gtty) (xl @ xr))
      (f_equivS (snd es.es_ml) (snd es.es_mr) pre
         (s_subst sb bl) (s_subst sb br) (es_po es)) in

  let infos = List.combine dt.EcDecl.tydt_ctors (List.combine bsl bsr) in

  List.map cond infos @ List.map goal infos

(* Pure core of the rule on equal values, shared by the rule and its
   checker. Its side conditions are part of it. The logical variables bound
   in the premises are fresh at each call: the checker compares up to
   alpha-conversion. *)
let equiv_match_eq_subgoals (hyps : LDecl.hyps) (es : equivS) =
  let env = LDecl.toenv hyps in
  let ml, mr = fst es.es_ml, fst es.es_mr in
  let ((el, bsl), (er, bsr)), (p, dt, tyl, tyr) =
    single_matches "equiv-match-eq" env es in

  if not (EcReduction.EqTest.for_type env el.e_ty er.e_ty) then
    failwith "equiv-match-eq: matches on different types";

  let fl = ss_inv_generalize_right (ss_inv_of_expr ml el) mr in
  let fr = ss_inv_generalize_left  (ss_inv_of_expr mr er) ml in

  (* forall &1 &2, P => el = er *)
  let cond =
    EcSubst.f_forall_mems_ts_inv es.es_ml es.es_mr
      (map_ts_inv2 f_imp_simpl (es_pr es) (map_ts_inv2 f_eq fl fr)) in

  (* forall xs,
       equiv [bl ~ br[xs/xs'] : el = C xs /\ er = C xs /\ P ==> Q]
     (simplifying conjunction) *)
  let goal ((c, _), ((cl, bl), (cr, br))) =
    let sb     = f_subst_init () in
    let sb, xs = add_elocals sb cl in
    let sb =
      List.fold_left2
        (fun sb (x, xty) (y, _) ->
          bind_elocal sb y (e_subst sb (e_local x xty)))
        sb cl cr in
    let copl = f_ctor p tyl c (List.snd cl) fl.inv.f_ty in
    let copr = f_ctor p tyr c (List.snd cr) fr.inv.f_ty in
    let pre  = branch_pre es (f_eq_app copl xs fl) (f_eq_app copr xs fr) in
    f_forall (List.map (snd_map gtty) xs)
      (f_equivS (snd es.es_ml) (snd es.es_mr) pre
         (s_subst sb bl) (s_subst sb br) (es_po es)) in

  let infos = List.combine dt.EcDecl.tydt_ctors (List.combine bsl bsr) in

  cond :: List.map goal infos

(* -------------------------------------------------------------------- *)
(* Rules (TCB). *)
let t_equiv_match_onesided (r : equiv_match_onesided) (tc : tcenv1) =
  let es = tc1_as_equivS tc in
  let sg =
    try  equiv_match_onesided_subgoals (FApi.tc1_hyps tc) es r
    with Failure msg -> tc_error !!tc "%s" msg in
  FApi.xrule1 tc (REquivMatchOneSided r) sg

let t_equiv_match_synced (tc : tcenv1) =
  let es = tc1_as_equivS tc in
  let sg =
    try  equiv_match_synced_subgoals (FApi.tc1_hyps tc) es
    with Failure msg -> tc_error !!tc "%s" msg in
  FApi.xrule1 tc REquivMatchSynced sg

let t_equiv_match_eq (tc : tcenv1) =
  let es = tc1_as_equivS tc in
  let sg =
    try  equiv_match_eq_subgoals (FApi.tc1_hyps tc) es
    with Failure msg -> tc_error !!tc "%s" msg in
  FApi.xrule1 tc REquivMatchEq sg

(* -------------------------------------------------------------------- *)
let () =
  register_rule_checker
    (function
     | REquivMatchOneSided n ->
         Some (EcPlRecheck.checker_of "equiv-match-onesided" pf_as_equivS
                 (fun hyps es -> equiv_match_onesided_subgoals hyps es n))
     | REquivMatchSynced ->
         Some (EcPlRecheck.checker_of "equiv-match-synced" pf_as_equivS
                 equiv_match_synced_subgoals)
     | REquivMatchEq ->
         Some (EcPlRecheck.checker_of "equiv-match-eq" pf_as_equivS
                 equiv_match_eq_subgoals)
     | _ -> None)

(* -------------------------------------------------------------------- *)
(* Derived (no proof-node): push the continuation of the [match] of side
   [side] into its branches, when not empty. *)
let t_equiv_match_push (side : side) (c : stmt) =
  if List.is_empty c.s_node then t_id else
    EcEquivTransform.t_equiv_transform
      { etr_side = side; etr_tr = EcTrMatchPush.TrMatchPush }

(* The user-facing checks of the two-sided forms: both sides start with a
   [match], on the same datatype (and, for [eq], on the same type). They
   return the continuations. *)
let tc1_first_matches ~(eq : bool) (tc : tcenv1) (es : equivS) =
  let env = FApi.tc1_env tc in
  let (el, _), cl = tc1_first_match tc es.es_sl in
  let (er, _), cr = tc1_first_match tc es.es_sr in
  let pl, _, _ = oget (EcEnv.Ty.get_top_decl el.e_ty env) in
  let pr, _, _ = oget (EcEnv.Ty.get_top_decl er.e_ty env) in
  if not (EcPath.p_equal pl pr) then
    tc_error !!tc "match statements on different inductive types";
  if eq && not (EcReduction.EqTest.for_type env el.e_ty er.e_ty) then
    tc_error !!tc "synced match requires matches on the same type";
  (cl, cr)

(* Derived (no proof-node): on [match e with ... end; c] (on one side, or
   on both sides), push the continuations into the branches, then apply
   the one-sided (resp. the synchronized, or on equal values) rule. *)
let t_equiv_match_head (mode : matchmode) (tc : tcenv1) =
  let es = tc1_as_equivS tc in
  match mode with
  | `SSided side ->
      let _, c = tc1_first_match tc (sideif side es.es_sl es.es_sr) in
      FApi.t_seq
        (t_equiv_match_push side c)
        (t_equiv_match_onesided { emo_side = side }) tc

  | `DSided dmode ->
      let cl, cr = tc1_first_matches ~eq:(dmode = `Eq) tc es in
      let rule =
        match dmode with
        | `ConstrSynced -> t_equiv_match_synced
        | `Eq           -> t_equiv_match_eq in
      FApi.t_seqs
        [t_equiv_match_push `Left cl; t_equiv_match_push `Right cr; rule] tc

(* -------------------------------------------------------------------- *)
(* Elaboration: the goal is known to be an [equivS]. *)
let process_equiv_match (mode : matchmode) (tc : tcenv1) =
  t_equiv_match_head mode tc
