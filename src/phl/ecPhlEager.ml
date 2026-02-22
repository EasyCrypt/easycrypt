open EcAst
open EcCoreGoal
open EcEnv
open EcFol
open EcLowGoal
open EcLowPhlGoal
open EcMatching.Zipper
open EcModules
open EcPV
open EcTypes
open EcUtils
module ER = EcReduction
module PT = EcProofTerm
module TTC = EcProofTyping

(** Builds a formula that represents equality on the list of variables [l]
    between two memories [ml] and [mr] *)
let list_eq_to_form ml mr (l, l_glob) =
  let to_form m = List.map (fun (pv, ty) -> (f_pvar pv ty m).inv) in
  let to_form_glob m =
    List.map (fun x -> (f_glob (EcPath.mget_ident x) m).inv)
  in
  {
    ml;
    mr;
    inv =
      f_eqs
        (to_form ml l @ to_form_glob ml l_glob)
        (to_form mr l @ to_form_glob mr l_glob);
  }

(** Returns a formula that describes equality on all variables from one side of
    the memory present in the formula [q].

    Example: If [q] is [(a{ml} \/ b{m'} /\ c{ml})], (with [ml] the first bound
    memory, [mr] the second and [m'] another memory, distinct from [ml]) then
    this function returns [(a{ml} = a{mr} /\ c{ml} = c{mr})]. The result of this
    operation is sometimes denoted [={q.m1}]. *)
let eq_on_sided_form env { ml; mr; inv } =
  PV.fv env ml inv |> PV.elements |> list_eq_to_form ml mr

(** Returns a formula that describes equality on all variables from both
    memories in predicate [inv], as well as equality on all variables read from
    [c].

    This is used to implement what is denoted [Eq] in the module documentation,
    i.e. equality on the whole memory. *)
let eq_on_form_and_stmt env { ml; mr; inv } c =
  s_read env c
  |> PV.union (PV.fv env ml inv)
  |> PV.union (PV.fv env mr inv)
  |> PV.elements |> list_eq_to_form ml mr

(** Equality on all variables from a function [f] *)
let eq_on_fun env m1 m2 f =
  let l, l' = NormMp.flatten_use (NormMp.fun_use env f) in
  let l_glob = List.map EcPath.mident l in
  let l_pv = List.map (fun (x, ty) -> (pv_glob x, ty)) l' in
  list_eq_to_form m1 m2 (l_pv, l_glob)

(** Given a goal environment [tc] and a statement [s], if the goal is an
    equivalence of the shape [s; c ~ c'; s], returns the same equivalence goal,
    as well as the terms c and c'.

    Yields an error if the statements are not of the right form. *)
let destruct_eager tc s =
  let env = FApi.tc1_env tc
  and es = tc1_as_equivS tc
  and ss = List.length s.s_node in

  let c, c' = (es.es_sl, es.es_sr) in
  let z, c = s_split env (Zpr.cpos ss) c
  and c', z' = s_split env (Zpr.cpos (List.length c'.s_node - ss)) c' in

  let env, _, _ = FApi.tc1_eflat tc in
  let z_eq_s = ER.EqTest.for_stmt env (stmt z) s
  and z'_eq_s = ER.EqTest.for_stmt env (stmt z') s in

  if z_eq_s && z'_eq_s then (es, stmt c, stmt c')
  else
    let err_stmt, prefix =
      if z_eq_s then (z', "tail of the right") else (z, "head of the left")
    and ppe = EcPrinting.PPEnv.ofenv (FApi.tc1_env tc) in
    tc_error_lazy !!tc (fun fmt ->
        Format.fprintf fmt
          "eager: the %s statement is not of the right form:@\n\
           %a should be@\n\
           %a"
          prefix (EcPrinting.pp_stmt ppe) (stmt err_stmt)
          (EcPrinting.pp_stmt ppe) s)

(** Given a goal environment with a current goal of the shape [s; op ~ op'; s],
    returns the triplet [(es, s, op, op')]. Yields an error if the goal doesn't
    have the right shape *)
let destruct_on_op id_op tc =
  let env = FApi.tc1_env tc and es = tc1_as_equivS tc in
  let s =
    try
      let s, _ = split_at_cpos1 env (-1, `ByMatch (Some (-1), id_op)) es.es_sl
      (* ensure the right statement also contains an [id_op]: *)
      and _, _ = split_at_cpos1 env (1, `ByMatch (None, id_op)) es.es_sr in
      s
    with InvalidCPos ->
      tc_error_lazy !!tc (fun fmt ->
          Format.fprintf fmt "eager: invalid pivot statement")
  in

  if List.is_empty s then
    tc_error_lazy !!tc (fun fmt ->
        Format.fprintf fmt "eager: empty swapping statement");

  let es, c1, c2 = destruct_eager tc (stmt s) in
  match (c1.s_node, c2.s_node) with
  | [ i1 ], [ i2 ] -> (es, stmt s, i1, i2)
  | _, _ ->
      let verb, side =
        if List.length c1.s_node = 1 then ("precede", "right")
        else ("follow", "left")
      in
      tc_error_lazy !!tc (fun fmt ->
          Format.fprintf fmt
            "eager: no statements may %s the %s pivot statement." verb side)

let rec match_eq tc m1 m2 t1 t2 =
  match (t1.f_node, t2.f_node) with
  | Fpvar (p1, m1_), Fpvar (p2, m2_) ->
      ((m1 = m1_ && m2 = m2_) || (m1 = m2_ && m2 = m1_)) && p1 = p2
  | Fglob (p1, m1_), Fglob (p2, m2_) ->
      ((m1 = m1_ && m2 = m2_) || (m1 = m2_ && m2 = m1_)) && p1 = p2
  | Ftuple l1, Ftuple l2 -> List.for_all2 (match_eq tc m1 m2) l1 l2
  | _ -> false

(** Ensure that a given proposition is a conjunction of same-name variables
    equalities between two given memories.

    This test is of course a bit conservative but should be sufficient for all
    the use cases it covers *)
let rec ensure_eq_shape tc m1 m2 q =
  match q.f_node with
  | Fapp (_, [ q1; q2 ]) when is_and q ->
      ensure_eq_shape tc m1 m2 q1 && ensure_eq_shape tc m1 m2 q2
  | Fapp (_, [ t1; t2 ]) when is_eq q -> match_eq tc m1 m2 t1 t2
  | _ -> is_true q

(** Ensure the swapping statement [s] only interacts with global variables. *)
let check_only_global pf env s =
  let sw = s_write env s
  and sr = s_read env s
  and check_mp _ = ()
  and check_glob v _ =
    if is_loc v then
      tc_error_lazy pf (fun fmt ->
          let ppe = EcPrinting.PPEnv.ofenv env in
          Format.fprintf fmt
            "eager: swapping statement may use only global variables: %a"
            (EcPrinting.pp_pv ppe) v)
  in
  PV.iter check_glob check_mp sw;
  PV.iter check_glob check_mp sr

(* -------------------------------------------------------------------- *)
(* Internal variants of eager tactics *)

let t_eager_seq_r (i, j) s (r2, r1) tc =
  let env, _, _ = FApi.tc1_eflat tc and eC, c, c' = destruct_eager tc s in

  let (_, ml_ty), (_, mr_ty) = (eC.es_ml, eC.es_mr) in
  let c1, c2 = s_split env i c and c1', c2' = s_split env j c' in
  let eqMem1 = eq_on_form_and_stmt env r1 (stmt c1')
  and eqQ1 = eq_on_sided_form env (es_po eC) in

  let a =
    f_equivS ml_ty mr_ty (es_pr eC)
      (stmt (s.s_node @ c1))
      (stmt (c1' @ s.s_node))
      r2
  and b =
    f_equivS ml_ty mr_ty r1
      (stmt (s.s_node @ c2))
      (stmt (c2' @ s.s_node))
      (es_po eC)
  and c = f_equivS mr_ty mr_ty eqMem1 (stmt c1') (stmt c1') r1
  and d = f_equivS ml_ty ml_ty r2 (stmt c2) (stmt c2) eqQ1 in
  FApi.xmutate1 tc `EagerSeq [ a; b; c; d ]

(* -------------------------------------------------------------------- *)
let t_eager_if_r tc =
  let es, s, c, c' = destruct_on_op `If tc in
  let e, c1, c2 = destr_if c and e', c1', c2' = destr_if c' in

  let { ml; mr; inv = pr_inv } = es_pr es in
  let { es_ml = _, ml_ty; es_mr = _, mr_ty } = es in

  let fe = (ss_inv_of_expr ml e).inv and fe' = (ss_inv_of_expr mr e').inv in
  let aT =
    f_forall
      [ (ml, GTmem ml_ty); (mr, GTmem mr_ty) ]
      (f_imp pr_inv (f_eq fe fe'))
  in

  let bT =
    let b = EcIdent.create "b" in
    let eqb = f_eq fe (f_local b tbool) in
    let pre = { m = ml; inv = f_and pr_inv eqb } in
    let post = { m = ml; inv = eqb } in
    f_forall [ (mr, GTmem mr_ty); (b, GTty tbool) ] (f_hoareS ml_ty pre s post)
  in

  let cT =
    let pre = { ml; mr; inv = f_and pr_inv (f_eq fe f_true) } in
    let st = stmt (s.s_node @ c1.s_node) in
    let st' = stmt (c1'.s_node @ s.s_node) in
    f_equivS ml_ty mr_ty pre st st' (es_po es)
  in

  let dT =
    let pre = { ml; mr; inv = f_and pr_inv (f_eq fe f_false) } in
    let st = stmt (s.s_node @ c2.s_node) in
    let st' = stmt (c2'.s_node @ s.s_node) in
    f_equivS ml_ty mr_ty pre st st' (es_po es)
  in

  FApi.xmutate1 tc `EagerIf [ aT; bT; cT; dT ]

(* -------------------------------------------------------------------- *)
let t_eager_while_r i tc =
  let env, _, _ = FApi.tc1_eflat tc in

  let es, s, w, w' = destruct_on_op `While tc in
  let e, c = destr_while w and _e, c' = destr_while w' in

  let { ml; mr; inv = pr_inv } = es_pr es in
  let { es_ml = _, ml_ty; es_mr = _, mr_ty } = es in

  let sub_to_left_mem = 
    let open EcSubst in
    subst_expr (add_memory empty mr ml)
  in

  if (not (ER.EqTest.for_expr env e (sub_to_left_mem _e))) then
    tc_error !!tc "eager: both while guards must be syntactically equal";
  
  let eqMem1 = eq_on_form_and_stmt env i c' and eqI = eq_on_sided_form env i in

  let el = ss_inv_of_expr ml e and er = ss_inv_of_expr mr e in

  let aT =
    let and_ = f_and_simpl (f_eq el.inv er.inv) eqI.inv in
    f_forall [ (ml, GTmem ml_ty); (mr, GTmem mr_ty) ] (f_imp i.inv and_)
  and bT =
    let pre = { ml; mr; inv = f_and i.inv el.inv } in
    f_equivS ml_ty mr_ty pre
      (stmt (s.s_node @ c.s_node))
      (stmt (c'.s_node @ s.s_node))
      i
  and cT =
    let b = EcIdent.create "b" in
    let eqb = f_eq el.inv (f_local b tbool) in
    let pre = { m = ml; inv = f_and pr_inv eqb } in
    let post = { m = ml; inv = eqb } in
    f_forall [ (mr, GTmem mr_ty); (b, GTty tbool) ] (f_hoareS ml_ty pre s post)
  and dT = f_equivS ml_ty mr_ty eqMem1 c' c' i
  and eT = f_equivS ml_ty mr_ty i c c i
  and fT =
    f_equivS ml_ty mr_ty { ml; mr; inv = f_and i.inv (f_not el.inv) } s s i
  in

  FApi.xmutate1 tc `EagerWhile [ aT; bT; cT; dT; eT; fT ]

(* -------------------------------------------------------------------- *)
let t_eager_fun_def_r tc =
  let env = FApi.tc1_env tc in
  let eg = tc1_as_eagerF tc in

  let fl, fr = (NormMp.norm_xfun env eg.eg_fl, NormMp.norm_xfun env eg.eg_fr) in

  EcPhlFun.check_concrete !!tc env fl;
  EcPhlFun.check_concrete !!tc env fr;

  let memenvl, (fsigl, fdefl), memenvr, (fsigr, fdefr), env =
    Fun.equivS eg.eg_ml eg.eg_mr fl fr env
  in

  let extend mem fdef =
    match fdef.f_ret with
    | None -> (f_tt, mem, fdef.f_body)
    | Some e ->
        let v = { ov_name = Some "result"; ov_type = e.e_ty } in
        let mem, s = EcMemory.bind_fresh v mem in
        (* oget cannot fail — Some in, Some out *)
        let x = EcTypes.pv_loc (oget s.ov_name) in
        ( (f_pvar x e.e_ty (fst mem)).inv,
          mem,
          s_seq fdef.f_body (stmt [ i_asgn (LvVar (x, e.e_ty), e) ]) )
  in

  let el, meml, sfl = extend memenvl fdefl in
  let er, memr, sfr = extend memenvr fdefr in
  let ml, mr = (EcMemory.memory meml, EcMemory.memory memr) in
  let s = PVM.empty in
  let s = PVM.add env pv_res ml el s in
  let s = PVM.add env pv_res mr er s in
  let post = map_ts_inv1 (PVM.subst env s) (eg_po eg) in
  let s = PVM.empty in
  let s = EcPhlFun.subst_pre env fsigl ml s in
  let s = EcPhlFun.subst_pre env fsigr mr s in
  let pre = map_ts_inv1 (PVM.subst env s) (eg_pr eg) in

  let cond =
    f_equivS (snd meml) (snd memr) pre (s_seq eg.eg_sl sfl) (s_seq sfr eg.eg_sr)
      post
  in

  FApi.xmutate1 tc `EagerFunDef [ cond ]

(* -------------------------------------------------------------------- *)
let t_eager_fun_abs_r i tc =
  let env, _, _ = FApi.tc1_eflat tc and eg = tc1_as_eagerF tc in

  if not (ER.EqTest.for_stmt env eg.eg_sl eg.eg_sr) then
    tc_error !!tc "eager: both swapping statements must be identical";

  if not (ensure_eq_shape tc i.ml i.mr i.inv) then
    tc_error !!tc
      "eager: the invariant must be a conjunction of same-name variable \
       equalities";

  let s, fl, fr = (eg.eg_sl, eg.eg_fl, eg.eg_fr) in

  let pre, post, sg_e = EcPhlFun.FunAbsLow.equivF_abs_spec !!tc env fl fr i in
  let _, _, sg_f = EcPhlFun.FunAbsLow.equivF_abs_spec !!tc env fr fr i in
  let _, _, sg_g = EcPhlFun.FunAbsLow.equivF_abs_spec !!tc env fl fl i in

  let do_e og =
    let ef = destr_equivF og in
    f_eagerF (ef_pr ef) s ef.ef_fl ef.ef_fr s (ef_po ef)
  in

  let do_f og =
    let ef = destr_equivF og in

    let eqMem = eq_on_fun env i.ml i.mr ef.ef_fr in
    f_equivF (map_ts_inv2 f_and eqMem (ef_pr ef)) ef.ef_fl ef.ef_fl (ef_po ef)
  in

  let sg_e = List.map do_e sg_e and sg_f = List.map do_f sg_f in

  (* Reorder per-oracle goals in order to align with the description *)
  let sg =
    List.combine sg_e (List.combine sg_f sg_g)
    |> List.concat_map (fun (x, (y, z)) -> [ x; y; z ])
  and sg_d = f_equivS EcMemory.abstract_mt EcMemory.abstract_mt i s s i in

  let tactic tc = FApi.xmutate1 tc `EagerFunAbs (sg_d :: sg) in

  FApi.t_last tactic (EcPhlConseq.t_eagerF_conseq pre post tc)

(* -------------------------------------------------------------------- *)
let t_eager_call_r fpre fpost tc =
  let env, hyps, _ = FApi.tc1_eflat tc in
  let es = tc1_as_equivS tc in
  let fpre = EcSubst.ts_inv_rebind fpre (fst es.es_ml) (fst es.es_mr) in
  let fpost = EcSubst.ts_inv_rebind fpost (fst es.es_ml) (fst es.es_mr) in

  let (lvl, fl, argsl), sl = pf_last_call !!tc es.es_sl in
  let (lvr, fr, argsr), sr = pf_first_call !!tc es.es_sr in

  let swl = s_write env sl in
  let swr = s_write env sr in

  let check_a e =
    let er = e_read env e in
    let diff = PV.interdep env swl er in

    if not (PV.is_empty diff) then
      tc_error_lazy !!tc (fun fmt ->
          Format.fprintf fmt "eager: swapping statement may not write to `%a`"
            (PV.pp env) diff)
  in

  List.iter check_a argsl;

  let modil = PV.union (f_write env fl) swl in
  let modir = PV.union (f_write env fr) swr in
  let post =
    EcPhlCall.wp2_call env fpre fpost (lvl, fl, argsl) modil (lvr, fr, argsr)
      modir (es_po es) hyps
  in
  let f_concl = f_eagerF fpre sl fl fr sr fpost in
  let concl =
    f_equivS (snd es.es_ml) (snd es.es_mr) (es_pr es) (stmt []) (stmt []) post
  in

  FApi.xmutate1 tc `EagerCall [ f_concl; concl ]

(* -------------------------------------------------------------------- *)
let t_eager_seq = FApi.t_low3 "eager-seq" t_eager_seq_r
let t_eager_if = FApi.t_low0 "eager-if" t_eager_if_r
let t_eager_while = FApi.t_low1 "eager-while" t_eager_while_r
let t_eager_fun_def = FApi.t_low0 "eager-fun-def" t_eager_fun_def_r
let t_eager_fun_abs = FApi.t_low1 "eager-fun-abs" t_eager_fun_abs_r
let t_eager_call = FApi.t_low2 "eager-call" t_eager_call_r

(* -------------------------------------------------------------------- *)
let process_seq (i, j) s factor tc =
  let open BatTuple.Tuple2 in
  let indices =
    mapn (tc1_process_codepos1 tc) ((Some `Left, i), (Some `Right, j))
  and factor =
    factor
    |> ( function Single p -> (p, p) | Double pp -> pp )
    |> mapn (TTC.tc1_process_prhl_form tc tbool)
  and s = TTC.tc1_process_prhl_stmt tc `Left s in

  t_eager_seq indices s factor tc

let process_if = t_eager_if

let process_while inv tc =
  (* This is performed here only to recover [e{1}] and setup
     the consequence rule accordingly. *)
  let es, _, w, _ = destruct_on_op `While tc in
  let e, _ = destr_while w in
  let e1 = ss_inv_of_expr (fst es.es_ml) e in

  let inv = TTC.tc1_process_prhl_form tc tbool inv in
  (EcPhlConseq.t_equivS_conseq inv
     { inv with inv = f_and inv.inv (f_not e1.inv) }
  @+ [ t_trivial; t_trivial; t_eager_while inv ])
    tc

let process_fun_def tc = t_eager_fun_def tc

let process_fun_abs inv tc =
  let hyps = FApi.tc1_hyps tc in
  let { eg_ml = ml; eg_mr = mr } = tc1_as_eagerF tc in
  let env = LDecl.inv_memenv ml mr hyps in
  let inv = TTC.pf_process_formula !!tc env inv in
  t_eager_fun_abs { ml; mr; inv } tc

let process_call info tc =
  let process_cut' fpre fpost =
    let env, hyps, _ = FApi.tc1_eflat tc in
    let es = tc1_as_equivS tc in

    let (_, fl, _), sl = tc1_last_call tc es.es_sl in
    let (_, fr, _), sr = tc1_first_call tc es.es_sr in

    check_only_global !!tc env sl;
    check_only_global !!tc env sr;

    let ml, mr = (fst es.es_ml, fst es.es_mr) in
    let penv, qenv = LDecl.equivF ml mr fl fr hyps in
    let fpre = TTC.pf_process_formula !!tc penv fpre in
    let fpost = TTC.pf_process_formula !!tc qenv fpost in
    f_eagerF { ml; mr; inv = fpre } sl fl fr sr { ml; mr; inv = fpost }
  in
  let process_cut = function
    | EcParsetree.CI_spec (fpre, fpost) -> process_cut' fpre fpost
    | CI_inv inv -> process_cut' inv inv
    | _ -> tc_error !!tc "eager: invalid call specification"
  in

  let pt, ax =
    PT.tc1_process_full_closed_pterm_cut ~prcut:process_cut tc info
  in
  let eg = pf_as_eagerF !!tc ax in

  FApi.t_on1seq 0
    (t_eager_call (eg_pr eg) (eg_po eg))
    (EcLowGoal.Apply.t_apply_bwd_hi ~dpe:true pt)
    tc
