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
    between two memories [m1] and [m2] *)
let list_eq_to_form m1 m2 (l, l_glob) =
  let to_form m = List.map (fun (pv, ty) -> f_pvar pv ty m) in
  let to_form_glob m = List.map (fun x -> f_glob (EcPath.mget_ident x) m) in
  f_eqs
    (to_form m1 l @ to_form_glob m1 l_glob)
    (to_form m2 l @ to_form_glob m2 l_glob)

(** Returns a formula that describes equality on all variables from one side of
    the memory present in the formula [q].

    Example: If [q] is [(a{m1} \/ b{m3} /\ c{m1})], (with [m1] the first
    argument, [m2] the second and [m3] another memory, distinct from [m1]) then
    this function returns [(a{m1} = a{m2} /\ c{m1} = c{m2})]. The result of this
    operation is sometimes denoted [={q.m1}]. *)
let eq_on_sided_form env m1 m2 q =
  PV.fv env m1 q |> PV.elements |> list_eq_to_form m1 m2

(** Returns a formula that describes equality on all variables from both
    memories in predicate [q], as well as equality on all variables read from
    [c].

    This is used to implement what is denoted [Eq] in the module documentation,
    i.e. equality on the whole memory. *)
let eq_on_form_and_stmt env m1 m2 q c =
  s_read env c
  |> PV.union (PV.fv env m1 q)
  |> PV.union (PV.fv env m2 q)
  |> PV.elements |> list_eq_to_form m1 m2

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
      let s, _ = split_at_cpos1 env (-1, `ByMatch (None, id_op)) es.es_sl
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

  let m1 = fst eC.es_ml
  and m2 = fst eC.es_mr
  and c1, c2 = s_split env i c
  and c1', c2' = s_split env j c' in
  let eqMem1 = eq_on_form_and_stmt env m1 m2 r1 (stmt c1')
  and eqQ1 = eq_on_sided_form env m1 m2 eC.es_po in

  let a =
    f_equivS_r
      {
        eC with
        es_sl = stmt (s.s_node @ c1);
        es_sr = stmt (c1' @ s.s_node);
        es_po = r2;
      }
  and b =
    f_equivS_r
      {
        eC with
        es_pr = r1;
        es_sl = stmt (s.s_node @ c2);
        es_sr = stmt (c2' @ s.s_node);
      }
  and c =
    f_equivS_r
      {
        eC with
        es_ml = (fst eC.es_ml, snd eC.es_mr);
        es_pr = eqMem1;
        es_sl = stmt c1';
        es_sr = stmt c1';
        es_po = r1;
      }
  and d =
    f_equivS_r
      {
        eC with
        es_mr = (fst eC.es_mr, snd eC.es_ml);
        es_pr = r2;
        es_sl = stmt c2;
        es_sr = stmt c2;
        es_po = eqQ1;
      }
  in
  FApi.xmutate1 tc `EagerSeq [ a; b; c; d ]

(* -------------------------------------------------------------------- *)
let t_eager_if_r tc =
  let hyps = FApi.tc1_hyps tc and es, s, c, c' = destruct_on_op `If tc in
  let e, c1, c2 = destr_if c and e', c1', c2' = destr_if c' in

  let fel = form_of_expr (fst es.es_ml) e in
  let fer = form_of_expr (fst es.es_mr) e' in
  let fe = form_of_expr mhr e in

  let m2 = as_seq1 (LDecl.fresh_ids hyps [ "&m2" ]) in

  let aT =
    f_forall
      [ (mleft, GTmem (snd es.es_ml)); (mright, GTmem (snd es.es_mr)) ]
      (f_imp es.es_pr (f_eq fel fer))
  in

  let bT =
    let bind m1 m2 s = Fsubst.f_bind_mem s m1 m2 and b = EcIdent.create "b1" in
    let eqb = f_eq fe (f_local b tbool)
    and p =
      Fsubst.f_subst_id |> bind mleft mhr |> bind mright m2 |> fun s ->
      Fsubst.f_subst s es.es_pr
    in

    f_forall
      [ (m2, GTmem (snd es.es_mr)); (b, GTty tbool) ]
      (f_hoareS (mhr, snd es.es_ml) (f_and p eqb) s eqb)
  in

  let cT =
    let pre = f_and es.es_pr (f_eq fel f_true) in
    let st = stmt (s.s_node @ c1.s_node) in
    let st' = stmt (c1'.s_node @ s.s_node) in
    f_equivS es.es_ml es.es_mr pre st st' es.es_po
  in

  let dT =
    let pre = f_and es.es_pr (f_eq fel f_false) in
    let st = stmt (s.s_node @ c2.s_node) in
    let st' = stmt (c2'.s_node @ s.s_node) in
    f_equivS es.es_ml es.es_mr pre st st' es.es_po
  in

  FApi.xmutate1 tc `EagerIf [ aT; bT; cT; dT ]

(* -------------------------------------------------------------------- *)
let t_eager_while_r i tc =
  let env, hyps, _ = FApi.tc1_eflat tc in

  let es, s, w, w' = destruct_on_op `While tc in
  let e, c = destr_while w and e', c' = destr_while w' in

  let m1 = fst es.es_ml and m2 = fst es.es_mr in
  let eqMem1 = eq_on_form_and_stmt env m1 m2 i c'
  and eqI = eq_on_sided_form env m1 m2 i in

  let e1 = form_of_expr (fst es.es_ml) e in
  let e2 = form_of_expr (fst es.es_mr) e' in
  let fe = form_of_expr mhr e in

  let m2 = as_seq1 (LDecl.fresh_ids hyps [ "&m2" ]) in

  let aT =
    f_forall
      [ (mleft, GTmem (snd es.es_ml)); (mright, GTmem (snd es.es_mr)) ]
      (f_imp i (f_eq e1 e2))
  and bT =
    f_equivS_r
      {
        es with
        es_pr = f_and_simpl i e1;
        es_sl = stmt (s.s_node @ c.s_node);
        es_sr = stmt (c'.s_node @ s.s_node);
        es_po = i;
      }
  and cT =
    let bind m1 m2 s = Fsubst.f_bind_mem s m1 m2 and b = EcIdent.create "b1" in
    let eqb = f_eq fe (f_local b tbool)
    and p =
      Fsubst.f_subst_id |> bind mleft mhr |> bind mright m2 |> fun s ->
      Fsubst.f_subst s es.es_pr
    in
    f_forall
      [ (m2, GTmem (snd es.es_mr)); (b, GTty tbool) ]
      (f_hoareS (mhr, snd es.es_ml) (f_and p eqb) s eqb)
  and dT =
    f_equivS_r { es with es_pr = eqMem1; es_sl = c'; es_sr = c'; es_po = i }
  and eT = f_equivS_r { es with es_pr = i; es_sl = c; es_sr = c; es_po = eqI }
  and fT =
    f_equivS_r
      { es with es_pr = f_and i (f_not e1); es_sl = s; es_sr = s; es_po = i }
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
    Fun.equivS fl fr env
  in

  let extend mem fdef =
    match fdef.f_ret with
    | None -> (f_tt, mem, fdef.f_body)
    | Some e ->
        let v = { ov_name = Some "result"; ov_type = e.e_ty } in
        let mem, s = EcMemory.bind_fresh v mem in
        (* oget cannot fail — Some in, Some out *)
        let x = EcTypes.pv_loc (oget s.ov_name) in
        ( f_pvar x e.e_ty (fst mem),
          mem,
          s_seq fdef.f_body (stmt [ i_asgn (LvVar (x, e.e_ty), e) ]) )
  in

  let el, meml, sfl = extend memenvl fdefl in
  let er, memr, sfr = extend memenvr fdefr in
  let ml, mr = (EcMemory.memory meml, EcMemory.memory memr) in
  let s = PVM.empty in
  let s = PVM.add env pv_res ml el s in
  let s = PVM.add env pv_res mr er s in
  let post = PVM.subst env s eg.eg_po in
  let s = PVM.empty in
  let s = EcPhlFun.subst_pre env fsigl ml s in
  let s = EcPhlFun.subst_pre env fsigr mr s in
  let pre = PVM.subst env s eg.eg_pr in

  let cond =
    f_equivS_r
      {
        es_ml = meml;
        es_mr = memr;
        es_sl = s_seq eg.eg_sl sfl;
        es_sr = s_seq sfr eg.eg_sr;
        es_pr = pre;
        es_po = post;
      }
  in

  FApi.xmutate1 tc `EagerFunDef [ cond ]

(* -------------------------------------------------------------------- *)
let t_eager_fun_abs_r i tc =
  let env, _, _ = FApi.tc1_eflat tc
  and eg = tc1_as_eagerF tc
  and mleft' = EcMemory.abstract mleft
  and mright' = EcMemory.abstract mright in

  if not (s_equal eg.eg_sl eg.eg_sr) then
    tc_error !!tc "eager: both swapping statements must be identical";

  if not (ensure_eq_shape tc mleft mright i) then
    tc_error !!tc
      "eager: the invariant must be a conjunction of same-name variable \
       equalities";

  let s, fl, fr = (eg.eg_sl, eg.eg_fl, eg.eg_fr) in

  let pre, post, sg_e = EcPhlFun.FunAbsLow.equivF_abs_spec !!tc env fl fr i in
  let _, _, sg_f = EcPhlFun.FunAbsLow.equivF_abs_spec !!tc env fr fr i in
  let _, _, sg_g = EcPhlFun.FunAbsLow.equivF_abs_spec !!tc env fl fl i in

  let do_e og =
    let ef = destr_equivF og in
    f_eagerF ef.ef_pr s ef.ef_fl ef.ef_fr s ef.ef_po
  in

  let do_f og =
    let ef = destr_equivF og in
    let eqMem = eq_on_fun env mleft mright ef.ef_fr in
    f_equivF (f_and eqMem ef.ef_pr) ef.ef_fl ef.ef_fl ef.ef_po
  in

  let sg_e = List.map do_e sg_e and sg_f = List.map do_f sg_f in

  (* Reorder per-oracle goals in order to align with the description *)
  let sg =
    List.combine sg_e (List.combine sg_f sg_g)
    |> List.concat_map (fun (x, (y, z)) -> [ x; y; z ])
  and sg_d = f_equivS mleft' mright' i s s i in

  let tactic tc = FApi.xmutate1 tc `EagerFunAbs (sg_d :: sg) in

  FApi.t_last tactic (EcPhlConseq.t_eagerF_conseq pre post tc)

(* -------------------------------------------------------------------- *)
let t_eager_call_r fpre fpost tc =
  let env, hyps, _ = FApi.tc1_eflat tc in
  let es = tc1_as_equivS tc in

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

  let ml = EcMemory.memory es.es_ml in
  let mr = EcMemory.memory es.es_mr in
  let modil = PV.union (f_write env fl) swl in
  let modir = PV.union (f_write env fr) swr in
  let post =
    EcPhlCall.wp2_call env fpre fpost (lvl, fl, argsl) modil (lvr, fr, argsr)
      modir ml mr es.es_po hyps
  in
  let f_concl = f_eagerF fpre sl fl fr sr fpost in
  let concl =
    f_equivS_r { es with es_sl = stmt []; es_sr = stmt []; es_po = post }
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
  let mem_ty = FApi.tc1_goal tc |> destr_equivS |> fun x -> x.es_mr |> snd in
  let indices =
    mapn (TTC.tc1_process_codepos1 tc) ((Some `Left, i), (Some `Right, j))
  and factor =
    factor
    |> ( function Single p -> (p, p) | Double pp -> pp )
    |> mapn (TTC.tc1_process_prhl_form tc tbool)
  and s = TTC.tc1_process_stmt tc mem_ty s in

  t_eager_seq indices s factor tc

let process_if = t_eager_if

let process_while inv tc =
  (* This is performed here only to recover [e{1}] and setup
     the consequence rule accordingly. *)
  let es, _, w, _ = destruct_on_op `While tc in
  let e, _ = destr_while w in
  let e1 = form_of_expr (fst es.es_ml) e in

  let inv = TTC.tc1_process_prhl_form tc tbool inv in
  (EcPhlConseq.t_equivS_conseq inv (f_and inv (f_not e1))
  @+ [ t_trivial; t_trivial; t_eager_while inv ])
    tc

let process_fun_def tc = t_eager_fun_def tc

let process_fun_abs i tc =
  let mleft, mright = (Fun.inv_memory `Left, Fun.inv_memory `Right) in
  let hyps = LDecl.push_all [ mleft; mright ] (FApi.tc1_hyps tc) in
  let i = TTC.pf_process_formula !!tc hyps i in
  t_eager_fun_abs i tc

let process_call info tc =
  let process_cut' fpre fpost =
    let env, hyps, _ = FApi.tc1_eflat tc in
    let es = tc1_as_equivS tc in

    let (_, fl, _), sl = tc1_last_call tc es.es_sl in
    let (_, fr, _), sr = tc1_first_call tc es.es_sr in

    check_only_global !!tc env sl;
    check_only_global !!tc env sr;

    let penv, qenv = LDecl.equivF fl fr hyps in
    let fpre = TTC.pf_process_form !!tc penv tbool fpre in
    let fpost = TTC.pf_process_form !!tc qenv tbool fpost in
    f_eagerF fpre sl fl fr sr fpost
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
    (t_eager_call eg.eg_pr eg.eg_po)
    (EcLowGoal.Apply.t_apply_bwd_hi ~dpe:true pt)
    tc
