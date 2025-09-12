(* -------------------------------------------------------------------- *)
open EcUtils
open EcAst
open EcFol
open EcEnv

open EcCoreGoal
open EcLowGoal

module Mid = EcIdent.Mid

(* -------------------------------------------------------------------- *)
let t_pr_lemma lemma tc =
  let concl = FApi.tc1_goal tc in
  assert (f_equal concl lemma);
  FApi.xmutate1 tc `RwPr []

(* -------------------------------------------------------------------- *)
let pr_eq env m f args p1 p2 =
  let mem = Fun.prF_memenv mhr f env in
  let hyp = f_forall_mems [ mem ] (f_iff p1 p2) in
  let concl = f_eq (f_pr m f args p1) (f_pr m f args p2) in
  f_imp hyp (f_eq concl f_true)

let pr_sub env m f args p1 p2 =
  let mem = Fun.prF_memenv mhr f env in
  let hyp = f_forall_mems [ mem ] (f_imp p1 p2) in
  let concl = f_real_le (f_pr m f args p1) (f_pr m f args p2) in
  f_imp hyp (f_eq concl f_true)

let pr_false m f args = f_eq (f_pr m f args f_false) f_r0

let pr_not m f args p =
  f_eq
    (f_pr m f args (f_not p))
    (f_real_sub (f_pr m f args f_true) (f_pr m f args p))

let pr_or m f args por p1 p2 =
  let pr1 = f_pr m f args p1 in
  let pr2 = f_pr m f args p2 in
  let pr12 = f_pr m f args (f_and p1 p2) in
  let pr = f_real_sub (f_real_add pr1 pr2) pr12 in
  f_eq (f_pr m f args (por p1 p2)) pr

let pr_disjoint env m f args por p1 p2 =
  let mem = Fun.prF_memenv mhr f env in
  let hyp = f_forall_mems [ mem ] (f_not (f_and p1 p2)) in
  let pr1 = f_pr m f args p1 in
  let pr2 = f_pr m f args p2 in
  let pr = f_real_add pr1 pr2 in
  f_imp hyp (f_eq (f_pr m f args (por p1 p2)) pr)

let pr_split m f args ev1 ev2 =
  let pr = f_pr m f args ev1 in
  let pr1 = f_pr m f args (f_and ev1 ev2) in
  let pr2 = f_pr m f args (f_and ev1 (f_not ev2)) in
  f_eq pr (f_real_add pr1 pr2)

let pr_ge0 m f args ev =
  let pr = f_pr m f args ev in
  f_eq (f_real_le f_r0 pr) f_true

let pr_le1 m f args ev =
  let pr = f_pr m f args ev in
  f_eq (f_real_le pr f_r1) f_true

let pr_sum env pr =
  let prf = EcEnv.Fun.by_xpath pr.pr_fun env in
  let xty = prf.f_sig.fs_ret in
  let x = EcIdent.create "x" in
  let fx = f_local x xty in

  let prx =
    let event =
      f_and_simpl pr.pr_event (f_eq (f_pvar EcTypes.pv_res xty EcFol.mhr) fx)
    in
    f_pr pr.pr_mem pr.pr_fun pr.pr_args event
  in

  let prx =
    EcFol.f_app
      (EcFol.f_op EcCoreLib.CI_Sum.p_sum [ xty ]
         (EcTypes.tfun (EcTypes.tfun xty EcTypes.treal) EcTypes.treal))
      [ EcFol.f_lambda [ (x, GTty xty) ] prx ]
      EcTypes.treal
  in

  f_eq (f_pr_r pr) prx

let pr_mu1_le_eq_mu1 m f args resv k fresh_id d =
  let kfresh = f_local fresh_id k.f_ty in
  let f_ll = f_bdHoareF f_true f f_true FHeq f_r1
  and f_le_mu1 = f_forall [ (fresh_id, gtty k.f_ty) ]
    (f_real_le (f_pr m f args (f_eq resv kfresh)) (f_mu_x d kfresh))
  and concl =
    f_eq (f_pr m f args (f_eq resv k)) (f_mu_x d k) in
  f_imp f_ll (f_imp f_le_mu1 concl)

let p_List = [EcCoreLib.i_top; "List"]
let p_BRA  = [EcCoreLib.i_top; "StdBigop"; "Bigreal"; "BRA"]
let p_list_has = EcPath.fromqsymbol (p_List, "has")
let p_BRA_big = EcPath.fromqsymbol (p_BRA, "big")

let destr_pr_has pr =
  match pr.pr_event.f_node with
  | Fapp ({ f_node = Fop(op, [ty_elem]) }, [f_f; f_l]) ->
      if EcPath.p_equal p_list_has op then
        Some(ty_elem, f_f, f_l)
      else None
  | _ -> None
(*
 lemma mu_has_le ['a 'b] (P : 'a -> 'b -> bool) (d : 'a distr) (s : 'b list) :
   mu d (fun a => has (P a) s) <= BRA.big predT (fun b => mu d (fun a => P a b)) s.
   Pr [f(args)@ &m : has P s] <= BRA.big predT (fun b => Pr [f(args) &m : P b])
*)
let pr_has_le f_pr =
  let pr = destr_pr f_pr in
  let ty_elem, f_f, f_l = oget (destr_pr_has pr) in
  let idx = EcIdent.create "x" in
  let x = f_local idx ty_elem in
  let pr_event = f_app f_f [x] EcTypes.tbool in
  let f_pr1 = f_pr_r {pr with pr_event} in
  let f_fsum = f_lambda [idx, GTty ty_elem] f_pr1 in
  let f_sum =
    f_app (f_op p_BRA_big [ty_elem] EcTypes.treal) [f_predT ty_elem; f_fsum; f_l] EcTypes.treal in
  f_real_le f_pr f_sum

(* -------------------------------------------------------------------- *)
exception FoundPr of form

let select_pr on_ev sid f =
  match f.f_node with
  | Fpr { pr_event = ev } ->
      if on_ev ev && Mid.set_disjoint f.f_fv sid then raise (FoundPr f)
      else false
  | _ -> false

let select_pr_cmp on_cmp sid f =
  match f.f_node with
  | Fapp
      ({ f_node = Fop (op, _) }, [ { f_node = Fpr pr1 }; { f_node = Fpr pr2 } ])
    ->
      if on_cmp op
        && EcIdent.id_equal pr1.pr_mem pr2.pr_mem
        && EcPath.x_equal pr1.pr_fun pr2.pr_fun
        && f_equal pr1.pr_args pr2.pr_args
        && Mid.set_disjoint f.f_fv sid
      then raise (FoundPr f)
      else false
  | _ -> false

let select_pr_ge0 sid f =
  match f.f_node with
  | Fapp ({ f_node = Fop (op, _) }, [ f'; { f_node = Fpr _ } ]) ->
      if EcPath.p_equal EcCoreLib.CI_Real.p_real_le op
        && f_equal f' f_r0
        && Mid.set_disjoint f.f_fv sid
      then raise (FoundPr f)
      else false
  | _ -> false

let select_pr_le1 sid f =
  match f.f_node with
  | Fapp ({ f_node = Fop (op, _) }, [ { f_node = Fpr _ }; f' ]) ->
      if EcPath.p_equal EcCoreLib.CI_Real.p_real_le op
        && f_equal f' f_r1
        && Mid.set_disjoint f.f_fv sid
      then raise (FoundPr f)
      else false
  | _ -> false

let select_pr_muhasle sid f =
  match f.f_node with
  | Fapp ({ f_node = Fop (op, _) }, [ { f_node = Fpr pr } as f_pr; _ ]) ->
      if EcPath.p_equal EcCoreLib.CI_Real.p_real_le op then
        match destr_pr_has pr with
        | Some (_, _, f_l) when
          Mid.set_disjoint f_l.f_fv (Mid.add EcCoreFol.mhr () sid) ->
            raise (FoundPr f_pr)
        | _ -> false
      else false
  | _ -> false

(* -------------------------------------------------------------------- *)
let pr_rewrite_lemma =
  [
    ("mu1_le_eq_mu1", `Mu1LeEqMu1);
    ("muE", `MuSum);
    ("mu_disjoint", `MuDisj);
    ("mu_eq", `MuEq);
    ("mu_false", `MuFalse);
    ("mu_ge0", `MuGe0);
    ("mu_le1", `MuLe1);
    ("mu_not", `MuNot);
    ("mu_or", `MuOr);
    ("mu_split", `MuSplit);
    ("mu_sub", `MuSub);
    ("mu_has_le", `MuHasLe)
  ]

(* -------------------------------------------------------------------- *)
let t_pr_rewrite_low (s, dof) tc =
  let kind =
    try List.assoc s pr_rewrite_lemma
    with Not_found ->
      tc_error !!tc "Pr-rewrite: `%s` is not a suitable probability lemma" s
  in

  let expect_arg = function `MuSplit | `Mu1LeEqMu1 -> true | _ -> false in
  (if not (is_some dof = expect_arg kind) then
     let neg = if is_some dof then "no " else "" in
     tc_error !!tc "Pr-rewrite: %sargument expected for `%s`" neg s);

  let select =
    match kind with
    | `Mu1LeEqMu1 -> select_pr is_eq
    | `MuDisj | `MuOr -> select_pr is_or
    | `MuEq -> select_pr_cmp (EcPath.p_equal EcCoreLib.CI_Bool.p_eq)
    | `MuFalse -> select_pr is_false
    | `MuGe0 -> select_pr_ge0
    | `MuLe1 -> select_pr_le1
    | `MuNot -> select_pr is_not
    | `MuSplit -> select_pr (fun _ev -> true)
    | `MuSub -> select_pr_cmp (EcPath.p_equal EcCoreLib.CI_Real.p_real_le)
    | `MuSum -> select_pr (fun _ev -> true)
    | `MuHasLe -> select_pr_muhasle
  in

  let select xs fp = if select xs fp then `Accept (-1) else `Continue in
  let env, hyps, concl = FApi.tc1_eflat tc in
  let torw =
    try
      ignore (EcMatching.FPosition.select select concl);
      tc_error !!tc "Pr-rewrite: cannot find a pattern for `%s`" s
    with FoundPr f -> f in

  let lemma, args =
    match kind with
    | `Mu1LeEqMu1 ->
      let { pr_mem; pr_fun; pr_args; pr_event } = destr_pr torw in
      let (resv, k) = destr_eq pr_event in
      let k_id = EcEnv.LDecl.fresh_id hyps "k" in
      let d = (oget dof) tc torw (EcTypes.tdistr k.f_ty) in
      (pr_mu1_le_eq_mu1 pr_mem pr_fun pr_args resv k k_id d, 2)

    | (`MuEq | `MuSub as kind) -> begin
      match torw.f_node with
      | Fapp(_, [{f_node = Fpr ({ pr_event = ev1 } as pr) };
                 {f_node = Fpr ({ pr_event = ev2 }) };])
        -> begin
          let { pr_mem = m; pr_fun = f; pr_args = args } = pr in
          match kind with
          | `MuEq  -> (pr_eq  env m f args ev1 ev2, 1)
          | `MuSub -> (pr_sub env m f args ev1 ev2, 1)
        end
      | _ -> assert false
      end

    | `MuFalse ->
        let { pr_mem = m ; pr_fun = f; pr_args = args } = destr_pr torw in
        (pr_false m f args, 0)

    | `MuNot ->
        let { pr_mem = m ; pr_fun = f; pr_args = args; } as pr = destr_pr torw in
        let ev = destr_not pr.pr_event in
        (pr_not m f args ev, 0)

    | `MuOr ->
        let { pr_mem = m ; pr_fun = f; pr_args = args; } as pr = destr_pr torw in
        let (asym, (ev1, ev2)) = destr_or_r pr.pr_event in
        (pr_or m f args (match asym with | `Asym -> f_ora | `Sym -> f_or) ev1 ev2, 0)

    | `MuDisj ->
        let { pr_mem = m ; pr_fun = f; pr_args = args; } as pr = destr_pr torw in
        let (asym, (ev1, ev2)) = destr_or_r pr.pr_event in
        (pr_disjoint env m f args (match asym with | `Asym -> f_ora | `Sym -> f_or) ev1 ev2, 1)

    | `MuSplit ->
      let pr = destr_pr torw in
      let ev' = (oget dof) tc torw EcTypes.tbool in
      (pr_split pr.pr_mem pr.pr_fun pr.pr_args pr.pr_event ev', 0)

    | `MuGe0 -> begin
      match torw.f_node with
      | Fapp({f_node = Fop _}, [_; {f_node = Fpr pr}]) ->
            let { pr_mem = m; pr_fun = f; pr_args = args; pr_event = ev } = pr in
            (pr_ge0 m f args ev, 0)
      | _ -> assert false
      end

    | `MuLe1 -> begin
      match torw.f_node with
      | Fapp({f_node = Fop _}, [{f_node = Fpr pr}; _]) ->
            let { pr_mem = m; pr_fun = f; pr_args = args; pr_event = ev } = pr in
            (pr_le1 m f args ev, 0)
      | _ -> assert false
      end

    | `MuSum ->
        (pr_sum env (destr_pr torw), 0)

    | `MuHasLe ->
        (pr_has_le torw, 0)

  in

  let rwpt = EcCoreGoal.ptcut ~args:(List.make args (PASub None)) lemma in

  FApi.t_first
    (t_pr_lemma lemma)
    (t_rewrite rwpt (`LtoR, None) tc)

let t_pr_rewrite_i (s, f) tc =
  let do_ev = omap (fun f _ _ _ -> f) f in
  t_pr_rewrite_low (s, do_ev) tc

let t_pr_rewrite (s, f) tc =
  let to_env f tc torw ty =
    let env, hyps, _ = FApi.tc1_eflat tc in
    let pr = destr_pr torw in
    let mp = EcEnv.Fun.prF_memenv EcFol.mhr pr.pr_fun env in
    let hyps = LDecl.push_active mp hyps in
    EcProofTyping.process_form hyps f ty
  in
  t_pr_rewrite_low (s, omap to_env f) tc
