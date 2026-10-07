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
let pr_eq env pr_m f args p1 p2 =
  let m = p1.m in
  let mem = Fun.prF_memenv m f env in
  let hyp = EcSubst.f_forall_mems_ss_inv mem (map_ss_inv2 f_iff p1 p2) in
  let concl = f_eq (f_pr pr_m f args p1) (f_pr pr_m f args p2) in
  f_imp hyp (f_eq concl f_true)

let pr_sub env pr_m f args p1 p2 =
  let m = p1.m in
  let mem = Fun.prF_memenv m f env in
  let hyp = EcSubst.f_forall_mems_ss_inv mem (map_ss_inv2 f_imp p1 p2) in
  let concl = f_real_le (f_pr pr_m f args p1) (f_pr pr_m f args p2) in
  f_imp hyp (f_eq concl f_true)

let pr_false pr_m f args = 
  let m = EcIdent.create "&hr" in
  f_eq (f_pr pr_m f args {m;inv=f_false}) f_r0

let pr_not pr_m f args p =
  let m = p.m in
  f_eq
    (f_pr pr_m f args (map_ss_inv1 f_not p))
    (f_real_sub (f_pr pr_m f args {m;inv=f_true}) (f_pr pr_m f args p))

let pr_or pr_m f args por p1 p2 =
  let pr1 = f_pr pr_m f args p1 in
  let pr2 = f_pr pr_m f args p2 in
  let pr12 = f_pr pr_m f args (map_ss_inv2 f_and p1 p2) in
  let pr = f_real_sub (f_real_add pr1 pr2) pr12 in
  f_eq (f_pr pr_m f args (por p1 p2)) pr

let pr_disjoint env pr_m f args por p1 p2 =
  let m = p1.m in
  let mem = Fun.prF_memenv m f env in
  let hyp = EcSubst.f_forall_mems_ss_inv mem (map_ss_inv1 f_not (map_ss_inv2 f_and p1 p2)) in
  let pr1 = f_pr pr_m f args p1 in
  let pr2 = f_pr pr_m f args p2 in
  let pr = f_real_add pr1 pr2 in
  f_imp hyp (f_eq (f_pr pr_m f args (por p1 p2)) pr)

let pr_split pr_m f args ev1 ev2 =
  let pr = f_pr pr_m f args ev1 in
  let pr1 = f_pr pr_m f args (map_ss_inv2 f_and ev1 ev2) in
  let pr2 = f_pr pr_m f args (map_ss_inv2 f_and ev1 (map_ss_inv1 f_not ev2)) in
  f_eq pr (f_real_add pr1 pr2)

let pr_ge0 pr_m f args ev =
  let pr = f_pr pr_m f args ev in
  f_eq (f_real_le f_r0 pr) f_true

let pr_le1 pr_m f args ev =
  let pr = f_pr pr_m f args ev in
  f_eq (f_real_le pr f_r1) f_true

let pr_sum env pr =
  let prf = EcEnv.Fun.by_xpath pr.pr_fun env in
  let xty = prf.f_sig.fs_ret in
  let x = EcIdent.create "x" in
  let ev = pr.pr_event in
  let m = ev.m in
  let fx = {m;inv=f_local x xty} in
  let prx =
    let event =
      map_ss_inv2 f_and_simpl
        ev
        (map_ss_inv2 f_eq (f_pvar EcTypes.pv_res xty ev.m) fx)
    in f_pr pr.pr_mem pr.pr_fun pr.pr_args event in

  let prx =
    EcFol.f_app
      (EcFol.f_op EcCoreLib.CI_Sum.p_sum [ xty ]
         (EcTypes.tfun (EcTypes.tfun xty EcTypes.treal) EcTypes.treal))
      [ EcFol.f_lambda [ (x, GTty xty) ] prx ]
      EcTypes.treal
  in

  f_eq (f_pr_r pr) prx

let pr_mu1_le_eq_mu1 pr_m f args resv k fresh_id d =
  let m = resv.m in
  let kfresh = f_local fresh_id k.f_ty in
  let f_ll = f_bdHoareF {m;inv=f_true} f {m;inv=f_true} FHeq {m;inv=f_r1}
  and f_le_mu1 = f_forall [ (fresh_id, gtty k.f_ty) ]
    (f_real_le (f_pr pr_m f args {m;inv=f_eq resv.inv kfresh}) (f_mu_x d kfresh))
  and concl =
    f_eq (f_pr pr_m f args {m;inv=f_eq resv.inv k}) (f_mu_x d k) in
  f_imp f_ll (f_imp f_le_mu1 concl)

let p_List = [EcCoreLib.i_top; "List"]
let p_BRA  = [EcCoreLib.i_top; "StdBigop"; "Bigreal"; "BRA"]
let p_list_has = EcPath.fromqsymbol (p_List, "has")
let p_BRA_big = EcPath.fromqsymbol (p_BRA, "big")
let p_Logic = [EcCoreLib.i_top; "Logic"]
let p_pred0 = EcPath.fromqsymbol (p_Logic, "pred0")
let p_predI = EcPath.fromqsymbol (p_Logic, "predI")
let p_predU = EcPath.fromqsymbol (p_Logic, "predU")
let p_predC = EcPath.fromqsymbol (p_Logic, "predC")

let destr_has m event =
  match event.f_node with
  | Fapp ({ f_node = Fop(op, [ty_elem]) }, [f_f; f_l]) ->
      if EcPath.p_equal p_list_has op && not (Mid.mem m f_l.f_fv) then
        Some (ty_elem, {m;inv=f_f}, f_l)
      else None
  | _ -> None

let destr_pr_has pr =
  destr_has pr.pr_event.m pr.pr_event.inv

let is_eq_w_const_rhs (f: ss_inv): bool =
  try 
    let _, rhs = destr_eq f.inv in
    not (Mid.mem f.m rhs.f_fv)
  with DestrError _ -> false

(*
 lemma mu_has_le ['a 'b] (P : 'a -> 'b -> bool) (d : 'a distr) (s : 'b list) :
   mu d (fun a => has (P a) s) <= BRA.big predT (fun b => mu d (fun a => P a b)) s.
   Pr [f(args)@ &m : has Pa s] <= BRA.big predT (fun b => Pr [f(args) &m : Pa b]) s
*)
let pr_has_le f_pr =
  let pr = destr_pr f_pr in
  let ty_elem, f_f, f_l = oget (destr_pr_has pr) in
  let idx = EcIdent.create "x" in
  let x = f_local idx ty_elem in
  let pr_event = map_ss_inv1 (fun f -> f_app f [x] EcTypes.tbool) f_f in
  let f_pr1 = f_pr_r {pr with pr_event} in
  let f_fsum = f_lambda [idx, GTty ty_elem] f_pr1 in
  let f_sum =
    f_app (f_op p_BRA_big [ty_elem] EcTypes.treal) [f_predT ty_elem; f_fsum; f_l] EcTypes.treal in
  f_real_le f_pr f_sum

(* -------------------------------------------------------------------- *)
type pr_rewrite_kind =
  [ `Mu1LeEqMu1
  | `MuSum
  | `MuDisj
  | `MuEq
  | `MuFalse
  | `MuGe0
  | `MuLe1
  | `MuNot
  | `MuOr
  | `MuSplit
  | `MuSub
  | `MuHasLe ]

let rec decompose_imps f =
  try
    let f1, f2 = destr_imp f in
    let fs, c = decompose_imps f2 in
    (f1 :: fs, c)
  with DestrError _ ->
    ([], f)

let destr_mu f =
  match f.f_node with
  | Fapp ({ f_node = Fop (op, [ty]) }, [d; p]) ->
      if EcPath.p_equal EcCoreLib.CI_Distr.p_mu op then Some (ty, d, p) else None
  | _ -> None

let destr_eq_opt f =
  try Some (destr_eq f) with DestrError _ -> None

let destr_imp_opt f =
  try Some (destr_imp f) with DestrError _ -> None

let destr_or_r_opt f =
  try Some (destr_or_r f) with DestrError _ -> None

let destr_weight f =
  obind (fun (ty, d, p) ->
    if f_equal p (f_predT ty) then Some (ty, d) else None)
    (destr_mu f)

let destr_mu1 f =
  obind (fun (_, d, p) ->
    match p.f_node with
    | Fapp ({ f_node = Fop (op, _) }, [x]) ->
        if EcPath.p_equal EcCoreLib.CI_Pred.p_pred1 op then Some (d, x) else None
    | _ -> None)
    (destr_mu f)

let destr_pred_not f =
  match f.f_node with
  | Fapp ({ f_node = Fop (op, [_]) }, [p]) ->
      if EcPath.p_equal p_predC op then Some p else None
  | _ -> None

let destr_pred_binop path f =
  match f.f_node with
  | Fapp ({ f_node = Fop (op, [_]) }, [p; q]) ->
      if EcPath.p_equal path op then Some (p, q) else None
  | _ -> None

let destr_pred_and = destr_pred_binop p_predI
let destr_pred_or  = destr_pred_binop p_predU

let destr_real_add f =
  match f.f_node with
  | Fapp ({ f_node = Fop (op, _) }, [f1; f2]) ->
      if EcPath.p_equal EcCoreLib.CI_Real.p_real_add op then Some (f1, f2) else None
  | _ -> None

let destr_real_opp f =
  match f.f_node with
  | Fapp ({ f_node = Fop (op, _) }, [f1]) ->
      if EcPath.p_equal EcCoreLib.CI_Real.p_real_opp op then Some f1 else None
  | _ -> None

let destr_real_sub f =
  obind (fun (f1, f2) -> omap (fun f2 -> (f1, f2)) (destr_real_opp f2))
    (destr_real_add f)

let is_pred0 f =
  match f.f_node with
  | Fop (op, [_]) -> EcPath.p_equal p_pred0 op
  | _ -> false

let destr_lambda1 f =
  match f.f_node with
  | Fquant (Llambda, [(x, GTty ty)], body) -> ((x, ty), body)
  | _ -> raise Not_found

let destr_mu1_le_eq_mu1 hyps concl =
  if List.length hyps <> 2 then None else
  match hyps, concl.f_node with
  | [hll; hle], Fquant (Lforall, [_], body) ->
      begin match body.f_node with
      | Fapp ({ f_node = Fop (op, _) }, [lhs; rhs]) when EcPath.p_equal EcCoreLib.CI_Bool.p_eq op ->
          begin match destr_mu1 lhs, destr_mu1 rhs with
          | Some (d1, _), Some (d2, _) when f_equal d1 d2 ->
              begin match hll.f_node, hle.f_node with
              | Fapp ({ f_node = Fop (opll, _) }, [_]), Fquant (Lforall, [_], bodyle) ->
                  if EcPath.p_equal EcCoreLib.CI_Distr.p_lossless opll then
                    begin match bodyle.f_node with
                    | Fapp ({ f_node = Fop (ople, _) }, [lhsle; rhsle]) when EcPath.p_equal EcCoreLib.CI_Real.p_real_le ople ->
                        begin match destr_mu1 lhsle, destr_mu1 rhsle with
                        | Some (d1', _), Some (_, _) when f_equal d1 d1' -> Some `Mu1LeEqMu1
                        | _ -> None
                        end
                    | _ -> None
                    end
                  else None
              | _ -> None
              end
          | _ -> None
          end
      | _ -> None
      end
  | _ -> None

let classify_pr_rewrite env s : pr_rewrite_kind =
  let _path, ax = EcEnv.Ax.lookup ([], s) env in
  let body = snd (decompose_forall ax.ax_spec) in
  let hyps, concl = decompose_imps body in

  match concl.f_node with
  | Fapp ({ f_node = Fop (op, _) }, [lhs; rhs])
    when EcPath.p_equal EcCoreLib.CI_Bool.p_eq op ->
      begin match destr_mu lhs, destr_mu rhs with
      | Some (_, d1, _), Some (_, d2, _)
        when f_equal d1 d2 && List.length hyps = 1 ->
          `MuEq

      | Some (_, _, p), _ when List.length hyps = 0 && is_pred0 p && f_equal rhs f_r0 ->
          `MuFalse

      | Some (ty, d1, pnot), _
        when List.length hyps = 0 ->
          begin match destr_pred_not pnot, destr_real_sub rhs with
          | Some p, Some (w, mu) ->
              begin match destr_weight w, destr_mu mu with
              | Some (ty', d2), Some (_, d3, p')
                when EcTypes.ty_equal ty ty'
                  && f_equal d1 d2
                  && f_equal d1 d3
                  && f_equal p p' ->
                  `MuNot
              | _ -> raise Not_found
              end

          | _ ->
              begin match destr_pred_or pnot, destr_real_sub rhs with
              | Some (p1, p2), Some (sum12, mu12) ->
                  begin match destr_real_add sum12, destr_mu mu12 with
                  | Some (mu1, mu2), Some (_, d4, pand) ->
                      begin match destr_mu mu1, destr_mu mu2, destr_pred_and pand with
                      | Some (_, d2, q1), Some (_, d3, q2), Some (a1, a2)
                        when f_equal d1 d2
                          && f_equal d1 d3
                          && f_equal d1 d4
                          && f_equal p1 q1
                          && f_equal p2 q2
                          && f_equal p1 a1
                          && f_equal p2 a2 ->
                          `MuOr
                      | _ -> raise Not_found
                      end
                  | _ -> raise Not_found
                  end

              | _ ->
                  begin match rhs.f_node with
                  | Fapp ({ f_node = Fop (op, _) }, [mu1; mu2])
                    when EcPath.p_equal EcCoreLib.CI_Real.p_real_add op ->
                      begin match destr_pred_and pnot, destr_mu mu1, destr_mu mu2 with
                      | Some (p, q), Some (_, d2, pand1), Some (_, d3, pand2)
                        when f_equal d1 d2 && f_equal d1 d3 ->
                          begin match destr_pred_and pand1, destr_pred_and pand2 with
                          | Some (p1, q1), Some (p2, nq) ->
                              begin match destr_pred_not nq with
                              | Some q2
                                when f_equal p p1
                                  && f_equal p p2
                                  && f_equal q q1
                                  && f_equal q q2 ->
                                  `MuSplit
                              | _ -> raise Not_found
                              end
                          | _ -> raise Not_found
                          end
                      | _ -> raise Not_found
                      end

                  | Fapp ({ f_node = Fop (op, [_]) }, [lam])
                    when EcPath.p_equal EcCoreLib.CI_Sum.p_sum op
                      && List.length hyps = 0 ->
                      begin match destr_lambda1 lam with
                      | (_, _), body ->
                          begin match body.f_node with
                          | Fif (cond, then_, else_) ->
                              begin match destr_mu1 then_ with
                              | Some (_, x) when f_equal cond x && f_equal else_ f_r0 ->
                                  `MuSum
                              | _ -> raise Not_found
                              end
                          | _ -> raise Not_found
                          end
                      end

                  | _ -> raise Not_found
                  end
              end
          end

      | _ ->
          begin match destr_mu1_le_eq_mu1 hyps concl with
          | Some kind -> kind
          | None -> raise Not_found
          end
      end

  | Fapp ({ f_node = Fop (op, _) }, [lhs; rhs])
    when EcPath.p_equal EcCoreLib.CI_Real.p_real_le op ->
      begin match destr_mu lhs, destr_mu rhs with
      | Some (_, d1, _), Some (_, d2, _)
        when f_equal d1 d2 && List.length hyps = 1 ->
          `MuSub

      | _, Some _ when f_equal lhs f_r0 && List.length hyps = 0 ->
          `MuGe0

      | Some _, _ when f_equal rhs f_r1 && List.length hyps = 0 ->
          `MuLe1

      | Some (_, _, p), _
        when List.length hyps = 1 ->
          begin match destr_pred_or p, rhs.f_node with
          | Some _, Fapp ({ f_node = Fop (op, _) }, [mu1; mu2])
            when EcPath.p_equal EcCoreLib.CI_Real.p_real_add op ->
              begin match destr_mu mu1, destr_mu mu2 with
              | Some _, Some _ -> `MuDisj
              | _ -> raise Not_found
              end
          | _ -> raise Not_found
          end

      | Some (_, _, p), _
        when List.length hyps = 0 ->
          begin match destr_has (EcIdent.create "&hr") p, rhs.f_node with
          | Some (ty1, _, s1), Fapp ({ f_node = Fop (op, [_]) }, [predt; lam; s2])
            when EcPath.p_equal p_BRA_big op && f_equal s1 s2 ->
              begin match destr_lambda1 lam with
              | (_, ty2), body when EcTypes.ty_equal ty1 ty2 && f_equal predt (f_predT ty2) ->
                  begin match destr_mu body with
                  | Some _ -> `MuHasLe
                  | None -> raise Not_found
                  end
              | _ -> raise Not_found
              end
          | _ -> raise Not_found
          end

      | _ -> raise Not_found
      end

  | Fquant (Lforall, [_], _) ->
      begin match destr_mu1_le_eq_mu1 hyps concl with
      | Some kind -> kind
      | None -> raise Not_found
      end

  | _ ->
      raise Not_found

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
          Mid.set_disjoint f_l.f_fv sid ->
            raise (FoundPr f_pr)
        | _ -> false
      else false
  | _ -> false

(* -------------------------------------------------------------------- *)
let t_pr_rewrite_low (s, (dof: (_ -> _ -> _ -> ss_inv) option)) tc =
  let env, hyps, concl = FApi.tc1_eflat tc in
  let kind =
    try classify_pr_rewrite env s
    with Not_found ->
      tc_error !!tc "Pr-rewrite: `%s` is not a suitable probability lemma" s
  in

  let expect_arg = function `MuSplit | `Mu1LeEqMu1 -> true | _ -> false in
  (if not (is_some dof = expect_arg kind) then
     let neg = if is_some dof then "no " else "" in
     tc_error !!tc "Pr-rewrite: %sargument expected for `%s`" neg s);

  let select =
    match kind with
    | `Mu1LeEqMu1 -> select_pr is_eq_w_const_rhs
    | `MuDisj | `MuOr -> select_pr (fun inv -> is_or inv.inv)
    | `MuEq -> select_pr_cmp (EcPath.p_equal EcCoreLib.CI_Bool.p_eq)
    | `MuFalse -> select_pr (fun inv -> is_false inv.inv)
    | `MuGe0 -> select_pr_ge0
    | `MuLe1 -> select_pr_le1
    | `MuNot -> select_pr (fun inv -> is_not inv.inv)
    | `MuSplit -> select_pr (fun _ev -> true)
    | `MuSub -> select_pr_cmp (EcPath.p_equal EcCoreLib.CI_Real.p_real_le)
    | `MuSum -> select_pr (fun _ev -> true)
    | `MuHasLe -> select_pr_muhasle
  in

  let select xs fp = if select xs fp then `Accept (-1) else `Continue in
  let torw =
    try
      ignore (EcMatching.FPosition.select select concl);
      tc_error !!tc "Pr-rewrite: cannot find a pattern for `%s`" s
    with FoundPr f -> f in

  let lemma, args =
    match kind with
    | `Mu1LeEqMu1 -> 
      let { pr_fun; pr_args; pr_mem } as pr = destr_pr torw in
      let (resv, k) = map_ss_inv_destr2 destr_eq pr.pr_event in
      let k_id = EcEnv.LDecl.fresh_id hyps "k" in
      let d = (oget dof) tc torw (EcTypes.tdistr k.inv.f_ty) in
      (* Check that k and d do not reference the post-execution memory.
         Otherwise the rewrite is unsound: the event `res = k` would use
         k from the post-state, but `mu1 d k` treats k as a constant. *)
      if Mid.mem k.m k.inv.f_fv then
        (* This case should already be filtered by selection *)
        assert false;
      if Mid.mem d.m d.inv.f_fv then
        tc_error !!tc
          "Pr-rewrite: the distribution must not depend on memories";
      (pr_mu1_le_eq_mu1 pr_mem pr_fun pr_args resv k.inv k_id d.inv, 2)

    | (`MuEq | `MuSub as kind) -> begin
      match torw.f_node with
      | Fapp(_, [{f_node = Fpr pr1 };
                 {f_node = Fpr pr2 };])
        -> begin
          let { pr_mem = m ; pr_fun = f; pr_args = args } = pr1 in
          let ev1 = pr1.pr_event in
          let ev2 = EcSubst.ss_inv_rebind pr2.pr_event ev1.m in
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
        let ev = map_ss_inv1 destr_not pr.pr_event in
        (pr_not m f args ev, 0)

    | `MuOr ->
        let { pr_mem = m ; pr_fun = f; pr_args = args; } as pr = destr_pr torw in
        let asym = fst (destr_or_r pr.pr_event.inv) in
        let (ev1, ev2) = map_ss_inv_destr2 (fun prev -> snd (destr_or_r prev)) pr.pr_event in
        (pr_or m f args (match asym with | `Asym -> map_ss_inv2 f_ora | `Sym -> map_ss_inv2 f_or) ev1 ev2, 0)

    | `MuDisj ->
        let { pr_mem = m ; pr_fun = f; pr_args = args; } as pr = destr_pr torw in
        let asym = fst (destr_or_r pr.pr_event.inv) in
        let (ev1, ev2) = map_ss_inv_destr2 (fun prev -> snd (destr_or_r prev)) pr.pr_event in
        (pr_disjoint env m f args (match asym with | `Asym -> map_ss_inv2 f_ora | `Sym -> map_ss_inv2 f_or) ev1 ev2, 1)

    | `MuSplit ->
      let pr = destr_pr torw in
      let ev' = EcSubst.ss_inv_rebind ((oget dof) tc torw EcTypes.tbool) pr.pr_event.m in
      (pr_split pr.pr_mem pr.pr_fun pr.pr_args pr.pr_event ev', 0)

    | `MuGe0 -> begin
      match torw.f_node with
      | Fapp({f_node = Fop _}, [_; {f_node = Fpr pr}]) ->
            let { pr_mem = m; pr_fun = f; pr_args = args } = pr in
            (pr_ge0 m f args pr.pr_event, 0)
      | _ -> assert false
      end

    | `MuLe1 -> begin
      match torw.f_node with
      | Fapp({f_node = Fop _}, [{f_node = Fpr pr}; _]) ->
            let { pr_mem = m; pr_fun = f; pr_args = args } = pr in
            (pr_le1 m f args pr.pr_event, 0)
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
    let m = EcIdent.create "&hr" in
    let mp = EcEnv.Fun.prF_memenv m pr.pr_fun env in
    let hyps = LDecl.push_active_ss mp hyps in
    {m;inv=EcProofTyping.process_form hyps f ty}
  in
  t_pr_rewrite_low (s, omap to_env f) tc
