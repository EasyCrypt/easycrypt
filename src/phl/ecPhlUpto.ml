(* -------------------------------------------------------------------- *)
open EcUtils
open EcPath
open EcTypes
open EcModules

open EcEnv
open EcReduction
open EcFol
open EcCoreGoal
open EcLowGoal
open EcHiGoal
open EcPhlPrRw
open EcCoreLib.CI_Real

(* -------------------------------------------------------------------- *)
(* Core tactic *)
let e_true  = expr_of_form mhr f_true
let e_false = expr_of_form mhr f_false

let is_lv_bad env bad x =
  match bad with
  | None -> false
  | Some bad -> EqTest.for_lv env x (LvVar (bad, tbool))

let is_bad be env bad x e =
   is_lv_bad env bad x && EqTest.for_expr env e be

let is_bad_true = is_bad e_true

let is_bad_false = is_bad e_false

let check_not_bad env bad lv =
  match lv with
  | LvVar _ -> not (is_lv_bad env bad lv)
  | LvTuple xs -> not (List.exists (fun xt -> is_lv_bad env bad (LvVar xt)) xs)

let rec s_upto_r env alpha bad s1 s2 =
  match s1, s2 with
  | [], [] -> true
  | {i_node = Sasgn(x1, e1)} :: _, {i_node = Sasgn (x2, e2)} :: _ when
          is_bad_true env bad x1 e1 && is_bad_true env bad x2 e2 -> true
  | i1 :: s1, i2 :: s2 ->
    i_upto env alpha bad i1 i2 && s_upto_r env alpha bad s1 s2
  | _, _ -> false

and s_upto env alpha bad s1 s2 = s_upto_r env alpha bad s1.s_node s2.s_node

and i_upto env alpha bad i1 i2 =

  match i1.i_node, i2.i_node with
  | Sasgn (lv1, _), Sasgn (lv2, _)
  | Srnd  (lv1, _), Srnd  (lv2, _) ->
    check_not_bad env bad lv1 &&
    check_not_bad env bad lv2 &&
    EqTest.for_instr env ~alpha i1 i2

  | Scall (lv1, f1, e1), Scall (lv2, f2, e2) ->
    omap_dfl (check_not_bad env bad) true lv1 &&
    omap_dfl (check_not_bad env bad) true lv2 &&
    oall2 (EqTest.for_lv env) lv1 lv2 &&
    List.all2 (EqTest.for_expr env ~alpha) e1 e2 &&
    f_upto env bad f1 f2

  | Sif (a1, b1, c1), Sif(a2, b2, c2) ->
    EqTest.for_expr env a1 a2 &&
    s_upto env alpha bad b1 b2 &&
    s_upto env alpha bad c1 c2

  | Swhile(a1,b1), Swhile(a2,b2) ->
    EqTest.for_expr env a1 a2 &&
    s_upto env alpha bad b1 b2

  | Smatch(e1,bs1), Smatch(e2,bs2) when List.length bs1 = List.length bs2 -> begin
    let module E = struct exception NotConv end in

    let check_branch (xs1, s1) (xs2, s2) =
      if List.length xs1 <> List.length xs2 then false
      else
        let alpha =
          let do1 alpha (id1, ty1) (id2, ty2) =
            if not (EqTest.for_type env ty1 ty2) then raise E.NotConv;
            EcIdent.Mid.add id1 (id2, ty2) alpha in
          List.fold_left2 do1 alpha xs1 xs2 in
        s_upto env alpha bad s1 s2 in

    try
         EqTest.for_expr env ~alpha e1 e2
      && List.all2 (check_branch) bs1 bs2
    with E.NotConv -> false
  end

  | Sassert a1, Sassert a2 ->
    EqTest.for_expr env ~alpha a1 a2

  | Sabstract id1, Sabstract id2 ->
    EcIdent.id_equal id1 id2

  | _, _ -> false

and f_upto env bad f1 f2 =
  let f1 = NormMp.norm_xfun env f1 in
  let f2 = NormMp.norm_xfun env f2 in
  let fun1 = Fun.by_xpath f1 env in
  let fun2 = Fun.by_xpath f2 env in
  match fun1.f_def, fun2.f_def with
  | FBalias _, _ | _, FBalias _ -> assert false
  | FBdef fd1, FBdef fd2 ->
    let check_param x1 x2 =
      x1.v_name = x2.v_name && EqTest.for_type env x1.v_type x2.v_type in
    List.all2 check_param fd1.f_locals fd2.f_locals &&
    oall2 (EqTest.for_expr env) fd1.f_ret fd2.f_ret &&
    s_upto env EcIdent.Mid.empty bad fd1.f_body fd2.f_body

  | FBabs o1, FBabs o2 ->
    f1.x_sub = f2.x_sub &&
    EcPath.mt_equal f1.x_top.m_top f2.x_top.m_top &&
    omap_dfl (fun bad ->
      let fv = EcPV.PV.add env bad tbool EcPV.PV.empty in
      EcPV.PV.check_depend env fv (m_functor f1.x_top); true) true bad &&
    List.all2 (f_upto env bad) (OI.allowed o1) (OI.allowed o2)

  | _, _ -> false

let rec s_upto_init env alpha bad s1 s2 =
  match s1, s2 with
  | [], [] -> true
  | {i_node = Sasgn(x1, e1)} :: s1, {i_node = Sasgn (x2, e2)} :: s2 when
          is_bad_false env (Some bad) x1 e1 && is_bad_false env (Some bad) x2 e2 ->
      s_upto_r env alpha (Some bad) s1 s2
  | i1 :: s1, i2 :: s2 ->
    i_upto env alpha None i1 i2 && s_upto_init env alpha bad s1 s2
  | _, _ -> false

let f_upto_init env bad f1 f2 =
  let f1 = NormMp.norm_xfun env f1 in
  let f2 = NormMp.norm_xfun env f2 in
  let fun1 = Fun.by_xpath f1 env in
  let fun2 = Fun.by_xpath f2 env in
  match fun1.f_def, fun2.f_def with
  | FBalias _, _ | _, FBalias _ -> assert false
  | FBdef fd1, FBdef fd2 ->
    let check_param x1 x2 =
      x1.v_name = x2.v_name && EqTest.for_type env x1.v_type x2.v_type in
    let alpha = EcIdent.Mid.empty in
    let body1 = fd1.f_body and body2 = fd2.f_body in
    List.all2 check_param fd1.f_locals fd2.f_locals &&
    oall2 (EqTest.for_expr env) fd1.f_ret fd2.f_ret &&
    ( s_upto_init env alpha bad body1.s_node body2.s_node ||
      s_upto      env alpha (Some bad) body1 body2)

  | FBabs _, FBabs _ -> f_upto env (Some bad) f1 f2

  | _, _ -> false

let destr_bad f =
  match destr_pvar f with
  | (PVglob _ as bad, m) when EcIdent.id_equal m mhr -> bad
  | _ -> destr_error ""

let destr_not_bad f =
  destr_bad (destr_not f)

let destr_event f =
  let b = try snd (destr_and f) with DestrError _ -> f in
  destr_not_bad b

let t_uptobad_r tc =
  let env, hyps, concl = FApi.tc1_eflat tc in
  let pr1, pr2 =
    try t2_map destr_pr (destr_eq concl)
    with DestrError _ ->
      tc_error !!tc ~who:"byupto" "expecting a formula of the form \"Pr[_] = Pr[_]\""
  in
  if not (EcMemory.mem_equal pr1.pr_mem pr2.pr_mem) then
    tc_error !!tc ~who:"byupto" "the initial memories should be equal";
  if not (is_conv ~ri:full_red hyps pr1.pr_args pr2.pr_args) then
    tc_error !!tc ~who:"byupto" "the initial arguments should be equal";
  if not (is_conv ~ri:full_red hyps pr1.pr_event pr2.pr_event) then
    tc_error !!tc ~who:"byupto" "the events should be equal";
  let bad =
    try destr_event pr1.pr_event
    with DestrError _ ->
      tc_error !!tc ~who:"byupto" "the event should have the form \"E /\ !bad\" or \"!bad\""
  in
  if not (f_upto_init env bad pr1.pr_fun pr2.pr_fun) then
      tc_error !!tc ~who:"byupto" "the two function are not equal upto bad";
  FApi.xmutate1 tc `HlUpto []

let t_uptobad = FApi.t_low0 "upto-bad" t_uptobad_r

(* End Core tactic                                                      *)
(* -------------------------------------------------------------------- *)

let p_real_maxr = real_order_lemma "maxr"
let destr_maxr  = destr_app2_eq ~name:"real_maxr" p_real_maxr

let eq_upto   = real_lemma "eq_upto"
let upto_abs  = real_lemma "upto_abs"
let upto_maxr = real_order_lemma "upto_maxr"
let upto_le   = real_lemma "upto_le"

let error_eq_add tc =
tc_error !!tc
"expecting a goal of the form\
 \"Pr[G1:E] - Pr[G2:E] = Pr[G1:E /\\ bad] - Pr[G2:E /\\ bad]\""

let error_eq tc =
tc_error !!tc
"expecting a goal of the form\
 \"Pr[G1:E] - Pr[G2:E] = Pr[G1:E /\\ bad] - Pr[G2:E /\\ bad]\" or\
 \"Pr[G1:E /\\ !bad] = Pr[G2:E /\\ !bad]\""

let error_add tc =
tc_error !!tc
"expecting a goal of the form\
 \"Pr[G1:E] <= Pr[G2:E [/\\ !bad]? ] + Pr[G1: [E /\\]? bad]\""

let error_abs_abs tc =
tc_error !!tc
"expecting a goal of the form\
 \"`| Pr[G1 : E] - Pr[G2 : E] | <= `| Pr[G1: E /\\ bad] - Pr[G2:E /\\ bad]\""

let error_abs_maxr tc =
tc_error !!tc
"expecting a goal of the form\
 \"`| Pr[G1 : E] - Pr[G2 : E] | <= maxr Pr[G1: [E /\\]? bad] - Pr[G2:[E /\\]? bad]\""

let destr_sub f1 f2 =
  let fe1, fe2 = DestrReal.sub f1 in
  let fe1b, fe2b = DestrReal.sub f2 in
  let pre1, pre2, prb1 = t3_map destr_pr (fe1, fe2, fe1b) in
  let e, fbad = destr_and prb1.pr_event in
  let fnbad = f_not fbad in
  let fenb = f_and e fnbad in
  let fe1nb = f_pr_r {pre1 with pr_event = fenb } in
  let fe2nb = f_pr_r {pre2 with pr_event = fenb } in
  fe1, fe1b, fe1nb, fe2, fe2b, fe2nb, fbad

let destr_sub_maxr f1 f2 =
  let fe1, fe2 = DestrReal.sub f1 in
  let fe1b', fe2b' = destr_maxr f2 in
  let pre1, pre2, prb1_ = t3_map destr_pr (fe1, fe2, fe1b') in
  let bad =
    let b = try snd (destr_and prb1_.pr_event) with DestrError _ -> prb1_.pr_event in
    destr_bad b in
  let fbad = f_pvar bad tbool mhr in
  let e = pre1.pr_event in
  let fnbad = f_not fbad in
  let fenb = f_and e fnbad in
  let feb   = f_and e fbad in
  let fe1b  = f_pr_r { pre1 with pr_event = feb } in
  let fe1nb = f_pr_r { pre1 with pr_event = fenb } in
  let fe2b  = f_pr_r { pre2 with pr_event = feb } in
  let fe2nb = f_pr_r { pre2 with pr_event = fenb } in
  fe1, fe1b, fe1nb, fe2, fe2b, fe2nb, fbad, fe1b', fe2b'

let t_split_pr fbad =
  t_pr_rewrite_i ("mu_split", Some fbad) @! t_trivial

let t_ge0_pr =
  t_pr_rewrite_i ("mu_ge0", None) @! t_trivial

let t_sub_pr =
  t_pr_rewrite_i ("mu_sub", None) @! t_trivial

let process_uptobad tc =
  let concl = FApi.tc1_goal tc in
  match sform_of_form concl with
  | SFeq (f1, f2) ->
    begin match sform_of_form f1, sform_of_form f2 with
    | SFop((o1,_), [_; _]), SFop((o2,_), [_; _])
         when EcPath.p_equal o1 p_real_add &&  EcPath.p_equal o2 p_real_add ->
        let fe1, fe1b, fe1nb, fe2, fe2b, fe2nb, fbad =
          try destr_sub f1 f2
          with DestrError _ -> error_eq_add tc in
        (t_apply_prept
          (`App (`UG eq_upto,
            [`F fe1; `F fe1b; `F fe1nb;
             `F fe2; `F fe2b; `F fe2nb;
             `H_; `H_; `H_])) @+
           [ t_split_pr fbad;
             t_split_pr fbad;
             t_uptobad ]) tc
    | SFpr _, SFpr _ -> t_uptobad tc
    | _ -> error_eq tc
    end

  | SFop((o,_), [f1; f]) when EcPath.p_equal o p_real_le ->
    begin match sform_of_form f1 with
    | SFpr pr1 ->
      (* Pr[G1 : E] <= Pr[G2 : E [/\ !bad]] + Pr[G1: [E /\] bad] *)
      let f2, fb = DestrReal.add f in
        let pr2, e, bad =
        try
          let pr2, prb = t2_map destr_pr (f2, fb) in
          let bad =
            try destr_bad prb.pr_event
            with DestrError _ -> destr_bad (snd (destr_and prb.pr_event))
          in
          let e = pr1.pr_event in
          pr2, e, bad
        with DestrError _ -> error_add tc in

      let fbad = f_pvar bad tbool mhr in
      let fnbad = f_not fbad in
      let pr1b, pr1nb, pr2nb =
        f_pr_r {pr1 with pr_event = f_and e fbad},
        f_pr_r {pr1 with pr_event = f_and e fnbad},
        f_pr_r {pr2 with pr_event = f_and e fnbad} in
      (t_apply_prept
        (`App (`UG upto_le,
          [`F f1; `F pr1b; `F pr1nb;
           `F pr2nb; `F f2; `F fb;
           `H_; `H_; `H_; `H_])) @+
          [  t_split_pr fbad;
             t_uptobad;
             t_sub_pr;
             t_sub_pr;
          ]) tc

    | SFop((o,_), [f1]) when EcPath.p_equal o p_real_abs ->
      begin match DestrReal.abs f with
      | f2 ->
        (* `| Pr[G1 : E] - Pr[G2 : E] | <= `| Pr[G1: E /\ bad] - Pr[G2:E /\ bad] *)
        let fe1, fe1b, fe1nb, fe2, fe2b, fe2nb, fbad =
          try destr_sub f1 f2
          with DestrError _ -> error_abs_abs tc in
        (t_apply_prept
          (`App (`UG upto_abs,
            [`F fe1; `F fe1b; `F fe1nb;
             `F fe2; `F fe2b; `F fe2nb;
             `H_; `H_; `H_])) @+
           [ t_split_pr fbad;
             t_split_pr fbad;
             t_uptobad ]) tc
      | exception DestrError _ ->
        (* `| Pr[G1 : E] - Pr[G2 : E] | <= maxr Pr[G1: [E /\] bad] Pr[G2: [E /\] bad] *)
        let fe1, fe1b, fe1nb, fe2, fe2b, fe2nb, fbad, fe1b', fe2b' =
          try destr_sub_maxr f1 f
          with DestrError _ -> error_abs_maxr tc in
        (t_apply_prept
          (`App (`UG upto_maxr,
            [`F fe1; `F fe1b; `F fe1nb;
             `F fe2; `F fe2b; `F fe2nb;
             `F fe1b'; `F fe2b';
             `H_; `H_; `H_; `H_; `H_; `H_; `H_])) @+
           [ t_split_pr fbad;
             t_split_pr fbad;
             t_uptobad;
             t_ge0_pr;
             t_sub_pr;
             t_ge0_pr;
             t_sub_pr;
        ]) tc
      end

    | _ ->
        tc_error !!tc
          "expecting a goal of the form \"Pr[_] <= Pr[_] + Pr[_]\" or \"`|Pr[_] - Pr[_]| <= _\""
    end
  | _ ->
    tc_error !!tc ~who:"byupto" "expecting a goal of the form \" _ <= _\""
