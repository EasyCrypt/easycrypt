(* -------------------------------------------------------------------- *)
open EcUtils
open EcPath
open EcAst
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
(* Syntactic check that two procedures are equal up to [bad]: they are
   the same program until [bad <- true], which both execute at the same
   point, and [bad] is never assigned anything but [true] afterwards. *)
let e_true  = expr_of_form f_true
let e_false = expr_of_form f_false

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

exception BadAssign of xpath option * instr

let badassign i env bad lv =
  if not (check_not_bad env bad lv) then raise (BadAssign (None, i))

let rec check_bad_true env bad s =
  match s with
  | [] -> ()
  | i :: c ->
    begin match i.i_node with
    | Sasgn (lv, e) ->
       if not (is_bad_true env bad lv e) then badassign i env bad lv
    | Srnd  (lv, _) ->
      badassign i env bad lv
    | Scall (lv, f, _) ->
       oiter (badassign i env bad) lv;
       check_f_bad_true env bad f
    | Sif (_, c1, c2) ->
      check_bad_true env bad c1.s_node;
      check_bad_true env bad c2.s_node
    | Swhile(_,c) ->
      check_bad_true env bad c.s_node
    | Smatch(_,bs) ->
      let check_branch (_, s) = check_bad_true env bad s.s_node in
      List.iter (check_branch) bs
    | Sraise _ -> tacuerror "exception are not supported"
    | Sabstract _ -> ()
    end;
    check_bad_true env bad c

and check_f_bad_true env bad f =
  let f = NormMp.norm_xfun env f in
  let fd = Fun.by_xpath f env in
  match fd.f_def with
  | FBalias _ -> assert false
  | FBdef fd ->
    begin
      try check_bad_true env bad fd.f_body.s_node
      with BadAssign (None, i) -> raise (BadAssign(Some f, i))
    end
  | FBabs o ->
    oiter (fun bad ->
      let fv = EcPV.PV.add env bad tbool EcPV.PV.empty in
      EcPV.PV.check_depend env fv (m_functor f.x_top)) bad;
    List.iter (check_f_bad_true env bad) (OI.allowed o)

(* The two procedures have the same parameters (in the same order) and the
   same local variables: their bodies are then compared syntactically, the
   variables of one standing for the same ones of the other. *)
let same_vars env fun1 fun2 fd1 fd2 =
  let check_param a1 a2 =
       a1.ov_name = a2.ov_name
    && EqTest.for_type env a1.ov_type a2.ov_type in
  let check_local x1 x2 =
    x1.v_name = x2.v_name && EqTest.for_type env x1.v_type x2.v_type in
     List.all2 check_param fun1.f_sig.fs_anames fun2.f_sig.fs_anames
  && List.all2 check_local fd1.f_locals fd2.f_locals

let rec s_upto_r env alpha bad s1 s2 =
  match s1, s2 with
  | [], [] -> true
  | {i_node = Sasgn(x1, e1)} :: s1, {i_node = Sasgn (x2, e2)} :: s2 when
          is_bad_true env bad x1 e1 && is_bad_true env bad x2 e2 ->
      check_bad_true env bad s1;
      check_bad_true env bad s2;
      true

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
    EqTest.for_expr env ~alpha a1 a2 &&
    s_upto env alpha bad b1 b2 &&
    s_upto env alpha bad c1 c2

  | Swhile(a1,b1), Swhile(a2,b2) ->
    EqTest.for_expr env ~alpha a1 a2 &&
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

  | Sraise _, Sraise _ -> tacuerror "exception are not supported"

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
    same_vars env fun1 fun2 fd1 fd2 &&
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

(* The bodies may start with a common prefix, not constrained by [bad],
   followed by [bad <- false] on both sides. *)
let rec s_upto_init env alpha bad s1 s2 =
  match s1, s2 with
  | [], [] -> true
  | {i_node = Sasgn(x1, e1)} :: s1, {i_node = Sasgn (x2, e2)} :: s2 when
          is_bad_false env (Some bad) x1 e1 && is_bad_false env (Some bad) x2 e2 ->
      check_bad_true env (Some bad) s1;
      check_bad_true env (Some bad) s2;
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
    let alpha = EcIdent.Mid.empty in
    let body1 = fd1.f_body and body2 = fd2.f_body in
    same_vars env fun1 fun2 fd1 fd2 &&
    oall2 (EqTest.for_expr env) fd1.f_ret fd2.f_ret &&
    ( s_upto_init env alpha bad body1.s_node body2.s_node ||
      s_upto      env alpha (Some bad) body1 body2 )

  | FBabs _, FBabs _ -> f_upto env (Some bad) f1 f2

  | _, _ -> false

(* -------------------------------------------------------------------- *)
let destr_bad (f: ss_inv) =
  match destr_pvar f.inv with
  | (PVglob _ as bad, m) when EcIdent.id_equal m f.m -> bad
  | _ -> destr_error ""

let destr_not_bad f =
  destr_bad (map_ss_inv1 destr_not f)

let destr_event f =
  let b = try snd (map_ss_inv_destr2 destr_and f) with DestrError _ -> f in
  destr_not_bad b

(* -------------------------------------------------------------------- *)
(* The upto rule has no parameters: [bad] is read from the event. *)
type EcCoreGoal.rule += REquivUpto

(* Why the side conditions of the rule do not hold, in the order they are
   checked. *)
type upto_error =
  | UENotPrEq                           (* not [Pr[_] = Pr[_]] *)
  | UEMemory                            (* different initial memories *)
  | UEArgs                              (* different arguments *)
  | UEEvent                             (* different events *)
  | UEBadForm                           (* event not [E /\ !bad] / [!bad] *)
  | UENotUpto                           (* procedures not equal upto bad *)
  | UEBadAssign of xpath option * instr (* [bad] reset after being set *)

exception UptoError of upto_error

(* -------------------------------------------------------------------- *)
(* Pure core shared by the rule and its checker: it checks the side
   conditions of the rule (raising [UptoError] when one does not hold),
   so the checker re-validates them. The rule has no premise. *)
let equiv_upto_subgoals (hyps : LDecl.hyps) (concl : form) : form list =
  let env  = LDecl.toenv hyps in
  let fail = fun e -> raise (UptoError e) in
  let pr1, pr2 =
    try t2_map destr_pr (destr_eq concl)
    with DestrError _ -> fail UENotPrEq in
  if not (EcMemory.mem_equal pr1.pr_mem pr2.pr_mem) then
    fail UEMemory;
  if not (is_conv ~ri:full_red hyps pr1.pr_args pr2.pr_args) then
    fail UEArgs;
  if not (ss_inv_alpha_eq hyps pr1.pr_event pr2.pr_event) then
    fail UEEvent;
  let bad =
    try destr_event pr1.pr_event
    with DestrError _ -> fail UEBadForm in
  begin match f_upto_init env bad pr1.pr_fun pr2.pr_fun with
  | true -> ()
  | false -> fail UENotUpto
  | exception BadAssign (f, i) -> fail (UEBadAssign (f, i))
  end;
  []

(* -------------------------------------------------------------------- *)
let upto_error (tc : tcenv1) (e : upto_error) =
  match e with
  | UENotPrEq ->
      tc_error !!tc ~who:"byupto" "expecting a formula of the form \"Pr[_] = Pr[_]\""
  | UEMemory ->
      tc_error !!tc ~who:"byupto" "the initial memories should be equal"
  | UEArgs ->
      tc_error !!tc ~who:"byupto" "the initial arguments should be equal"
  | UEEvent ->
      tc_error !!tc ~who:"byupto" "the events should be equal"
  | UEBadForm ->
      tc_error !!tc ~who:"byupto" "the event should have the form \"E /\ !bad\" or \"!bad\""
  | UENotUpto ->
      tc_error !!tc ~who:"byupto" "the two functions are not equal upto bad"
  | UEBadAssign (f, i) ->
      let ppenv = EcPrinting.PPEnv.ofenv (FApi.tc1_env tc) in
      let pp_fun fmt = function
       | None -> ()
       | Some f -> Format.fprintf fmt " in function %a" (EcPrinting.pp_funname ppenv) f in
      tc_error !!tc ~who:"byupto" "bad is assigned after being set to true%a, %a"
        pp_fun f (EcPrinting.pp_instr ppenv) i

(* Rule (TCB). The side conditions are checked by the pure core; their
   failure is reported with the tactic's messages. *)
let t_equiv_upto (tc : tcenv1) =
  let subgoals =
    try equiv_upto_subgoals (FApi.tc1_hyps tc) (FApi.tc1_goal tc)
    with UptoError e -> upto_error tc e in
  FApi.xrule1 tc REquivUpto subgoals

(* -------------------------------------------------------------------- *)
let () =
  register_rule_checker
    (function
     | REquivUpto ->
         Some (EcPlRecheck.checker_of "equiv-upto" (fun _ concl -> concl)
                 equiv_upto_subgoals)
     | _ -> None)

(* -------------------------------------------------------------------- *)
(* Elaboration: [byupto] on a probability statement. The statements that
   are not directly an instance of the rule are reduced to it by a lemma
   of the real theory, whose premises are the instance of the rule and
   facts on probabilities (closed by [rewrite Pr] and [trivial]). *)
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
  let e, fbad = map_ss_inv_destr2 destr_and prb1.pr_event in
  let fnbad = map_ss_inv1 f_not fbad in
  let fenb = map_ss_inv2 f_and e fnbad in
  let fe1nb = f_pr pre1.pr_mem pre1.pr_fun pre1.pr_args fenb in
  let fe2nb = f_pr pre2.pr_mem pre2.pr_fun pre2.pr_args fenb in
  fe1, fe1b, fe1nb, fe2, fe2b, fe2nb, fbad

let destr_sub_maxr f1 f2 =
  let fe1, fe2 = DestrReal.sub f1 in
  let fe1b', fe2b' = destr_maxr f2 in
  let pre1, pre2, prb1_ = t3_map destr_pr (fe1, fe2, fe1b') in
  let bad =
    let b = try snd (map_ss_inv_destr2 destr_and prb1_.pr_event) with DestrError _ -> prb1_.pr_event in
    destr_bad b in
  let e = pre1.pr_event in
  let fbad = f_pvar bad tbool e.m in
  let fnbad = map_ss_inv1 f_not fbad in
  let fenb = map_ss_inv2 f_and e fnbad in
  let feb   = map_ss_inv2 f_and e fbad in
  let fe1b  = f_pr pre1.pr_mem pre1.pr_fun pre1.pr_args feb in
  let fe1nb = f_pr pre1.pr_mem pre1.pr_fun pre1.pr_args fenb in
  let fe2b  = f_pr pre2.pr_mem pre2.pr_fun pre2.pr_args feb in
  let fe2nb = f_pr pre2.pr_mem pre2.pr_fun pre2.pr_args fenb in
  fe1, fe1b, fe1nb, fe2, fe2b, fe2nb, fbad, fe1b', fe2b'

(* TEMPORARY: the facts on probabilities are closed by [rewrite Pr], from
   the not-yet-migrated [EcPhlPrRw]. *)
let t_split_pr fbad =
  t_pr_rewrite_i ("mu_split", Some fbad) @! t_trivial

let t_ge0_pr =
  t_pr_rewrite_i ("mu_ge0", None) @! t_trivial

let t_sub_pr =
  t_pr_rewrite_i ("mu_sub", None) @! t_trivial

let process_upto (tc : tcenv1) =
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
             t_equiv_upto ]) tc
    | SFpr _, SFpr _ -> t_equiv_upto tc
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
            try destr_bad (prb.pr_event)
            with DestrError _ -> destr_bad (snd (map_ss_inv_destr2 destr_and prb.pr_event))
          in
          let e = pr1.pr_event in
          pr2, e, bad
        with DestrError _ -> error_add tc in

      let fbad = (f_pvar bad tbool e.m) in
      let fnbad = map_ss_inv1 f_not fbad in
      let pr1b, pr1nb, pr2nb =
        f_pr pr1.pr_mem pr1.pr_fun pr1.pr_args (map_ss_inv2 f_and e fbad),
        f_pr pr1.pr_mem pr1.pr_fun pr1.pr_args (map_ss_inv2 f_and e fnbad),
        f_pr pr2.pr_mem pr2.pr_fun pr2.pr_args (map_ss_inv2 f_and e fnbad) in
      (t_apply_prept
        (`App (`UG upto_le,
          [`F f1; `F pr1b; `F pr1nb;
           `F pr2nb; `F f2; `F fb;
           `H_; `H_; `H_; `H_])) @+
          [  t_split_pr fbad;
             t_equiv_upto;
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
             t_equiv_upto ]) tc
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
             t_equiv_upto;
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
