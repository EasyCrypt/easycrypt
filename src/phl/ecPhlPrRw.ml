(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2016 - Inria
 * 
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcUtils
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
  let hyp = f_forall_mems [mem] (f_iff p1 p2) in
  let concl = f_eq (f_pr m f args p1) (f_pr m f args p2) in
    f_imp hyp (f_eq concl f_true)

let pr_sub env m f args p1 p2 = 
  let mem = Fun.prF_memenv mhr f env in
  let hyp = f_forall_mems [mem] (f_imp p1 p2) in
  let concl = f_real_le (f_pr m f args p1) (f_pr m f args p2) in
    f_imp hyp (f_eq concl f_true)

let pr_false m f args = 
  f_eq (f_pr m f args f_false) f_r0

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
  let hyp = f_forall_mems [mem] (f_not (f_and p1 p2)) in 
  let pr1 = f_pr m f args p1 in
  let pr2 = f_pr m f args p2 in
  let pr =  f_real_add pr1 pr2 in
    f_imp hyp (f_eq (f_pr m f args (por p1 p2)) pr)

let pr_split m f args ev1 ev2 = 
  let pr  = f_pr m f args ev1 in 
  let pr1 = f_pr m f args (f_and ev1 ev2) in
  let pr2 = f_pr m f args (f_and ev1 (f_not ev2)) in
  f_eq pr (f_real_add pr1 pr2)

(* -------------------------------------------------------------------- *)
exception FoundPr of form

let select_pr on_ev sid f = 
  match f.f_node with
  | Fpr { pr_event = ev } ->
      if   on_ev ev && Mid.set_disjoint f.f_fv sid
      then raise (FoundPr f)
      else false
  | _ -> false

let select_pr_cmp on_cmp sid f = 
  match f.f_node with
  | Fapp({f_node = Fop(op,_)},
         [{f_node = Fpr pr1};
          {f_node = Fpr pr2}]) ->

      if    on_cmp op
         && EcIdent.id_equal pr1.pr_mem  pr2.pr_mem
         && EcPath.x_equal   pr1.pr_fun  pr2.pr_fun
         && f_equal          pr1.pr_args pr2.pr_args
         && Mid.set_disjoint f.f_fv sid
      then raise (FoundPr f)
      else false

  | _ -> false

(* -------------------------------------------------------------------- *)
let pr_rewrite_lemma = 
  ["mu_eq"      , `MuEq;
   "mu_sub"     , `MuSub;
   "mu_false"   , `MuFalse;
   "mu_not"     , `MuNot;
   "mu_or"      , `MuOr;
   "mu_disjoint", `MuDisj;
   "mu_split"   , `MuSplit]

(* -------------------------------------------------------------------- *)

let t_pr_rewrite_low (s,dof) tc = 
  let kind = 
    try List.assoc s pr_rewrite_lemma with Not_found -> 
      tc_error !!tc "do not reconize %s as a probability lemma" s in

  let check_f dof = 
    match kind, dof with
    | `MuSplit, None -> tc_error !!tc  "argument expected for %s" s
    | `MuSplit, Some _ -> ()
    | _, Some _ -> tc_error !!tc "no argument expected for %s" s
    | _, _ -> () in
  check_f dof;

  let select = 
    match kind with 
    | `MuEq    -> select_pr_cmp (EcPath.p_equal EcCoreLib.CI_Bool.p_eq)
    | `MuSub   -> select_pr_cmp (EcPath.p_equal EcCoreLib.CI_Real.p_real_le)
    | `MuFalse -> select_pr is_false
    | `MuNot   -> select_pr is_not
    | `MuOr
    | `MuDisj  -> select_pr is_or 
    | `MuSplit -> select_pr (fun _ev -> true) in

  let select xs fp = if select xs fp then `Accept (-1) else `Continue in
  let env, _, concl = FApi.tc1_eflat tc in
  let torw =
    try
      ignore (EcMatching.FPosition.select select concl);
      tc_error !!tc "cannot find a pattern for %s" s
    with FoundPr f -> f in

  let lemma, args = 
    match kind with
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
      let ev' = (oget dof) tc torw in
      (pr_split pr.pr_mem pr.pr_fun pr.pr_args pr.pr_event ev', 0) 

  in

  let rwpt =
    { pt_head = PTCut lemma;
      pt_args = List.make args (PASub None); } in

  FApi.t_first
    (t_pr_lemma lemma)
    (t_rewrite rwpt (`LtoR, None) tc)

let t_pr_rewrite_i (s,f) tc =
  let do_ev = omap (fun f _ _ -> f) f in
  t_pr_rewrite_low (s,do_ev) tc

let t_pr_rewrite (s,f) tc = 
  let do_ev  = 
    omap (fun f tc torw ->
      let env,hyps,_ = FApi.tc1_eflat tc in
      let pr = destr_pr torw in
      let mp = EcEnv.Fun.prF_memenv EcFol.mhr pr.pr_fun env in
      let hyps = LDecl.push_active mp hyps in
      EcProofTyping.process_formula hyps f) f in
  t_pr_rewrite_low (s,do_ev) tc
