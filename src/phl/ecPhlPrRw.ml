(* --------------------------------------------------------------------
 * Copyright (c) - 2012-2014 - IMDEA Software Institute and INRIA
 * Distributed under the terms of the CeCILL-C license
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

(* -------------------------------------------------------------------- *)
exception FoundPr of form

let select_pr on_ev sid f = 
  match f.f_node with
  | Fpr(_,_,_,ev) -> 
      if   on_ev ev && Mid.set_disjoint f.f_fv sid
      then raise (FoundPr f)
      else false
  | _ -> false

let select_pr_cmp on_cmp sid f = 
  match f.f_node with
  | Fapp({f_node = Fop(op,_)},
         [{f_node = Fpr(m1,f1,arg1,_)};
          {f_node = Fpr(m2,f2,arg2,_)}]) ->

      if    on_cmp op
         && EcIdent.id_equal m1 m2
         && EcPath.x_equal f1 f2
         && f_equal arg1 arg2
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
   "mu_disjoint", `MuDisj]

(* -------------------------------------------------------------------- *)
let t_pr_rewrite s tc = 
  let kind = 
    try List.assoc s pr_rewrite_lemma with Not_found -> 
      tc_error !!tc "do not reconize %s as a probability lemma" s in
  let select = 
    match kind with 
    | `MuEq    -> select_pr_cmp (EcPath.p_equal EcCoreLib.p_eq)
    | `MuSub   -> select_pr_cmp (EcPath.p_equal EcCoreLib.p_real_le)
    | `MuFalse -> select_pr is_false
    | `MuNot   -> select_pr is_not
    | `MuOr
    | `MuDisj  -> select_pr is_or in

  let select xs _ fp = if select xs fp then `Accept (-1) else `Continue in
  let env, _, concl = FApi.tc1_eflat tc in
  let torw =
    try
      ignore (EcMatching.FPosition.select select concl);
      tc_error !!tc "can not find a pattern for %s" s
    with FoundPr f -> f in

  let lemma, args = 
    match kind with
    | (`MuEq | `MuSub as kind) -> begin
      match torw.f_node with
      | Fapp(_, [{f_node = Fpr(m,f,args,ev1)};
                 {f_node = Fpr(_,_,_,ev2)}])
        -> begin
          match kind with
          | `MuEq  -> (pr_eq  env m f args ev1 ev2, 1)
          | `MuSub -> (pr_sub env m f args ev1 ev2, 1)
        end
      | _ -> assert false
      end

    | `MuFalse ->
        let m,f,args,_ = destr_pr torw in (pr_false m f args, 0)

    | `MuNot ->
        let m,f,args,ev = destr_pr torw in
        let ev = destr_not ev in
          (pr_not m f args ev, 0)

    | `MuOr ->
        let m,f,args,ev = destr_pr torw in
        let asym,ev1,ev2 = destr_or_kind ev in
          (pr_or m f args (if asym then f_ora else f_or) ev1 ev2, 0)

    | `MuDisj ->
        let m,f,args,ev = destr_pr torw in
        let asym,ev1,ev2 = destr_or_kind ev in
          (pr_disjoint env m f args (if asym then f_ora else f_or) ev1 ev2, 1)
  in

  let rwpt =
    { pt_head = PTCut lemma;
      pt_args = List.create args (PASub None); } in

  FApi.t_first
    (t_pr_lemma lemma)
    (t_rewrite rwpt (`LtoR, None) tc)
