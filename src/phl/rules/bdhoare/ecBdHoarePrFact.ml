(* -------------------------------------------------------------------- *)
open EcUtils
open EcAst
open EcFol
open EcEnv

open EcCoreGoal
open EcLowGoal

module Mid = EcIdent.Mid

(* -------------------------------------------------------------------- *)
(* The facts of the [pr-fact] rule: an axiom schema of facts on the
   probabilities [Pr[f(args) @ &m : _]] of one procedure, from one
   initial memory and with the same arguments. Each schema carries its
   resolved parameters: the events (in the final memory of [f]) and the
   binders it introduces, so that the fact is a deterministic function of
   the node. *)
type pr_fact =
  | PFMuEq       of ss_inv * ss_inv
  | PFMuSub      of ss_inv * ss_inv
  | PFMuFalse    of memory
  | PFMuNot      of ss_inv
  | PFMuOr       of [`Sym | `Asym] * ss_inv * ss_inv
  | PFMuDisj     of [`Sym | `Asym] * ss_inv * ss_inv
  | PFMuSplit    of ss_inv * ss_inv
  | PFMuGe0      of ss_inv
  | PFMuLe1      of ss_inv
  | PFMuSum      of ss_inv * EcIdent.t
  | PFMu1LeEqMu1 of ss_inv * form * EcIdent.t * form
  | PFMuHasLe    of ss_inv * EcIdent.t

(* Parameters of the rule: already resolved and typed, the same record is
   the rule argument and the node payload. *)
type pr_fact_node = {
  pfn_mem  : memory;    (* initial memory &m *)
  pfn_fun  : EcPath.xpath;
  pfn_args : form;
  pfn_fact : pr_fact;
}

type EcCoreGoal.rule += RBdHoarePrFact of pr_fact_node

exception InvalidPrFact of string

(* -------------------------------------------------------------------- *)
let p_List = [EcCoreLib.i_top; "List"]
let p_BRA  = [EcCoreLib.i_top; "StdBigop"; "Bigreal"; "BRA"]
let p_list_has = EcPath.fromqsymbol (p_List, "has")
let p_BRA_big = EcPath.fromqsymbol (p_BRA, "big")

(* [has P s], [s] not depending on the memory of the event. *)
let destr_ev_has (ev : ss_inv) =
  let m = ev.m in
  match ev.inv.f_node with
  | Fapp ({ f_node = Fop(op, [ty_elem]) }, [f_f; f_l]) ->
      if EcPath.p_equal p_list_has op && not (Mid.mem m f_l.f_fv) then
        Some(ty_elem, {m;inv=f_f}, f_l)
      else None
  | _ -> None

(* -------------------------------------------------------------------- *)
(* The schemas. *)
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

let pr_false pr_m f args m =
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

let pr_sum env pr_m f args ev x =
  let prf = EcEnv.Fun.by_xpath f env in
  let xty = prf.f_sig.fs_ret in
  let m = ev.m in
  let fx = {m;inv=f_local x xty} in
  let prx =
    let event =
      map_ss_inv2 f_and_simpl
        ev
        (map_ss_inv2 f_eq (f_pvar EcTypes.pv_res xty ev.m) fx)
    in f_pr pr_m f args event in

  let prx =
    EcFol.f_app
      (EcFol.f_op EcCoreLib.CI_Sum.p_sum [ xty ]
         (EcTypes.tfun (EcTypes.tfun xty EcTypes.treal) EcTypes.treal))
      [ EcFol.f_lambda [ (x, GTty xty) ] prx ]
      EcTypes.treal
  in

  f_eq (f_pr pr_m f args ev) prx

let pr_mu1_le_eq_mu1 pr_m f args resv k fresh_id d =
  let m = resv.m in
  let kfresh = f_local fresh_id k.f_ty in
  let f_ll = f_bdHoareF {m;inv=f_true} f {m;inv=f_true} FHeq {m;inv=f_r1}
  and f_le_mu1 = f_forall [ (fresh_id, gtty k.f_ty) ]
    (f_real_le (f_pr pr_m f args {m;inv=f_eq resv.inv kfresh}) (f_mu_x d kfresh))
  and concl =
    f_eq (f_pr pr_m f args {m;inv=f_eq resv.inv k}) (f_mu_x d k) in
  f_imp f_ll (f_imp f_le_mu1 concl)

(*
 lemma mu_has_le ['a 'b] (P : 'a -> 'b -> bool) (d : 'a distr) (s : 'b list) :
   mu d (fun a => has (P a) s) <= BRA.big predT (fun b => mu d (fun a => P a b)) s.
   Pr [f(args)@ &m : has Pa s] <= BRA.big predT (fun b => Pr [f(args) &m : Pa b]) s
*)
let pr_has_le pr_m f args ev ty_elem f_f f_l idx =
  let x = f_local idx ty_elem in
  let pr_event = map_ss_inv1 (fun f -> f_app f [x] EcTypes.tbool) f_f in
  let f_pr1 = f_pr pr_m f args pr_event in
  let f_fsum = f_lambda [idx, GTty ty_elem] f_pr1 in
  let f_sum =
    f_app (f_op p_BRA_big [ty_elem] EcTypes.treal) [f_predT ty_elem; f_fsum; f_l] EcTypes.treal in
  f_real_le (f_pr pr_m f args ev) f_sum

(* -------------------------------------------------------------------- *)
(* Pure core shared by the rule and its checker: the fact of the node.
   The side conditions of the schemas (the events sharing one memory, the
   constants not depending on it, the binders not captured) are checked
   here, raising [InvalidPrFact], so the checker re-validates them. *)
let pr_fact (hyps : LDecl.hyps) (n : pr_fact_node) : form =
  let env  = LDecl.toenv hyps in
  let fail = fun msg -> raise (InvalidPrFact msg) in
  let pr_m, f, args = n.pfn_mem, n.pfn_fun, n.pfn_args in
  let same_mem (p1 : ss_inv) (p2 : ss_inv) =
    if not (EcIdent.id_equal p1.m p2.m) then
      fail "the events are not in the same memory" in
  let fresh x fs =
    if List.exists (fun (g : form) -> Mid.mem x g.f_fv) fs then
      fail "the bound variable is not fresh" in

  match n.pfn_fact with
  | PFMuEq (p1, p2) ->
      same_mem p1 p2; pr_eq env pr_m f args p1 p2
  | PFMuSub (p1, p2) ->
      same_mem p1 p2; pr_sub env pr_m f args p1 p2
  | PFMuFalse m ->
      pr_false pr_m f args m
  | PFMuNot p ->
      pr_not pr_m f args p
  | PFMuOr (asym, p1, p2) ->
      let por = match asym with `Asym -> f_ora | `Sym -> f_or in
      same_mem p1 p2; pr_or pr_m f args (map_ss_inv2 por) p1 p2
  | PFMuDisj (asym, p1, p2) ->
      let por = match asym with `Asym -> f_ora | `Sym -> f_or in
      same_mem p1 p2; pr_disjoint env pr_m f args (map_ss_inv2 por) p1 p2
  | PFMuSplit (ev1, ev2) ->
      same_mem ev1 ev2; pr_split pr_m f args ev1 ev2
  | PFMuGe0 ev ->
      pr_ge0 pr_m f args ev
  | PFMuLe1 ev ->
      pr_le1 pr_m f args ev
  | PFMuSum (ev, x) ->
      fresh x [args; ev.inv]; pr_sum env pr_m f args ev x
  | PFMu1LeEqMu1 (resv, k, k', d) ->
      if Mid.mem resv.m k.f_fv then
        fail "the value depends on the memory of the event";
      fresh k' [args; resv.inv; d];
      pr_mu1_le_eq_mu1 pr_m f args resv k k' d
  | PFMuHasLe (ev, x) ->
      let ty_elem, f_f, f_l =
        match destr_ev_has ev with
        | Some x -> x
        | None -> fail "the event is not of the form [has P s]" in
      fresh x [args; f_f.inv];
      pr_has_le pr_m f args ev ty_elem f_f f_l x

(* The rule has no premise: the goal must be the fact of the node. *)
let bdhoare_pr_fact_subgoals (hyps : LDecl.hyps) (concl : form) (n : pr_fact_node) =
  if not (f_equal concl (pr_fact hyps n)) then
    raise (InvalidPrFact "the goal is not the fact");
  []

(* -------------------------------------------------------------------- *)
(* Rule (TCB). *)
let t_bdhoare_pr_fact (n : pr_fact_node) (tc : tcenv1) =
  let subgoals =
    try  bdhoare_pr_fact_subgoals (FApi.tc1_hyps tc) (FApi.tc1_goal tc) n
    with InvalidPrFact msg -> tc_error !!tc "Pr-rewrite: %s" msg in
  FApi.xrule1 tc (RBdHoarePrFact n) subgoals

(* -------------------------------------------------------------------- *)
let () =
  register_rule_checker
    (function
     | RBdHoarePrFact n ->
         Some (EcPlRecheck.checker_of "bdhoare-pr-fact" (fun _ concl -> concl)
                 (fun hyps concl -> bdhoare_pr_fact_subgoals hyps concl n))
     | _ -> None)

(* ==================================================================== *)
(* Derived (no proof-node): [rewrite Pr], rewriting with a fact of the
   rule. *)
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
        match destr_ev_has pr.pr_event with
        | Some (_, _, f_l) when
          Mid.set_disjoint f_l.f_fv sid ->
            raise (FoundPr f_pr)
        | _ -> false
      else false
  | _ -> false

let is_eq_w_const_rhs (f: ss_inv): bool =
  try
    let _, rhs = destr_eq f.inv in
    not (Mid.mem f.m rhs.f_fv)
  with DestrError _ -> false

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
(* [dof tc torw ty] is the argument of the lemma ([mu_split] and
   [mu1_le_eq_mu1]), for the selected probability [torw]. *)
let t_pr_rewrite_low (s, (dof: (_ -> _ -> _ -> ss_inv) option)) tc =
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
  let hyps, concl = FApi.tc1_flat tc in
  let torw =
    try
      ignore (EcMatching.FPosition.select select concl);
      tc_error !!tc "Pr-rewrite: cannot find a pattern for `%s`" s
    with FoundPr f -> f in

  let node pr fact =
    { pfn_mem = pr.pr_mem; pfn_fun = pr.pr_fun; pfn_args = pr.pr_args;
      pfn_fact = fact; } in

  let node, args =
    match kind with
    | `Mu1LeEqMu1 ->
      let pr = destr_pr torw in
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
      (node pr (PFMu1LeEqMu1 (resv, k.inv, k_id, d.inv)), 2)

    | (`MuEq | `MuSub as kind) -> begin
      match torw.f_node with
      | Fapp(_, [{f_node = Fpr pr1 };
                 {f_node = Fpr pr2 };])
        -> begin
          let ev1 = pr1.pr_event in
          let ev2 = EcSubst.ss_inv_rebind pr2.pr_event ev1.m in
          match kind with
          | `MuEq  -> (node pr1 (PFMuEq  (ev1, ev2)), 1)
          | `MuSub -> (node pr1 (PFMuSub (ev1, ev2)), 1)
        end
      | _ -> assert false
      end

    | `MuFalse ->
        (node (destr_pr torw) (PFMuFalse (EcIdent.create "&hr")), 0)

    | `MuNot ->
        let pr = destr_pr torw in
        (node pr (PFMuNot (map_ss_inv1 destr_not pr.pr_event)), 0)

    | (`MuOr | `MuDisj) as kind ->
        let pr = destr_pr torw in
        let asym = fst (destr_or_r pr.pr_event.inv) in
        let (ev1, ev2) = map_ss_inv_destr2 (fun prev -> snd (destr_or_r prev)) pr.pr_event in
        begin match kind with
        | `MuOr   -> (node pr (PFMuOr   (asym, ev1, ev2)), 0)
        | `MuDisj -> (node pr (PFMuDisj (asym, ev1, ev2)), 1)
        end

    | `MuSplit ->
      let pr = destr_pr torw in
      let ev' = EcSubst.ss_inv_rebind ((oget dof) tc torw EcTypes.tbool) pr.pr_event.m in
      (node pr (PFMuSplit (pr.pr_event, ev')), 0)

    | `MuGe0 -> begin
      match torw.f_node with
      | Fapp({f_node = Fop _}, [_; {f_node = Fpr pr}]) ->
            (node pr (PFMuGe0 pr.pr_event), 0)
      | _ -> assert false
      end

    | `MuLe1 -> begin
      match torw.f_node with
      | Fapp({f_node = Fop _}, [{f_node = Fpr pr}; _]) ->
            (node pr (PFMuLe1 pr.pr_event), 0)
      | _ -> assert false
      end

    | `MuSum ->
        let pr = destr_pr torw in
        (node pr (PFMuSum (pr.pr_event, EcIdent.create "x")), 0)

    | `MuHasLe ->
        let pr = destr_pr torw in
        (node pr (PFMuHasLe (pr.pr_event, EcIdent.create "x")), 0)

  in

  let lemma = pr_fact hyps node in
  let rwpt = EcCoreGoal.ptcut ~args:(List.make args (PASub None)) lemma in

  FApi.t_first
    (t_bdhoare_pr_fact node)
    (t_rewrite rwpt (`LtoR, None) tc)

let t_pr_rewrite (s, f) tc =
  let do_ev = omap (fun f _ _ _ -> f) f in
  t_pr_rewrite_low (s, do_ev) tc

(* ==================================================================== *)
(* Elaboration: [rewrite Pr s [f]], the argument typed in the final
   memory of the selected probability. *)
let process_pr_rewrite (s, f) tc =
  let to_env f tc torw ty =
    let env, hyps, _ = FApi.tc1_eflat tc in
    let pr = destr_pr torw in
    let m = EcIdent.create "&hr" in
    let mp = EcEnv.Fun.prF_memenv m pr.pr_fun env in
    let hyps = LDecl.push_active_ss mp hyps in
    {m;inv=EcProofTyping.process_form hyps f ty}
  in
  t_pr_rewrite_low (s, omap to_env f) tc
