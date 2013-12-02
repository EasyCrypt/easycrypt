(* -------------------------------------------------------------------- *)
open EcUtils
open EcTypes
open EcFol
open EcEnv
open EcBaseLogic
open EcLogic
module Mid = EcIdent.Mid

(* -------------------------------------------------------------------- *)
class rn_hl_pr_lemma =
object
  inherit xrule "[hl] pr-lemma"
end

let rn_hl_pr_lemma =
  RN_xtd (new rn_hl_pr_lemma)

(* -------------------------------------------------------------------- *)
let t_pr_lemma lemma g = 
  let concl = get_concl g in
    assert (f_equal concl lemma);
    prove_goal_by [] rn_hl_pr_lemma g

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
         && List.all2 f_equal arg1 arg2
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
let t_pr_rewrite s g = 
  let kind = 
    try List.assoc s pr_rewrite_lemma with Not_found -> 
      tacuerror "Do not reconize %s as a probability lemma" s in
  let select = 
    match kind with 
    | `MuEq    -> select_pr_cmp (EcPath.p_equal EcCoreLib.p_eq)
    | `MuSub   -> select_pr_cmp (EcPath.p_equal EcCoreLib.p_real_le)
    | `MuFalse -> select_pr is_false
    | `MuNot   -> select_pr is_not
    | `MuOr
    | `MuDisj  -> select_pr is_or in

  let select xs fp = if select xs fp then Some (-1) else None in
  let env, _, concl = get_goal_e g in
  let torw =
    try
      ignore (EcMetaProg.FPosition.select select concl);
      tacuerror "can not find a pattern for %s" s
    with FoundPr f -> f in

  let lemma, args = 
    match kind with
    | (`MuEq | `MuSub as kind) -> begin
      match torw.f_node with
      | Fapp(_, [{f_node = Fpr(m,f,args,ev1)};
                 {f_node = Fpr(_,_,_,ev2)}])
        -> begin
          match kind with
          | `MuEq  -> (pr_eq  env m f args ev1 ev2, [AAnode])
          | `MuSub -> (pr_sub env m f args ev1 ev2, [AAnode])
        end
      | _ -> assert false
      end

    | `MuFalse ->
        let m,f,args,_ = destr_pr torw in (pr_false m f args, [])

    | `MuNot ->
        let m,f,args,ev = destr_pr torw in
        let ev = destr_not ev in
          (pr_not m f args ev, [])

    | `MuOr ->
        let m,f,args,ev = destr_pr torw in
        let asym,ev1,ev2 = destr_or_kind ev in
          (pr_or m f args (if asym then f_ora else f_or) ev1 ev2, [])

    | `MuDisj ->
        let m,f,args,ev = destr_pr torw in
        let asym,ev1,ev2 = destr_or_kind ev in
          (pr_disjoint env m f args (if asym then f_ora else f_or) ev1 ev2, [AAnode])
  in
    t_on_first
      (t_pr_lemma lemma)
      (t_rewrite_form `LtoR lemma args g)


(* -------------------------------------------------------------------- *)
class rn_bdhoare_split =
object
  inherit xrule "[hl] bdhoare_split"
end

let rn_bdhoare_split =
  RN_xtd (new rn_bdhoare_split)

let t_bdhoare_split_bop 
    get_bdh mk_bdh destr_bop mk_bop
    b1 b2 b3 g =
  let concl = get_concl g in
  let bh,po,cmp,bd = get_bdh concl in
  let a,b = destr_bop po in
  let g1 = mk_bdh bh a cmp b1 in
  let g2 = mk_bdh bh b cmp b2 in
  let g3 = mk_bdh bh (mk_bop a b) (hoarecmp_opp cmp) b3 in
  let nb = f_real_sub (f_real_add b1 b2) b3 in
  assert (f_equal nb bd);
  prove_goal_by [g1;g2;g3] rn_bdhoare_split g

let t_bdhoare_split_bop_conseq 
    t_conseq_bd
    get_bdh mk_bdh destr_bop mk_bop
    b1 b2 b3 g =
  let _,_,cmp,b = get_bdh (get_concl g) in
  let nb = f_real_sub (f_real_add b1 b2) b3 in
  let t_main = 
    t_bdhoare_split_bop get_bdh mk_bdh destr_bop mk_bop
      b1 b2 b3 in
  if f_equal nb b then t_main g
  else t_seq_subgoal (t_conseq_bd cmp nb) [t_id None; t_main] g

let bdhoare_kind g = 
  match (get_concl g).f_node with
  | FbdHoareS _ -> true
  | FbdHoareF _ -> false
  | _           -> tacuerror "The conclusion should be a bdhoare judgment"

let gen_S = 
  let get_bdh g = 
    let bh = EcCorePhl.t_as_bdHoareS g in
    bh,bh.bhs_po, bh.bhs_cmp, bh.bhs_bd in
  let mk_bdh bh po cmp b = 
    f_bdHoareS_r { bh with bhs_po = po; bhs_cmp = cmp; bhs_bd = b } in
  fun tac -> tac EcPhlConseq.t_bdHoareS_conseq_bd get_bdh mk_bdh 

let gen_F = 
  let get_bdh g = 
    let bh = EcCorePhl.t_as_bdHoareF g in
    bh,bh.bhf_po, bh.bhf_cmp, bh.bhf_bd in   
  let mk_bdh bh po cmp b = 
    f_bdHoareF bh.bhf_pr bh.bhf_f po cmp b in
  fun tac -> tac EcPhlConseq.t_bdHoareF_conseq_bd get_bdh mk_bdh

let destr_and f = 
  try destr_and f 
  with DestrError _ -> tacuerror "The postcondition should be a conjunction"

let t_bdhoareS_and = gen_S t_bdhoare_split_bop_conseq destr_and f_or 
let t_bdhoareF_and = gen_F t_bdhoare_split_bop_conseq destr_and f_or 
let t_bdhoare_and b1 b2 b3 g =
  if bdhoare_kind g then t_bdhoareS_and b1 b2 b3 g
  else t_bdhoareF_and b1 b2 b3 g

let destr_or f = 
  try destr_or f 
  with DestrError _ -> tacuerror "The postcondition should be a disjunction"

let t_bdhoareS_or = gen_S t_bdhoare_split_bop_conseq destr_or f_and 
let t_bdhoareF_or = gen_F t_bdhoare_split_bop_conseq destr_or f_and 
let t_bdhoare_or b1 b2 b3 g = 
  if bdhoare_kind g then t_bdhoareS_or b1 b2 b3 g
  else t_bdhoareF_or b1 b2 b3 g

let t_bdhoare_split_not 
    get_bdh mk_bdh 
    b1 b2 g =
  let concl = get_concl g in
  let bh,po,cmp,bd = get_bdh concl in
  let g1 = mk_bdh bh f_true cmp b1 in
  let g2 = mk_bdh bh (f_not_simpl po) (hoarecmp_opp cmp) b2 in
  let nb = f_real_sub b1 b2 in
  assert (f_equal nb bd);
  prove_goal_by [g1;g2] rn_bdhoare_split g

let t_bdhoare_split_not_conseq 
    t_conseq_bd get_bdh mk_bdh 
    b1 b2 g =
  let _,_,cmp,b = get_bdh (get_concl g) in
  let nb = f_real_sub b1 b2 in
  let t_main = t_bdhoare_split_not get_bdh mk_bdh b1 b2  in
  if f_equal nb b then t_main g
  else t_seq_subgoal (t_conseq_bd cmp nb) [t_id None; t_main] g

let t_bdhoareS_not = gen_S t_bdhoare_split_not_conseq 
let t_bdhoareF_not = gen_F t_bdhoare_split_not_conseq 
let t_bdhoare_not b1 b2 g =
   if bdhoare_kind g then t_bdhoareS_not b1 b2 g 
   else t_bdhoareF_not b1 b2 g

open EcParsetree

let t_rewrite_glob s pqs = 
  let rwarg = (RWRw (s, None, None, [{ fp_kind = FPNamed(pqs,None); fp_args = []; }])) in
    EcHiLogic.process_rewrite pqs.EcLocation.pl_loc [(None, rwarg)]

let t_rewrite_logic s x = 
  let loc = EcLocation._dummy in
  let p = EcLocation.mk_loc loc ([EcCoreLib.id_top; "Logic"],x) in
  t_rewrite_glob s p 
  
let process_bdhoare_split info g =
  let hyps, concl = get_goal g in
  let (penv, qenv), pr, po = 
    match concl.f_node with
    | FbdHoareS bhs -> 
      let hyps = LDecl.push_active bhs.bhs_m hyps in
      (hyps, hyps), bhs.bhs_pr, bhs.bhs_po
    | FbdHoareF bhf -> (LDecl.hoareF bhf.bhf_f hyps), bhf.bhf_pr, bhf.bhf_po
    | _ -> tacuerror "The conclusion should be a bdhoare judgment" in
  match info with
  | EcParsetree.BDH_split_bop(b1,b2,b3) ->
    let t =
      if is_and po then t_bdhoare_and
      else if is_or po then t_bdhoare_or
      else tacuerror 
        "The postcondition should be a conjunction or a disjunction" in
    let b1 = EcCoreHiLogic.process_form penv b1 treal in
    let b2 = EcCoreHiLogic.process_form penv b2 treal in
    let b3 = match b3 with
      | None -> f_r0
      | Some b3 -> EcCoreHiLogic.process_form penv b3 treal in
    t b1 b2 b3 g
  | EcParsetree.BDH_split_or_case(b1,b2,f) -> 
    let b1 = EcCoreHiLogic.process_form penv b1 treal in
    let b2 = EcCoreHiLogic.process_form penv b2 treal in
    let f  = EcCoreHiLogic.process_form qenv f tbool in
    let t_conseq po lemma tac =
      t_seq_subgoal (EcPhlConseq.t_conseq pr po)
        [EcLogic.t_true;
         EcLogic.t_lseq [
           EcLogic.t_intros_i [EcIdent.create "_"];
           t_rewrite_logic `LtoR lemma;
           t_true ];
         tac] in
    t_conseq (f_or (f_and f po) (f_and (f_not f) po)) "orDandN"
      (EcLogic.t_seq_subgoal (t_bdhoare_or b1 b2 f_r0)
         [t_id None;
          t_id None;
          t_id None;
          t_conseq f_false "andDorN" EcPhlTrivial.t_trivial]) g
    
  | EcParsetree.BDH_split_not (b1, b2) ->
    let b1 = match b1 with
      | None -> f_r1
      | Some b1 -> EcCoreHiLogic.process_form penv b1 treal in
    let b2 = EcCoreHiLogic.process_form penv b2 treal in
    t_bdhoare_not b1 b2 g
    
      
    
      


