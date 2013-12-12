(* -------------------------------------------------------------------- *)
open EcUtils
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
