open EcUtils
open EcSymbols
open EcIdent
open EcPath
open EcTypes
open EcBaseLogic
open EcFol
open EcWhy3
open EcEnv

type pre_rule = rule_name EcBaseLogic.pre_rule
type pre_judgment = (rule_name, l_decl) EcBaseLogic.pre_judgment
type judgment_uc = (rule_name, l_decl) EcBaseLogic.judgment_uc

type goal = judgment_uc * int 
type goals = judgment_uc * int list

type tactic = goal -> goals 

include EcBaseLogic.Tactic

let open_juc hyps concl : judgment_uc = fst (open_juc (hyps, concl))

let close_juc juc = close_juc juc

let get_goal g = (get_open_goal g).pj_decl      
let get_hyps g = fst (get_goal g) 
let get_concl g = snd (get_goal g)

type tac_error =
  | UnknownAx      of EcPath.path 
  | NotAHypothesis of EcIdent.t 
  | ExclMidle      of form
  | And_I          of form
  | Or_I           of form
  | Imp_I          of form
  | Forall_I       of form
  | Exists_I       of form
  | Imp_E          of form
  | Forall_E       of form
  | Exists_E       of form
  | DupIdInCtxt    of EcIdent.t 
  | CanNotProve    of l_decl

exception TacError of tac_error


module PE = EcPrinting.EcDebugPP (* FIXME *)

let pp_tac_error fmt = function
  | UnknownAx p ->
      Format.fprintf fmt "Unknown axiom/lemma %a" PE.pp_path p
  | NotAHypothesis id -> 
      Format.fprintf fmt "Unknown hypothesis %s" (EcIdent.name id)
  | ExclMidle f ->
      Format.fprintf fmt "Can not applies excluded midle on %a" PE.pp_form f
  | And_I f ->
      Format.fprintf fmt "Can not applies and intro on %a" PE.pp_form f
  | Or_I f ->
      Format.fprintf fmt "Can not applies or intro on %a" PE.pp_form f
  | Imp_I f ->
      Format.fprintf fmt "Can not applies implies intro on %a" PE.pp_form f
  | Forall_I f ->
      Format.fprintf fmt "Can not applies forall intro on %a" PE.pp_form f
  | Exists_I f ->
      Format.fprintf fmt "Can not applies exists intro on %a" PE.pp_form f
  | Imp_E f ->
      Format.fprintf fmt "Can not applies implies elim on %a" PE.pp_form f  
  | Forall_E f ->
      Format.fprintf fmt "Can not applies forall elim on %a" PE.pp_form f
  | Exists_E f ->
      Format.fprintf fmt "Can not applies exists elim on %a" PE.pp_form f
  | DupIdInCtxt id -> 
      Format.fprintf fmt "Duplicate name in context %s" (EcIdent.name id)

  | CanNotProve g -> 
      Format.fprintf fmt "Can not prove %a" PE.pp_lgoal g

let _ = EcPexception.register (fun fmt exn ->
  match exn with
  | TacError e -> pp_tac_error fmt e 
  | _ -> raise exn)
      
let tacerror e = raise (TacError e)

let t_admit g = 
  let rule = { pr_name = RN_admit; pr_hyps = [] } in
  upd_rule_done g rule 

let t_hyp env id g = 
  let (hyps,concl) = get_goal g in
  let f = LDecl.lookup_hyp_by_id id hyps in
  check_alpha_equal env f concl;
  let rule = { pr_name = RN_local id; pr_hyps = [] } in
  upd_rule_done g rule

let t_glob env p tys g = 
  let f = Ax.instanciate p tys env in
  let concl = get_concl g in
  check_alpha_equal env f concl;
  let rule = { pr_name = RN_global(p,tys); pr_hyps = [] } in
  upd_rule_done g rule

let t_exc_midle env g = 
  let concl = get_concl g in
  let f1, f2 = destr_or concl in
  check_alpha_equal env f2 (f_not f1);
  let rule = { pr_name = RN_exc_midle; pr_hyps = [] } in
  upd_rule_done g rule 

let t_trivial pi env g = 
  let l_decl = get_goal g in
  if check_goal env pi l_decl then
    let rule = { pr_name = RN_prover (); pr_hyps = [] } in
    upd_rule_done g rule
  else tacerror (CanNotProve l_decl)

let t_clear id (juc,n as g) = 
  let hyps,concl = get_goal g in
  (* FIXME check that id is not in concl *)
  let hyps = LDecl.clear id hyps in
  let juc,n1 = new_goal juc (hyps,concl) in
  let rule = { pr_name = RN_clear id; pr_hyps = [n1] } in
  upd_rule (juc,n) rule
  
let get_equality f = 
  match f.f_node with
  | Fapp({f_node = Fop(op,_)},[f1;f2]) when 
      EcPath.p_equal op EcCoreLib.p_eq || EcPath.p_equal op EcCoreLib.p_iff ->
      f1, f2
  | _ -> assert false (* FIXME error message *)

let t_eq env feq (id,p) (juc,n as g) = 
  let t, u = get_equality feq in
  let hyps, concl = get_goal g in
  check_alpha_equal env (Fsubst.subst_local id u p) concl;
  let juc,n1 = new_goal juc (hyps, feq) in
  let juc,n2 = new_goal juc (hyps, Fsubst.subst_local id t p) in
  let rule = { pr_name = RN_eq(id,p); pr_hyps = [n1;n2] } in
  upd_rule (juc,n) rule 

let t_and_intro (juc,n as g) = 
  let hyps,concl = get_goal g in
  let a,b = destr_and concl in
  let juc, n1 = new_goal juc (hyps, a) in
  let juc, n2 = new_goal juc (hyps, b) in
  let rule = { pr_name = RN_and_I; pr_hyps = [n1;n2] } in
  upd_rule (juc,n) rule

let t_or_intro side (juc,n as g) = 
  let hyps,concl = get_goal g in
  let a,b = destr_or concl in
  let juc, n1 = new_goal juc (hyps, if side then a else b) in
  let rule = { pr_name = RN_or_I side; pr_hyps = [n1] } in
  upd_rule (juc,n) rule

let t_imp_intro id (juc,n as g) = 
  let hyps,concl = get_goal g in
  let a,b = destr_imp concl in
  let hyps = LDecl.add_local id (LD_hyp a) hyps in
  let juc, n1 = new_goal juc (hyps, b) in
  let rule = { pr_name = RN_imp_I; pr_hyps = [n1] } in
  upd_rule (juc,n) rule

let t_forall_intro id (juc,n as g) = 
  let hyps,concl = get_goal g in
  let id',ty,b = destr_forall1 concl in
  let hyps = LDecl.add_local id (LD_var(ty,None)) hyps in
  let juc, n1 = new_goal juc (hyps, Fsubst.subst_local id' (f_local id ty) b) in
  let rule = { pr_name = RN_forall_I; pr_hyps = [n1] } in
  upd_rule (juc,n) rule

let t_exists_intro env t (juc,n as g) = 
  let hyps,concl = get_goal g in
  let id',ty,b = destr_exists1 concl in
  check_type env t.f_ty ty;
  let juc, n1 = new_goal juc (hyps, Fsubst.subst_local id' t b) in
  let rule = { pr_name = RN_exists_I t; pr_hyps = [n1] } in
  upd_rule (juc,n) rule

let t_and_elim ff (juc,n as g) = 
  let hyps,concl = get_goal g in
  let a,b = destr_and ff in
  let concl = f_imp a (f_imp b concl) in
  let juc, n1 = new_goal juc (hyps, ff) in
  let juc, n2 = new_goal juc (hyps, concl) in
  let rule = { pr_name = RN_and_E; pr_hyps = [n1;n2] } in
  upd_rule (juc,n) rule

let t_or_elim ff (juc,n as g) = 
  let hyps,concl = get_goal g in
  let a,b = destr_or ff in
  let juc, n1 = new_goal juc (hyps, ff) in
  let juc, n2 = new_goal juc (hyps, f_imp a concl) in
  let juc, n3 = new_goal juc (hyps, f_imp b concl) in
  let rule = { pr_name = RN_or_E; pr_hyps = [n1;n2;n3] } in
  upd_rule (juc,n) rule

let t_imp_elim ff (juc,n as g) = 
  let hyps,concl = get_goal g in
  let a,b = destr_imp ff in
  let juc, n1 = new_goal juc (hyps, ff) in
  let juc, n2 = new_goal juc (hyps, a) in
  let juc, n3 = new_goal juc (hyps, f_imp b concl) in
  let rule = { pr_name = RN_imp_E; pr_hyps = [n1;n2;n3] } in
  upd_rule (juc,n) rule

let t_forall_elim env ff t (juc,n as g) = 
  let hyps,concl = get_goal g in
  let x,ty,p = destr_forall1 ff in
  check_type env t.f_ty ty;
  let p = Fsubst.subst_local x t p in
  let juc, n1 = new_goal juc (hyps, ff) in
  let juc, n2 = new_goal juc (hyps, f_imp p concl) in
  let rule = { pr_name = RN_forall_E t; pr_hyps = [n1;n2] } in
  upd_rule (juc,n) rule 

let t_exists_elim ff (juc,n as g) = 
  let hyps,concl = get_goal g in
  let x, ty, p = destr_exists1 ff in
  (* FIXME rename x, or check that x is not in concl *)
  let concl = f_forall [x,ty] (f_imp p concl) in
  let juc, n1 = new_goal juc (hyps, ff) in
  let juc, n2 = new_goal juc (hyps, concl) in
  let rule = { pr_name = RN_exists_E; pr_hyps = [n1;n2] } in
  upd_rule (juc,n) rule

let find_in_hyps env f hyps = 
  let test k = 
    try 
      let _, f' = LDecl.get_hyp k in
      check_alpha_equal env f f'; true
    with _ -> false in
  fst (List.find test hyps.h_local)


  
  
  

  
  






