(* -------------------------------------------------------------------- *)
open EcLocation
open EcUtils
open EcMaps
open EcSymbols
open EcIdent
open EcPath
open EcCoreLib
open EcTypes
open EcFol
open EcBaseLogic
open EcEnv
open EcReduction
open EcEctoField

type pre_judgment = {
  pj_decl : l_decl;
  pj_rule : (bool * int rule) option;
}

type judgment_uc = {
  juc_count : int;
  juc_map   : pre_judgment Mint.t;
}

type goals  = judgment_uc * int list
type goal   = judgment_uc * int 
type tactic = goal -> goals 

let new_goal juc decl =
  let n = juc.juc_count in
  let pj = { pj_decl = decl; pj_rule = None; } in
  let juc = 
    { juc_count = n + 1;
      juc_map   = Mint.add n pj juc.juc_map } in
  juc, n
        
let open_juc decl = 
  fst (new_goal { juc_count = 0; juc_map = Mint.empty } decl)
     
let get_pj (juc,n) =
  try Mint.find n juc.juc_map 
  with Not_found -> raise (UnknownSubgoal n)

let get_open_goal (juc,n) = 
  let g = get_pj (juc,n) in
  if g.pj_rule <> None then raise (NotAnOpenGoal (Some n));
  g
        
let upd_juc_map juc n pj = 
  { juc with juc_map = Mint.add n pj juc.juc_map }
    
let upd_done juc =
  let is_done juc = function
    | RA_node n ->
        begin match (get_pj (juc,n)).pj_rule with
        | Some(true, _) -> true
        | _ -> false 
        end
    | _ -> true in
  let rec upd juc n =
    let pj = get_pj (juc, n) in
    match pj.pj_rule with
    | None | Some(true, _) -> juc
    | Some(false,r) ->
        let juc = List.fold_left upd_arg juc r.pr_hyps in
        if List.for_all (is_done juc) r.pr_hyps then 
          upd_juc_map juc n { pj with pj_rule = Some(true,r)}
        else juc 
  and upd_arg juc = function
    | RA_node n -> upd juc n
    | _ -> juc in
  upd juc 0

let get_first_goal juc = 
  let rec aux n = 
    let pj = get_pj (juc, n) in
    match pj.pj_rule with
    | None -> juc, n 
    | Some(d, r) -> if d then raise (NotAnOpenGoal None) else auxs r.pr_hyps
  and auxs ns = 
    match ns with
    | [] -> raise (NotAnOpenGoal None) 
    | RA_node n :: ns -> (try aux n with _ -> auxs ns)
    | _ :: ns -> auxs ns in
  aux 0

let find_all_goals juc = 
  let juc = upd_done juc in
  let rec aux ns n = 
    let pj = get_pj (juc, n) in
    match pj.pj_rule with
    | None -> n :: ns
    | Some(d, r) -> if d then ns else List.fold_left auxa ns r.pr_hyps 
  and auxa ns = function
    | RA_node n -> aux ns n
    | _ -> ns in
  juc, List.rev (aux [] 0)

let close_juc juc =
  let rec close n = 
    let pj = get_pj (juc,n) in
    let hyps,concl = pj.pj_decl in
    let rule = 
      match pj.pj_rule with
      | None -> raise (StillOpenGoal n)
      | Some (_,r) ->
        { pr_name = r.pr_name;
          pr_hyps = List.map close_arg r.pr_hyps } in
    { j_decl = hyps, concl;
      j_rule = rule }
  and close_arg = function
    | RA_form f -> RA_form f
    | RA_id id  -> RA_id id
    | RA_mp mp  -> RA_mp mp
    | RA_node n -> RA_node (close n) in
  close 0

let upd_rule d pr (juc,n as g) = 
  let pj = get_open_goal g in
  let sg = List.pmap (function RA_node n -> Some n | _ -> None) pr.pr_hyps in
  upd_juc_map juc n { pj with pj_rule = Some(d, pr) }, sg


let upd_rule_done = upd_rule true
let upd_rule      = upd_rule false

let t_id msg (juc,n) =
  oiter msg (fun x -> Printf.fprintf stderr "DEBUG: %s\n%!" x);
  (juc, [n])

let t_on_goals t (juc,ln) = 
  let juc,ln = 
    List.fold_left (fun (juc,ln) n ->
      let juc,ln' = t (juc,n) in
      juc,List.rev_append ln' ln) (juc,[]) ln in
  juc,List.rev ln
        
let t_seq t1 t2 g = t_on_goals t2 (t1 g)
        
let rec t_lseq lt = 
  match lt with
  | [] -> t_id None
  | t1::lt -> t_seq t1 (t_lseq lt)

let t_subgoal lt (juc,ln) =
  let len1 = List.length lt in
  let len2 = List.length ln in
  if len1 <> len2 then raise (InvalidNumberOfTactic(len2, len1));
  let juc, ln = 
    List.fold_left2 (fun (juc,ln) t n ->
      let juc, ln' = t (juc, n) in
      juc, List.rev_append ln' ln) (juc,[]) lt ln in
  juc, List.rev ln

let t_on_nth t n (juc,ln) = 
  let r,n,l = try List.split_n n ln with _ -> assert false in
  let juc,ln = t (juc,n) in
  juc, List.rev_append r (List.append ln l)
        
let t_on_first t (_,ln as gs) =
  assert (ln <> []);
  t_on_nth t 0 gs 
        
let t_on_last t (_,ln as gs) =
  assert (ln <> []);
  t_on_nth t (List.length ln - 1) gs 

let t_seq_subgoal t lt g = t_subgoal lt (t g)

let t_try_base t g =
  (* FIXME: catch only tactics releated exceptions *)
  try `Success (t g) with e -> `Failure e

let t_try t g =
  match t_try_base t g with
  | `Failure _ -> t_id None g
  | `Success g -> g

let t_or t1 t2 g = 
  match t_try_base t1 g with
  | `Failure _ -> t2 g
  | `Success g -> g

let t_do b omax t g =
  let max = max (odfl max_int omax) 0 in

  let rec doit i g =
    let r = if i < max then Some (t_try_base t g) else None in

    match r with
    | None -> t_id None g

    | Some (`Failure e) ->
        let fail =
          match b, omax with
          | false, _      -> false
          | true , None   -> i < 1
          | true , Some m -> i < m
        in
          if fail then raise e else t_id None g

    | Some (`Success (juc, ln)) -> 
        t_subgoal (List.map (fun _ -> doit (i+1)) ln) (juc, ln)
  in
    doit 0 g

let t_repeat t = t_do false None t

let t_close t g =
  match t g with
  | (juc, []    ) -> (juc, [])
  | (_  , i :: _) -> raise (StillOpenGoal i)

let t_rotate mode (j, ns) =
  let mrev = match mode with `Left -> identity | `Right -> List.rev in

  match mrev ns with
  | []      -> (j, ns)
  | n :: ns -> (j, mrev (ns @ [n]))


(* -------------------------------------------------------------------- *)
let get_node  g = (get_pj g).pj_decl
let get_goal  g = (get_open_goal g).pj_decl
let get_hyps  g = fst (get_goal g)
let get_concl g = snd (get_goal g)

(* -------------------------------------------------------------------- *)
type tac_error =
  | UnknownAx             of EcPath.path
  | NotAHypothesis        of EcIdent.t
  | UnknownElims          of form
  | UnknownIntros         of form
  | UnknownSplit          of form
  | UnknownRewrite        of form
  | CannotClearConcl      of EcIdent.t * form
  | CannotReconizeElimT
  | TooManyArgument
  | NoHypToSubst          of EcIdent.t option
  | CannotProve           of l_decl
  | InvalNumOfTactic      of int * int
  | NotPhl                of bool option
  | NoSkipStmt
  | InvalidCodePosition   of string*int*int*int
  | CanNotApply           of string * string
  | InvalidName           of string
  | User                  of string

exception TacError of tac_error

let pp_tac_error fmt error =
  let env = PE.PPEnv.ofenv EcEnv.initial in (* FIXME *)
  match error with
  | UnknownAx p ->
      Format.fprintf fmt "Unknown axiom/lemma %a" PE.pp_path p
  | NotAHypothesis id ->
      Format.fprintf fmt "Unknown hypothesis %s" (EcIdent.name id)
  | UnknownElims f ->
    Format.fprintf fmt "Do not known what to eliminate in %a" (PE.pp_form env) f
  | UnknownIntros f ->
    Format.fprintf fmt "Do not known what to introduce in %a" (PE.pp_form env) f
  | UnknownSplit f ->
    Format.fprintf fmt "Do not known how to split %a" (PE.pp_form env) f
  | UnknownRewrite f ->
    Format.fprintf fmt "Do not known how to rewrite %a" (PE.pp_form env) f
  | CannotClearConcl(id,_) ->
    Format.fprintf fmt "Cannot clear %s, it is used in the conclusion"
      (EcIdent.name id)
  | CannotReconizeElimT ->
    Format.fprintf fmt "Cannot reconize the elimination lemma"
  | TooManyArgument ->
    Format.fprintf fmt "Too many arguments in the application"
  | NoHypToSubst (Some id) ->
    Format.fprintf fmt "Cannot find non recursive equation on %s"
      (EcIdent.name id)
  | NoHypToSubst None ->
    Format.fprintf fmt "Cannot find non recursive equation to substitute"
  | CannotProve _ ->
    Format.fprintf fmt "Cannot prove current goal"
  | InvalNumOfTactic (i1,i2) ->
    Format.fprintf fmt "Invalid number of tactics: %i given, %i expected" i2 i1
  | NoSkipStmt ->
    Format.fprintf fmt "Cannot apply skip rule"
  | NotPhl b ->
    let s =
      match b with
      | None -> "phl/prhl"
      | Some true -> "phl"
      | Some false -> "prhl" in
    Format.fprintf fmt "The conclusion does not end by a %s judgment" s
  | InvalidCodePosition (msg,k,lb,up) ->
    Format.fprintf fmt "%s: Invalid code line number %i, expected in [%i,%i]" msg k lb up
  | CanNotApply(s1,s2) ->
    Format.fprintf fmt "Can not apply %s tactic:@\n %s" s1 s2
  | InvalidName x ->
    Format.fprintf fmt "Invalid name for this kind of object: %s" x
  | User msg ->
    Format.fprintf fmt "%s" msg

let _ = EcPException.register (fun fmt exn ->
  match exn with
  | TacError error -> pp_tac_error fmt error
  | _ -> raise exn)

let tacerror error = raise (TacError error)

let tacuerror fmt =
  let buf  = Buffer.create 127 in
  let fbuf = Format.formatter_of_buffer buf in
    Format.kfprintf
      (fun _ ->
         Format.pp_print_flush fbuf ();
         raise (TacError (User (Buffer.contents buf))))
      fbuf fmt

let cannot_apply s1 s2 = tacerror (CanNotApply(s1,s2))

let t_subgoal lt gs =
  try
    t_subgoal lt gs
  with
  | InvalidNumberOfTactic (i1, i2) ->
      tacerror (InvalNumOfTactic (i1, i2))

let t_admit g =
  let rule = { pr_name = RN_admit; pr_hyps = [] } in
  upd_rule_done rule g

let check_hyps hyps1 hyps2 =
  assert (hyps1 == hyps2) (* FIXME error message *)

(* WARNING this do not generate the subgoal included in n.
   It could be greater to ensure we have no circular dependency *)
(* Use the proof of n1 to prove n *)
let use_node env juc n n1 =
  let hyps,concl = get_node (juc,n) in
  let hyps',concl' = get_goal (juc,n1) in
  check_hyps hyps hyps';
  check_conv env hyps concl concl';
  let rule = { pr_name = RN_conv; pr_hyps = [RA_node n] } in
  fst (upd_rule rule (juc,n1))

let t_use env n gs (juc,n1) =
  use_node env juc n n1, gs

let t_change env f (juc,n1) =
  let hyps = get_hyps (juc,n1) in
  check_type env f.f_ty tbool;
  let (juc,n) = new_goal juc (hyps,f) in
  t_use env n [n] (juc,n1)

let t_red env g =
  let hyps, concl = get_goal g in
  let f = EcReduction.h_red EcReduction.full_red env hyps concl in
  t_change env f g

let t_simplify env ri (juc,n1 as g) =
  let hyps, concl = get_goal g in
  let f = EcReduction.simplify ri env hyps concl in
  let (juc,n) = new_goal juc (hyps,f) in
  let rule = { pr_name = RN_conv; pr_hyps = [RA_node n] } in
  upd_rule rule (juc,n1)

let t_simplify_nodelta env g = 
  let ri = { full_red with delta_h = Some Mid.empty; delta_p = Some EcPath.Mp.empty } in 
  t_simplify env ri g
  
let mkn_hyp juc hyps id =
  let f = LDecl.lookup_hyp_by_id id hyps in
  let juc,n = new_goal juc (hyps,f) in
  let rule = { pr_name = RN_hyp id; pr_hyps = [] } in
  let juc, _ = upd_rule_done rule (juc,n) in
  juc, n

let t_hyp env id (juc,n as g) =
  let hyps = get_hyps g in
  let juc,nh = mkn_hyp juc hyps id in
  use_node env juc nh n, []

let mkn_glob env juc hyps p tys =
  let f = Ax.instanciate p tys env in
  let juc, n = new_goal juc (hyps,f) in
  let rule = { pr_name = RN_glob(p,tys); pr_hyps = [] } in
  let juc, _ = upd_rule_done rule (juc, n) in
  juc, n

let t_glob env p tys (juc,n as g) =
  let hyps = get_hyps g in
  let juc, nh = mkn_glob env juc hyps p tys in
  use_node env juc nh n, []

let t_trivial pi env g =
  let goal = get_goal g in
  if EcEnv.check_goal env pi goal then
    let rule = { pr_name = RN_prover (); pr_hyps = [] } in
    upd_rule_done rule g
  else tacerror (CannotProve goal)

let t_clear ids (juc,n as g) =
  let hyps,concl = get_goal g in
  if not (Mid.set_disjoint ids concl.f_fv) then
    tacerror (CannotClearConcl(Sid.choose (Mid.set_inter ids concl.f_fv), concl));
  let hyps = LDecl.clear ids hyps in
  let juc,n1 = new_goal juc (hyps,concl) in
  let rule = { pr_name = RN_clear ids; pr_hyps = [RA_node n1] } in
  upd_rule rule (juc,n)

let tyenv_of_hyps env hyps =
  let add env (id,k) =
    match k with
    | LD_var (ty,_) -> EcEnv.Var.bind_local id ty env
    | LD_mem mt     -> EcEnv.Memory.push (id,mt) env
    | LD_modty (i,r)    -> EcEnv.Mod.bind_local id i r env
    | LD_hyp   _    -> env in
  List.fold_left add env hyps.h_local

let check_modtype_restr env mp mt i restr = 
  EcTyping.check_sig_mt_cnv env mt i;
  let restr = EcEnv.NormMp.norm_restr env restr in
  let us = EcEnv.NormMp.top_uses env mp in
  let check u = 
    let me = EcEnv.Mod.by_mpath u env in
    match me.EcModules.me_body with 
    | EcModules.ME_Decl(_,nu) ->
      let nu = EcEnv.NormMp.norm_restr env nu in
      let diff = EcPath.Sm.diff restr nu in
      if not (EcPath.Sm.is_empty diff) then assert false; 
                                    (* FIXME error message *)
    | EcModules.ME_Structure _ -> 
      if EcPath.Sm.mem u restr then assert false (* FIXME error message *)
    | _ -> assert false in
  EcPath.Sm.iter check us; 

type app_arg =
  | AAform of form
  | AAmem  of EcIdent.t
  | AAmp   of EcPath.mpath * EcModules.module_sig 
  | AAnode

let check_arg do_arg env hyps s x gty a =
  let a = do_arg env hyps (Some gty) a in
  match gty, a with
  | GTty ty  , AAform f ->
      check_type env ty f.f_ty; (* FIXME error message *)
      f_bind_local s x f, RA_form f
  | GTmem _   , AAmem m ->
      f_bind_mem s x m, RA_id m
  | GTmodty (emt, restr), AAmp (mp, mt)  ->
    let env = tyenv_of_hyps env hyps in
    check_modtype_restr env mp mt emt restr;
    f_bind_mod s x mp, RA_mp mp
  | _ -> assert false (* FIXME error message *)

let mkn_apply do_arg env (juc,n) args =
  if args = [] then (juc,n), []
  else
    let hyps,concl = get_node (juc,n) in
    let env = tyenv_of_hyps env hyps in
    let check_arg = check_arg do_arg env hyps in
    let rec check_apply juc s ras f args =
      match args with
      | [] -> juc, List.rev ras, f_subst s f
      | a :: args' ->
        if is_forall f then 
          let (x,gty,f') = destr_forall1 f in
          let s, ra = check_arg s x gty a in
          check_apply juc s (ra::ras) f' args' 
        else if is_imp f then 
          let (f1,f2) = destr_imp f in
          let a = do_arg env hyps None a in
          assert (a = AAnode); (* FIXME error message *)
          let juc, n = new_goal juc (hyps, f_subst s f1) in
          check_apply juc s (RA_node n :: ras) f2 args' 
        else 
          let f = f_subst s f in
          match h_red_opt full_red env hyps f with
          | None -> tacerror TooManyArgument
          | Some f ->  check_apply juc f_subst_id ras f args in
    let juc, ras, concl = check_apply juc f_subst_id [] concl args in
    let (juc,n1) = new_goal juc (hyps,concl) in
    let rule = { pr_name = RN_apply; pr_hyps = RA_node n :: ras} in
    let juc, _ = upd_rule rule (juc,n1) in
    let ns = List.pmap (function RA_node n -> Some n | _ -> None) ras in
    (juc,n1), ns

let gen_t_apply do_arg env fn args (juc,n) =
  let (juc,an), ns = mkn_apply do_arg env (juc,fn) args in
  (use_node env juc an n, ns)

let gen_t_apply_form do_arg env f args (juc, n as g) =
  let hyps = get_hyps g in
  let juc, fn = new_goal juc (hyps, f) in
  let juc,ns = gen_t_apply do_arg env fn args (juc,n) in
  juc, fn::ns

let t_apply_form = gen_t_apply_form (fun _ _ _ a -> a)

let gen_t_apply_glob do_arg env p tys args (juc,n as g) =
  let hyps = get_hyps g in
  let juc,fn = mkn_glob env juc hyps p tys in
  gen_t_apply do_arg env fn args (juc,n)

let t_apply_glob = gen_t_apply_glob (fun _ _ _ a -> a)

let gen_t_apply_hyp do_arg env id args (juc ,n as g) =
  let hyps = get_hyps g in
  let juc,fn = mkn_hyp juc hyps id in
  gen_t_apply do_arg env fn args (juc, n)

let t_apply_hyp = gen_t_apply_hyp (fun _ _ _ a -> a)

let check_logic env p =
  try  ignore (EcEnv.Ax.by_path p env)
  with EcEnv.LookupFailure _ -> assert false

let t_apply_logic env p tyargs args g =
  check_logic env p;
  t_apply_glob env p tyargs args g
  

let pattern_form name env hyps f1 f =
  let x = EcIdent.create (odfl "x" name) in
  let fx = EcFol.f_local x f1.f_ty in
  let body =
    Hf.memo_rec 107
      (fun aux f ->
        if EcReduction.is_alpha_eq env hyps f f1 then fx
        else f_map (fun ty -> ty) aux f)
      f in
  x, body

let t_rewrite_gen fpat env side f g = 
  let hyps,concl = get_goal g in
  let rec find_rewrite f =
    if is_eq f then destr_eq f, true
    else if is_iff f then destr_iff f, false
    else
      match h_red_opt full_red env hyps f with
      | Some f -> find_rewrite f
      | None   -> tacerror (UnknownRewrite f) in
  let (f1,f2),eq = find_rewrite f in
  let p,tys =
    if eq then (if side then p_rewrite_l else p_rewrite_r), [f1.f_ty]
    else (if side then p_rewrite_iff_l else p_rewrite_iff_r), [] in
  let pred =
    let f = if side then f1 else f2 in
    let x, body = fpat env hyps f concl in
    f_lambda [x,GTty f.f_ty] body in
  t_on_last
    (t_red env)
    (t_apply_logic env p tys [AAform f1;AAform f2;AAform pred;AAnode;AAnode] g)

let t_rewrite = t_rewrite_gen (pattern_form None)

let t_rewrite_node env ((juc,an), gs) side n =
  let (_,f) = get_node (juc, an) in
  t_seq_subgoal (t_rewrite env side f)
    [t_use env an gs;t_id None] (juc,n)

let t_rewrite_hyp env side id args (juc,n as g) =
  let hyps = get_hyps g in
  let g' = mkn_hyp juc hyps id in
  t_rewrite_node env (mkn_apply (fun _ _ _ a -> a) env g' args) side n

let t_cut env f g =
  let concl = get_concl g in
  t_apply_logic env p_cut_lemma [] [AAform f;AAform concl;AAnode;AAnode] g

let set_loc loc f x =
  try f x
  with e -> EcLocation.locate_error loc e

let t_intros env ids (juc,n as g) =
  let hyps, concl = get_goal g in
  let add_local s id x gty =
    let id   = id.pl_desc in
    let name = EcIdent.name id in
    let gty = gty_subst s gty in
    match gty with
    | GTty ty ->
        if name <> "_" && not (EcIo.is_sym_ident name) then
          tacerror (InvalidName name);
        LD_var(ty,None), f_bind_local s x (f_local id ty)

    | GTmem me ->
        if name <> "_" && not (EcIo.is_mem_ident name) then
          tacerror (InvalidName name);
        LD_mem me, f_bind_mem s x id

    | GTmodty (i,r) ->
        if name <> "_" && not (EcIo.is_mod_ident name) then
          tacerror (InvalidName name);
        LD_modty (i,r), f_bind_mod s x (EcPath.mident id)
  in

  let add_ld id ld hyps =
    set_loc id.pl_loc (LDecl.add_local id.pl_desc ld) hyps in

  let rec check_intros hyps ids s concl =
    match ids with
    | [] -> hyps, f_subst s concl
    | id::ids' ->
      if is_forall concl then
        let (x,gty,concl) = destr_forall1 concl in
        let ld, s = add_local s id x gty in
        let hyps = add_ld id ld hyps in
        check_intros hyps ids' s concl
      else if is_imp concl then
        let f1, f2 = destr_imp concl in
        let hyps = add_ld id (LD_hyp (f_subst s f1)) hyps in
        check_intros hyps ids' s f2
      else if is_let1 concl then
        let x,ty,e1,concl = destr_let1 concl in
        let s = f_bind_local s x (f_local id.pl_desc ty) in
        let hyps = add_ld id (LD_var (s.fs_ty ty, Some (f_subst s e1))) hyps in
        check_intros hyps ids' s concl
      else if s == f_subst_id then
        match h_red_opt full_red env hyps concl with
        | None -> tacerror (UnknownIntros concl)
        | Some concl -> check_intros hyps ids s concl
      else check_intros hyps ids f_subst_id (f_subst s concl) in
  let hyps, concl = check_intros hyps ids f_subst_id concl in
  let (juc,n1) = new_goal juc (hyps,concl) in
  let ids = List.map unloc ids in
  let rule = { pr_name = RN_intros ids; pr_hyps = [RA_node n1]} in
  upd_rule rule (juc,n)

(* internal use *)
let t_intros_i env ids g =
  t_intros env
    (List.map (fun id -> {pl_desc = id; pl_loc = EcLocation._dummy}) ids)
    g

let createVarForBinding t =
  let v = EcIdent.create "_" in ((v, GTty t),EcFol.f_local v t)

let createVarForLet t =
  let v = EcIdent.create "_" in ((v, t), EcFol.f_local v t)

(* This tactic works only if the conclusion is exactly a reflexive equality *)
let t_reflex env g =
  let _, concl = get_goal g in
  let (f,_) = destr_eq concl in
  t_apply_logic env p_eq_refl [f.f_ty] [AAform f] g

(* Use to create two set of vars of a list of types*)
let parseType create types =
  let parse ty =
    let (bX, fX) = create ty in
    let (bY, fY) = create ty in
    ((bX, bY), (fX, fY))
  in
  List.split (List.map parse types)

(* Generate a lemma that permits to elim a tuple *)
let gen_eq_tuple_elim_lemma types =
  let (bC, fC) = createVarForBinding EcTypes.tbool in
  let (vars, fvars) = parseType createVarForBinding types in
  let (varsx, varsy) = List.split vars in
  let (fvarsx, fvarsy) = List.split fvars in
  let bindings = varsx@varsy@[bC] in
  let hyp1 = f_eq (f_tuple fvarsx) (f_tuple fvarsy) in
  let hyp2 = f_imps (List.map (fun (x,y) -> f_eq x y) fvars) fC in
  f_forall bindings (f_imps [hyp1; hyp2] fC)

(* Generate a proof of eq_tuple_elim *)
let gen_eq_tuple_elim_proof env types =
  let pred rvars fc =
    let (bT, fT) = createVarForBinding (ttuple types) in
    let projs = List.map createVarForLet types in
    let (intro, fprojs) = List.split projs in
    let introTu = LTuple intro in
    let eqs = List.map (fun (x, y) -> f_eq x y) (List.combine fprojs rvars) in
    let body = f_imps eqs fc in
    f_app (f_lambda [bT] (f_let introTu fT body)) [f_tuple rvars] (EcTypes.tbool)
  in
  
  let (locVars, locVarsF) = parseType createVarForLet types in
  let (locC, locCF) = createVarForLet EcTypes.tbool in
  let introVars =
    let (a, b) = List.split locVars in
    fst (List.split (a@b@[locC]))
  in
  let (_, rvars) = List.split locVarsF in
  let h1 = EcIdent.create "_" in
  let h2 = EcIdent.create "_" in
  let intro = t_intros_i env (introVars@[h1;h2]) in
  t_lseq [
    intro;
    t_seq_subgoal
      (t_apply_form env (pred rvars locCF) (List.map (fun _ -> AAnode) types))
      ((
        t_lseq [t_rewrite_hyp env false h1 [];
        t_apply_hyp env h2 [];
        t_apply_logic env p_true_intro [] []]
      )::(List.map (fun _ -> t_reflex env) types))
  ]
  
(* Generate a lemma that permits to split tuple *)
let gen_split_tuple_lemma types =
  let (vars, fvars) = parseType createVarForBinding types in
  let (varsx, varsy) = List.split vars in
  let (fvarsx, fvarsy) = List.split fvars in
  let bindings = varsx@varsy in
  let hyps = List.map (fun (x,y) -> f_eq x y) fvars in
  let body = f_eq (f_tuple fvarsx) (f_tuple fvarsy) in
  f_forall bindings (f_imps hyps body)

(* Generate the proof for gen_split_tuple_proof *)
let gen_split_tuple_proof env types =
  let introVars = List.map (fun _ -> EcIdent.create "_") (types@types) in
  let introHyps = List.map (fun _ -> EcIdent.create "_") types in
  let rews = List.map (fun h -> t_rewrite_hyp env true h []) introHyps in
  t_seq (t_lseq ((t_intros_i env (introVars@introHyps))::rews)) (t_reflex env)

let t_elim env f (juc,n) =
  let hyps,concl = get_goal (juc,n) in
  let rec aux f =
    match f.f_node with
    | Fop(p,_) when EcPath.p_equal p p_false ->
      t_apply_logic env p_false_elim [] [AAform concl; AAnode] (juc,n)

    | Fapp({f_node = Fop(p,_)}, [a1;a2] ) ->
      begin
        match op_kind p with
        | OK_and b ->
          t_apply_logic env (if b then p_anda_elim else p_and_elim) []
                [AAform a1;AAform a2;AAform concl;AAnode;AAnode] (juc,n)
        | OK_or b  ->
          t_apply_logic env (if b then p_ora_elim else p_or_elim) []
                [AAform a1;AAform a2;AAform concl;AAnode;AAnode;AAnode] (juc,n)
        | OK_iff   -> 
          t_apply_logic env p_iff_elim []
                [AAform a1;AAform a2;AAform concl;AAnode;AAnode] (juc,n)
        | OK_eq when is_tuple a1 && is_tuple a2 ->
          let fs1 = destr_tuple a1 in
          let fs2 = destr_tuple a2 in
          let types = List.map (fun v -> v.f_ty) fs1 in
          let args = List.map (fun f -> AAform f) (fs1 @ fs2 @ [concl]) in
          let lemma = gen_eq_tuple_elim_lemma types in
          let proof = gen_eq_tuple_elim_proof env types in
          let gs = t_apply_form env lemma (args@[AAnode; AAnode]) (juc,n) in
          t_on_first proof gs
        | _        -> aux_red f
      end
    | Fif(a1,a2,a3) ->
      t_apply_logic env p_if_elim [] [AAform a1;AAform a2;AAform a3;
                                     AAform concl;AAnode;AAnode;AAnode] (juc,n)
    | Fquant(Lexists,bd,f') ->
      let juc,n1 = new_goal juc (hyps, f) in
      let juc,n2 = new_goal juc (hyps,f_forall bd (f_imp f' concl)) in
      let rule = { pr_name = RN_exists_elim; pr_hyps = [RA_node n1; RA_node n2] } in
      upd_rule rule (juc, n)
    | _ -> aux_red f

  and aux_red f =
    match h_red_opt full_red env hyps f with
    | Some f -> aux f
    | _ -> tacerror (UnknownElims f) in
  aux f

let t_elim_hyp env h g =
  let f = LDecl.lookup_hyp_by_id h (get_hyps g) in
  t_on_first (t_hyp env h) (t_elim env f g)

let t_or_intro b env g =
  let hyps, concl = get_goal g in
  let rec aux f =
    match f.f_node with
    | Fapp({f_node = Fop(p,_)}, [f1;f2]) when EcPath.p_equal p p_or ->
      let lem = if b then p_or_intro_l else p_or_intro_r in
      t_apply_logic env lem [] [AAform f1; AAform f2; AAnode] g
    | Fapp({f_node = Fop(p,_)}, [f1;f2]) when EcPath.p_equal p p_ora ->
      let lem = if b then p_ora_intro_l else p_ora_intro_r in
      t_apply_logic env lem [] [AAform f1; AAform f2; AAnode] g
    | _ ->
      match h_red_opt full_red env hyps f with
      | Some f -> aux f
      | None -> tacerror (UnknownSplit f) in
  aux concl

let t_left  = t_or_intro true
let t_right = t_or_intro false

let t_generalize_form name env f g =
  let hyps,concl = get_goal g in
  let x,body = pattern_form name env hyps f concl in
  let ff = f_forall [x,GTty f.f_ty] body in
  t_apply_form env ff [AAform f] g

let t_generalize_hyps env ids g =
  let hyps,concl = get_goal g in
  let env1 = tyenv_of_hyps env hyps in
  let rec aux (s:f_subst) ids = 
    match ids with
    | [] -> f_subst s concl, [], []
    | id::ids ->
      match LDecl.ld_subst s (LDecl.lookup_by_id id hyps) with
      | LD_var (ty,body) ->
        let x = EcIdent.fresh id in
        let s = EcFol.f_bind_local s id (f_local x ty) in
        let ff,args,lt = aux s ids in
        begin match body with
        | None -> 
          f_forall [x, GTty ty] ff, AAform (f_local id ty) :: args, lt
        | Some body ->
          f_let (LSymbol(x,ty)) body ff, args, lt
        end
      | LD_mem mt ->
        let x = EcIdent.fresh id in
        let s = EcFol.f_bind_mem s id x in
        let ff, args, lt = aux s ids in
        f_forall [x, GTmem mt] ff, AAmem id :: args, lt
      | LD_modty (mt,r) -> 
        let x = EcIdent.fresh id in
        let s = EcFol.f_bind_mod s id (EcPath.mident x) in
        let mp = EcPath.mident id in
        let sig_ = (EcEnv.Mod.by_mpath mp env1).EcModules.me_sig in
        let ff, args, lt = aux s ids in
        f_forall [x,GTmodty(mt,r)] ff, AAmp(mp,sig_) :: args, lt 
      | LD_hyp f ->
        let ff, args, lt = aux s ids in
        f_imp f ff, AAnode :: args, t_hyp env id :: lt in
  let ff, args, lt = aux f_subst_id ids in
  t_seq_subgoal (t_apply_form env ff args) (t_id None :: lt) g

let t_generalize_hyp env id g = t_generalize_hyps env [id] g

let t_generalize_hyps clear env ids g = 
  if clear then 
    t_seq (t_generalize_hyps env ids) (t_clear (EcIdent.Sid.of_list ids)) g
  else t_generalize_hyps env ids g


let t_elimT env f p g =
  let hyps,concl = get_goal g in
  let ax = EcEnv.Ax.by_path p env in
  let rec skip_imp a f =
    if is_imp f then skip_imp (AAnode::a) (snd (destr_imp f))
    else a, f in

  match ax.EcDecl.ax_spec with
  | None -> tacerror (CannotReconizeElimT)
  | Some fax ->
    let tys =
      let tpred =
        try
          match destr_forall1 fax with
          | _, GTty ty, _ -> ty
          | _             -> raise Not_found
        with _ -> tacerror (CannotReconizeElimT) in
      let ue = EcUnify.UniEnv.create (Some hyps.h_tvar) in
      let (ue, tpred,tys) =
        EcUnify.UniEnv.freshen ue ax.EcDecl.ax_tparams None tpred in
      EcUnify.unify env ue tpred (tfun f.f_ty tbool);
      let subst = Tuni.subst (EcUnify.UniEnv.close ue) in
      List.map subst tys in
    let fax = EcEnv.Ax.instanciate p tys env in
    let vx, _, fax = destr_forall1 fax in
    let pf =
      let x, body = pattern_form (Some (EcIdent.name vx)) env hyps f concl in
      f_lambda [x,GTty f.f_ty] body in
    let aa =
      if is_forall fax then
        let _,_,fax = destr_forall1 fax in
        let aa, _ = skip_imp [] fax in
        AAform f::aa
      else
        let aa,fax = skip_imp [] fax in
        if not (is_forall fax) then tacerror (CannotReconizeElimT);
        List.rev_append aa [AAform f] in
    t_apply_glob env p tys (AAform pf::aa) g

let t_case env f g =
  check_logic env p_case_eq_bool;
  t_elimT env f p_case_eq_bool g

let prove_goal_by sub_gs rule (juc,n as g) =
  let hyps,_ = get_goal g in
  let add_sgoal (juc,ns) sg = 
    let juc,n = new_goal juc (hyps,sg) in juc, RA_node n::ns
  in
  let juc,ns = List.fold_left add_sgoal (juc,[]) sub_gs in
  let rule = { pr_name = rule ; pr_hyps = List.rev ns} in
  upd_rule rule (juc,n)

let t_field (plus,times,inv,minus,z,o,eq) (t1,t2) g =
	let (pzs,pbs) = appfield (t1, t2) plus minus times inv z o in
	let pzs' = List.fold_left (fun is i -> (f_not (mk_form (Fapp (eq, [i;z])) tbool)) :: is) [] pzs in
	let pbs' = List.fold_left (fun is (l,r) -> (mk_form (Fapp(eq, l :: r :: [])) tbool) :: is) [] pbs in
	prove_goal_by (pzs' @ pbs') RN_field g

let t_field_simp (plus,times,inv,minus,z,o,eq) t1 g =
	let (pzs,res) = appfield_simp t1 plus minus times inv z o in
	let pzs' = List.fold_left (fun is i -> (f_not (mk_form (Fapp (eq, [i;z])) tbool)) :: is) [] pzs in
	prove_goal_by (res :: pzs') RN_field g

let gen_t_exists do_arg env fs (juc,n as g) =
  let hyps,concl = get_goal g in
  let rec aux s ras fs concl =
    match fs with
    | [] -> ras, (f_subst s concl)
    | f::fs' ->
      if is_exists concl then
        let (x,gty,concl) = destr_exists1 concl in
        let s, a = check_arg do_arg env hyps s x gty f in
        aux s (a::ras) fs' concl
      else
        let concl = f_subst s concl in
        match h_red_opt full_red env hyps concl with
        | Some f -> aux f_subst_id ras fs f
        | None -> tacerror (UnknownSplit concl) in
  let args,concl = aux f_subst_id [] fs concl in
  let (juc,n1) = new_goal juc (hyps,concl) in
  let rule =
    {pr_name = RN_exists_intro; pr_hyps = List.rev_append args [RA_node n1] } in
  upd_rule rule (juc,n)

let t_exists = gen_t_exists (fun _ _ _ a -> a)

let t_split env g =
  let hyps, concl = get_goal g in
  let env0 = tyenv_of_hyps env hyps in
  let rec aux f =
    match f.f_node with
    | Fop(p,_) when EcPath.p_equal p p_true ->
      check_logic env p_true_intro;
      t_glob env p_true_intro [] g
    | Fapp({f_node = Fop(p,_)}, [f1;f2]) ->
      begin
        match op_kind p with
        | OK_and b -> 
          t_apply_logic env (if b then p_anda_intro else p_and_intro)
                [] [AAform f1;AAform f2;AAnode;AAnode] g
        | OK_iff   ->
          t_apply_logic env p_iff_intro []
                [AAform f1;AAform f2;AAnode;AAnode] g
        | OK_eq when EcReduction.is_conv env0 hyps f1 f2 -> t_reflex env g
        | OK_eq when is_tuple f1 && is_tuple f2 ->
          let fs1 = destr_tuple f1 in
          let fs2 = destr_tuple f2 in
          let types = List.map (fun v -> v.f_ty) fs1 in
          let args = List.map (fun f -> AAform f) (fs1@fs2) in
          let nodes = List.map (fun _ -> AAnode) fs1 in
          let lemma = gen_split_tuple_lemma types in
          let proof = gen_split_tuple_proof env types in
          let gs = t_apply_form env lemma (args@nodes) g in
          t_on_first proof gs
         | _ -> aux_red f
      end
    | Fif(f1,_f2,_f3) -> t_case env f1 g
    | _ ->  aux_red f
  and aux_red f =
    match h_red_opt full_red env hyps f with
    | Some f -> aux f
    | None -> tacerror (UnknownSplit f) in
  aux concl

let t_subst_gen env x h side g =
  let hyps,concl = get_goal g in
  let f = LDecl.lookup_hyp_by_id h hyps in
  let hhyps,_,_ =
    List.find_split (fun (id, _) -> EcIdent.id_equal x id) hyps.h_local in
  let rec gen fv hhyps =
    match hhyps with
    | [] -> ([], [], concl)
    | (id, lk) :: hhyps ->
      if EcIdent.id_equal id h then gen fv hhyps
      else match lk with
      | LD_var (ty, Some body) when not (Mid.set_disjoint body.f_fv fv) ->
        let aa, ids, concl = gen (Sid.add id fv) hhyps in
        aa, id::ids, f_let (LSymbol(id,ty)) body concl
      | LD_hyp f when not (Mid.set_disjoint f.f_fv fv) ->
        let aa, ids, concl = gen fv hhyps in
        id::aa, id::ids, f_imp f concl
      | _ -> gen fv hhyps in
  let aa, ids, concl = gen (Sid.singleton x) hhyps in
  let t_first =
    t_seq_subgoal (t_rewrite env side f)
      [ t_hyp env h;
        t_seq (t_clear (Sid.of_list (x::h::ids))) (t_intros_i env ids) ] in
  t_seq_subgoal (t_apply_form env concl (List.map (fun _ -> AAnode) aa))
    (t_first :: List.map (t_hyp env) aa) g

let cansubst_eq env hyps x f1 f2 = 
  match f1.f_node, x with
  | Flocal id, Some x when EcIdent.id_equal id x ->
    let f2 = simplify {no_red with delta_h = None} env hyps f2 in
    if Mid.mem id f2.f_fv then None else Some id
  | Flocal id, None ->
    let f2 = simplify {no_red with delta_h = None} env hyps f2 in
    if Mid.mem id f2.f_fv then None else Some id
  | _         -> None

let is_subst_eq env hyps x (hid,lk) =
  match lk with
  | LD_hyp f ->
    if is_eq_or_iff f then
      let f1, f2 = destr_eq_or_iff f in
      match cansubst_eq env hyps x f1 f2 with
      | Some id -> Some(hid, id,true)
      | None ->
        match cansubst_eq env hyps x f2 f1 with
        | Some id -> Some(hid, id,false)
        | None -> None
    else None
  | _ -> None

let t_subst1_loc env x g =
  let hyps = get_hyps g in
  match List.pick (is_subst_eq env hyps x) hyps.h_local with
  | None -> tacerror (NoHypToSubst x)
  | Some(h, x, side) ->
    t_subst_gen env x h side g

(* Substitution of f1 = Fpvar(pv,m) | Fglob(mp,m) *)

let pattern_pv env hyps f1 f =
  let x = EcIdent.create "x" in
  let fx = EcFol.f_local x f1.f_ty in
  let env = tyenv_of_hyps env hyps in
  let f1 = EcEnv.NormMp.norm_form env f1 in
  let subst = 
    match f1.f_node with
    | Fpvar (pv,m) -> EcPV.PVM.add env pv m fx EcPV.PVM.empty 
    | Fglob (mp,m) -> EcPV.PVM.add_glob env mp m fx EcPV.PVM.empty
    | _ -> assert false in
  let body = EcPV.PVM.subst env subst f in
  x, body

let t_subst_pv_gen env h side g =
  let hyps,_ = get_goal g in
  let f = LDecl.lookup_hyp_by_id h hyps in
  let to_gen = 
    List.filter (fun (id,lk) ->
      match lk with
      | LD_hyp _ -> not (EcIdent.id_equal h id) 
      | LD_var (_, Some _) -> true
      | _ -> false) (List.rev hyps.h_local) in
  let to_gen = List.map fst to_gen in
  let to_intros =
    List.map (fun id -> { pl_loc = EcLocation._dummy; pl_desc = id }) to_gen in
  t_seq (t_generalize_hyps true env to_gen)
    (t_seq_subgoal (t_rewrite_gen pattern_pv env side f)
            [t_hyp env h; 
             t_seq (t_clear (EcIdent.Sid.singleton h))
               (t_intros env to_intros)]) g

let cansubst_pv_eq env hyps fx f1 f2 = 
  let testfx f1 = 
    match fx with
    | None -> true
    | Some fx -> f_equal f1 (EcEnv.NormMp.norm_form env fx) in
  let check f1 = 
    let f1' = EcEnv.NormMp.norm_form env f1 in
    if testfx f1' then
      match f1'.f_node with
      | Fpvar(pv,m) ->
        let f2 = simplify {no_red with delta_h = None} env hyps f2 in
        let fv = EcPV.PV.fv env m f2 in
        if EcPV.PV.mem_pv pv fv then None
        else Some f1'
      | Fglob(mp,m) -> 
        let f2 = simplify {no_red with delta_h = None} env hyps f2 in
        let fv = EcPV.PV.fv env m f2 in
        if EcPV.PV.mem_glob mp fv then None
        else Some f1'
      | _ -> None
    else None in
  match f1.f_node with
  | Fpvar _ | Fglob _ -> check f1
  | _ -> None 

let is_subst_pv_eq env hyps fx (hid,lk) =
  match lk with
  | LD_hyp f ->
    if is_eq_or_iff f then
      let f1, f2 = destr_eq_or_iff f in
      match cansubst_pv_eq env hyps fx f1 f2 with
      | Some id -> Some(hid, id,true)
      | None ->
        match cansubst_pv_eq env hyps fx f2 f1 with
        | Some id -> Some(hid, id,false)
        | None -> None
    else None
  | _ -> None

let t_subst1_pv env fx g =
  let hyps = get_hyps g in
  match List.pick (is_subst_pv_eq env hyps fx) hyps.h_local with
  | None -> assert false (* FIXME error message *)
  | Some(h, _x, side) ->
    t_subst_pv_gen env h side g


let t_subst1 env fx g = 
  match fx with
  | None -> t_or (t_subst1_loc env None) (t_subst1_pv env None) g
  | Some fx ->
    match fx.f_node with
    | Flocal id -> t_subst1_loc env (Some id) g
    | (Fpvar _ | Fglob _) -> t_subst1_pv env (Some fx) g
    | _ -> assert false (* FIXME error message *)

let t_subst_all env =
  t_repeat (t_subst1 env None)

let find_in_hyps env f hyps =
  let test k =
    try
      let _, f' = LDecl.get_hyp k in
      check_conv env hyps f f'; true
    with _ -> false in
  fst (List.find test hyps.h_local)

let t_assumption env g = 
  let hyps,concl = get_goal g in
  let h = find_in_hyps env concl hyps in
  t_hyp env h g
    
let t_progress env tac g =
  let rec aux g = t_seq (t_simplify_nodelta env) aux0 g 
  and aux0 g = 
    t_seq (t_try tac) aux1 g
  and aux1 g = 
    let hyps,concl = get_goal g in
    match concl.f_node with
    | Fquant(Lforall,bd,_) ->
      let ids = 
        LDecl.fresh_ids hyps (List.map (fun (id,_) -> EcIdent.name id) bd) in
      t_seq (t_intros_i env ids) aux g
    | Flet (LTuple fs,f1,_) ->
      let p = p_tuple_ind (List.length fs) in
      t_seq (t_elimT env f1 p) aux g
    | Fapp({f_node = Fop(p,_)}, [f1;_]) when EcPath.p_equal p EcCoreLib.p_imp ->
      let id = LDecl.fresh_id hyps "H" in
      t_seq (t_intros_i env [id]) (aux2 id f1) g
    | _ -> t_try (t_seq (t_split env) aux) g
  and aux2 id f g = 
    let t1 = 
      match f.f_node with
      | Fop(p,_) when EcPath.p_equal p p_false -> t_elim_hyp env id
      | Fapp({f_node = Fop(p,_)}, [_;_] ) when is_op_and p -> 
        t_seq (t_elim_hyp env id) (t_clear (Sid.singleton id)) 
      | Fquant(Lexists,_,_) -> 
        t_seq (t_elim_hyp env id) (t_clear (Sid.singleton id))
      | _ when is_eq f -> 
        let f1, f2 = destr_eq f in
        if is_tuple f1 && is_tuple f2 then 
          t_seq (t_elim_hyp env id) (t_clear (Sid.singleton id))
        else t_subst_all env
          
      | _ -> t_subst_all env (* FIXME should allows to subst a given hyps *) in
    t_seq t1 aux g in
  aux g

  
  
  
