
open EcParsetree
open EcUtils
open EcTypes
open EcFol
open EcModules
open EcBaseLogic
open EcEnv
open EcLogic
open EcModules

exception CannotApply of string * string

let cannot_apply s1 s2 = raise (CannotApply(s1,s2))


let split_stmt n s = List.take_n n s



(* -------------------------------------------------------------------- *)
(* -------------------------  Substitution  --------------------------- *)
(* -------------------------------------------------------------------- *)

module PVM = struct

  module M = EcMaps.Map.Make(struct
    (* We assume that the mpath are in normal form *)  
    type t = prog_var * EcMemory.memory
    let compare (p1,m1) (p2,m2) = 
      let r = EcIdent.id_compare m1 m2 in
      if r = 0 then 
        let r = Pervasives.compare p1.pv_kind p2.pv_kind in
        if r = 0 then 
          let p1 = p1.pv_name.EcPath.m_path in
          let p2 = p2.pv_name.EcPath.m_path in
          EcPath.p_compare p1 p2 
        else r
      else r
  end)

  type subst = form M.t

  let empty = M.empty 

  let pvm env pv m = EcEnv.NormMp.norm_pvar env pv, m

  let add env pv m f s = M.add (pvm env pv m) f s 

  let add_none env pv m f s =
    M.change (fun o -> if o = None then Some f else o) (pvm env pv m) s

  let merge (s1:subst) (s2:subst) =
    M.merge (fun _ o1 o2 -> if o2 = None then o1 else o2) s1 s2

  let find env pv m s =
    M.find (pvm env pv m) s

  let subst env (s:subst) = 
    Hf.memo_rec 107 (fun aux f ->
      match f.f_node with
      | Fpvar(pv,m) -> 
          (try find env pv m s with Not_found -> f)
(*      | FeqGlob(m1,m2,mp) ->
        let xs, mps = EcEnv.norm_eqGlob_mp env mp in
        let add_m f mp = f_and_simpl (f_eqGlob m1 m2 mp) f in
        let add_v f (x,ty) = 
          let v1 = aux (f_pvar x ty m1) in
          let v2 = aux (f_pvar x ty m2) in
          f_and_simpl (f_eq_simpl v1 v2) f in
        let eqm = List.fold_left add_m f_true mps in
        List.fold_left add_v eqm xs  *)
      | FhoareF _ | FhoareS _ | FequivF _ | FequivS _ | Fpr _ -> assert false
      | _ -> EcFol.f_map (fun ty -> ty) aux f)

  let subst1 env pv m f = 
    let s = add env pv m f empty in
    subst env s

end



(* -------------------------------------------------------------------- *)
(* -------------------------------  Wp -------------------------------- *)
(* -------------------------------------------------------------------- *)

let id_of_pv pv = 
  EcIdent.create (EcPath.basename pv.pv_name.EcPath.m_path) 

let lv_subst env m lv f =
  match lv with
  | LvVar(pv,t) ->
      let id = id_of_pv pv in 
      let s = PVM.add env pv m (f_local id t) PVM.empty in
      (LSymbol (id,t), f), s
  | LvTuple vs ->
      let add (pv,t) (ids,s) = 
        let id = id_of_pv pv in
        let s = PVM.add_none env pv m (f_local id t) s in
        ((id,t)::ids, s) in
      let ids,s = List.fold_right add vs ([],PVM.empty) in
      (LTuple ids, f), s
  | LvMap((p,tys),pv,e,ty) ->
      let id = id_of_pv pv in 
      let s = PVM.add env pv m (f_local id ty) PVM.empty in
      let set = f_op p tys ty in
      let f = f_app set [f_pvar pv ty m; form_of_expr m e; f] ty in
      (LSymbol (id,ty), f), s
      
let wp_asgn_aux env m lv e (_let,s,f) =
  let lpe, se = lv_subst env m lv (form_of_expr m e) in
  let subst = PVM.subst env se in
  let _let = List.map (fun (lp,f) -> lp, subst f) _let in
  let s = PVM.merge se s in
  (lpe::_let, s,f)

exception HLerror

let mk_let env (_let,s,f) = 
  f_lets_simpl _let (PVM.subst env s f)
  
let wp_asgn1 env m s post =
  let r = List.rev s.s_node in
  match r with
  | {i_node = Sasgn(lv,e) } :: r' -> 
      let letsf = wp_asgn_aux env m lv e ([],PVM.empty,post) in
      EcModules.stmt (List.rev r'), mk_let env letsf
  | _ -> raise HLerror

let wp_asgn env m s post = 
  let r = List.rev s.s_node in
  let rec aux r letsf = 
    match r with 
    | [] -> [], letsf 
    | { i_node = Sasgn (lv,e) } :: r -> aux r (wp_asgn_aux env m lv e letsf) 
    | _ -> r, letsf in
  let (r',letsf) = aux r ([],PVM.empty, post) in
  if r == r' then s, post
  else 
    EcModules.stmt (List.rev r'), mk_let env letsf

exception No_wp

let rec wp_stmt env m (stmt: EcModules.instr list) letsf = 
  match stmt with
  | [] -> stmt, letsf
  | i :: stmt' -> 
      try 
        let letsf = wp_instr env m i letsf in
        wp_stmt env m stmt' letsf
      with No_wp -> stmt, letsf
and wp_instr env m i letsf = 
  match i.i_node with
  | Sasgn (lv,e) ->
      wp_asgn_aux env m lv e letsf
  | Sif (e,s1,s2) -> 
      let r1,letsf1 = wp_stmt env m (List.rev s1.s_node) letsf in
      let r2,letsf2 = wp_stmt env m (List.rev s2.s_node) letsf in
      if r1=[] && r2=[] then
        let post1 = mk_let env letsf1 in 
        let post2 = mk_let env letsf2 in
        let post  = f_if (form_of_expr m e) post1 post2 in
        [], PVM.empty, post
      else raise No_wp
  | _ -> raise No_wp

let wp env m s post = 
  let r,letsf = wp_stmt env m (List.rev s.s_node) ([],PVM.empty,post) in
  List.rev r, mk_let env letsf 


(* -------------------------------------------------------------------- *)
(* ----------------------  Auxiliary functions  ----------------------- *)
(* -------------------------------------------------------------------- *)

let destr_hoareF c =
  try destr_hoareF c with DestrError _ -> tacerror (NotPhl (Some true))
let destr_hoareS c =
  try destr_hoareS c with DestrError _ -> tacerror (NotPhl (Some true))
let destr_equivF c =
  try destr_equivF c with DestrError _ -> tacerror (NotPhl (Some false))
let destr_equivS c =
  try destr_equivS c with DestrError _ -> tacerror (NotPhl (Some false))

let t_hS_or_eS th te g =
  let concl = get_concl g in
  if is_hoareS concl then th g
  else if is_equivS concl then te g
  else tacerror (NotPhl None)

type destr_error =
  | Destr_hl 

exception DestrError of destr_error
exception NotSkipStmt

let destr_error e = raise (DestrError e)

let destr_hl env f = 
  match f.f_node with
    | FhoareS hr -> hr.hs_me, hr.hs_pre, hr.hs_s, hr.hs_post
    | FhoareF hr -> 
      let pre,fpath,post = hr.hf_pre, hr.hf_f, hr.hf_post  in 
      let fun_ = EcEnv.Fun.by_mpath fpath env in
      let b,ret_e = match fun_.f_def with 
        | Some fdef -> 
          fdef.f_body, fdef.f_ret
        | None -> assert false (* FIXME *)
      in
      let post = match ret_e with
        | None -> assert false (* FIXME *)
        | Some ret_e -> 
          let _,env = EcEnv.Fun.hoareF fpath env in
          let res = match EcEnv.Var.lookup_progvar_opt ~side:EcFol.mhr ([],"res") env with
            | Some (pv,_) -> pv
            | None -> assert false (* FIXME: error message *)
          in
          let subst = PVM.add env res EcFol.mhr (EcFol.form_of_expr EcFol.mhr ret_e) PVM.empty in
          PVM.subst env subst post
      in
      let locals = fst fun_.f_sig.fs_sig in
      let menv = List.fold_left 
        (fun menv v -> EcMemory.bind v.v_name v.v_type menv)
        (EcMemory.empty_local EcFol.mhr fpath) locals in
      menv,pre,b,post
    | _ -> destr_error Destr_hl

let upd_body body s = {body with EcModules.f_body = s}

module Pvar' = struct
  type t = EcTypes.prog_var * EcTypes.ty
  let mk_pvar pv mem ty = (pv,mem,ty)
  let compare lv1 lv2 = compare lv1 lv2
end

module PVset' = Set.Make(Pvar')

let rec modified_pvars_i instr = 
  let f_lval = function 
    | EcModules.LvVar (pv,ty ) -> PVset'.singleton (pv,ty)
    | EcModules.LvTuple pvs -> 
      List.fold_left (fun s (pv,ty) -> PVset'.add (pv,ty) s) PVset'.empty pvs
    | EcModules.LvMap ((_p,_tys),pv,_,ty) -> 
      (* FIXME: What are p and tys for? *)
      PVset'.singleton (pv,ty)
  in
  match instr.EcModules.i_node with
  | EcModules.Sasgn (lval,_) -> f_lval lval
  | EcModules.Srnd (lval,_) -> f_lval lval
  | EcModules.Scall _ -> assert false
  | EcModules.Sif (_,s1,s2) -> 
    PVset'.union (modified_pvars s1) (modified_pvars s2)
  | EcModules.Swhile (_,s) -> modified_pvars s
  | EcModules.Sassert _ -> PVset'.empty

and modified_pvars stmt = 
  List.fold_left (fun s i -> PVset'.union s (modified_pvars_i i)) 
    PVset'.empty stmt.EcModules.s_node


module Pvar = struct
  type t = EcTypes.prog_var * EcMemory.memory * EcTypes.ty
  let mk_pvar pv mem ty = (pv,mem,ty)
  let compare lv1 lv2 = compare lv1 lv2
end
module PVset = Set.Make(Pvar)
let rec free_pvar  fm = 
  match fm.f_node with
    | Fint _ | Fop _ -> PVset.empty
    | Fpvar (pv,mem) -> PVset.singleton (pv,mem,fm.f_ty) 
    | Flocal _ -> PVset.empty
    | Fquant(_,_,f) -> free_pvar f
    | Fif(f1,f2,f3) -> 
      PVset.union (free_pvar f1) (PVset.union (free_pvar f2) (free_pvar f3))
    | Flet(_, f1, f2) ->
      PVset.union (free_pvar f1) (free_pvar f2)
    | Fapp(f,args) ->
      List.fold_left (fun s f -> PVset.union s (free_pvar f)) (free_pvar f) args
    | Ftuple args ->
      List.fold_left (fun s f -> PVset.union s (free_pvar f)) PVset.empty args 
    | FhoareS _ (* (_,pre,_,post) *) -> 
      assert false (* FIXME: not implemented *)
      (* PVset.union (free_pvar pre) (free_pvar post) *)
    | _ -> assert false (* FIXME *)

let quantify_pvars env pvars phi = (* assert false  *)
  let f (pv,m,ty) (bds,phi) =
    if EcTypes.is_loc pv then
      let local = EcIdent.create (EcPath.name_mpath pv.EcTypes.pv_name) in
      let s = PVM.add env pv m (f_local local ty) PVM.empty in
      let phi = PVM.subst env s phi in 
      let bds = (local,GTty ty) :: bds in
      bds,phi
    else (bds,phi)
  in
  let bds,phi = PVset.fold f pvars ([],phi) in
  f_forall bds phi

let quantify_out_local_pvars env phi = 
  let free_pvars = free_pvar phi in
  Format.printf "Found %i free program variables \n" (List.length (PVset.elements free_pvars));
  Format.print_newline();
  quantify_pvars env free_pvars phi


(* -------------------------------------------------------------------- *)
(* -------------------------  Tactics --------------------------------- *)
(* -------------------------------------------------------------------- *)


let t_hoareF_fun_def env (juc,n1 as g) = 
  let hyps,concl = get_goal g in
  let hf = destr_hoareF concl in
  let memenv, fdef, env = Fun.hoareS hf.hf_f env in (* FIXME catch exception *)
  let m = EcMemory.memory memenv in
  let fres = 
    match fdef.f_ret with
    | None -> f_tt
    | Some e -> form_of_expr m e in
  let post = PVM.subst1 env (pv_res hf.hf_f) m fres hf.hf_post in
  let concl' = f_hoareS memenv hf.hf_pre fdef.f_body post in
  let (juc,n) = new_goal juc (hyps,concl') in
  let rule = { pr_name = RN_hl_fun_def; pr_hyps = [RA_node n] } in
  upd_rule rule (juc,n1)

let t_equivF_fun_def env (juc,n1 as g) = 
  let hyps,concl = get_goal g in
  let ef = destr_equivF concl in
  let memenvl,fdefl,memenvr,fdefr,env = Fun.equivS ef.eqf_fl ef.eqf_fr env in (* FIXME catch exception *)
  let ml, mr = EcMemory.memory memenvl, EcMemory.memory memenvr in
  let fresl = 
    match fdefl.f_ret with
    | None -> f_tt
    | Some e -> form_of_expr ml e in
  let fresr = 
    match fdefr.f_ret with
    | None -> f_tt
    | Some e -> form_of_expr mr e in
  let s = PVM.add env (pv_res ef.eqf_fl) ml fresl PVM.empty in
  let s = PVM.add env (pv_res ef.eqf_fr) mr fresr s in
  let post = PVM.subst env s ef.eqf_post in
  let concl' = f_equivS memenvl memenvr ef.eqf_pre fdefl.f_body fdefr.f_body post in
  let (juc,n) = new_goal juc (hyps,concl') in
  let rule = { pr_name = RN_hl_fun_def; pr_hyps = [RA_node n] } in
  upd_rule rule (juc,n1)

let t_fun_def env g =
  let concl = get_concl g in
  if is_hoareF concl then t_hoareF_fun_def env g
  else if is_equivF concl then t_equivF_fun_def env g
  else tacerror (NotPhl None)


  
let t_hoare_skip (juc,n as g) =
  let hyps,concl = get_goal g in
  let hs = destr_hoareS concl in
  if hs.hs_s.s_node <> [] then tacerror NoSkipStmt;
  let concl = f_imp hs.hs_pre hs.hs_post in
  let (m,mt) = hs.hs_me in 

  let concl = f_forall [(m,GTmem mt)] concl in
  let juc, n1 = new_goal juc (hyps,concl) in
  let rule = {pr_name = RN_hl_skip; pr_hyps = [RA_node n1]} in
  upd_rule rule (juc,n)

let t_equiv_skip (juc,n as g) =
  let hyps,concl = get_goal g in
  let es = destr_equivS concl in
  if es.eqs_sl.s_node <> [] then tacerror NoSkipStmt;
  if es.eqs_sr.s_node <> [] then tacerror NoSkipStmt;
  let concl = f_imp es.eqs_pre es.eqs_post in
  let (ml,mtl) = es.eqs_mel in 
  let (mr,mtr) = es.eqs_mer in 
  let concl = f_forall [(ml,GTmem mtl); (mr,GTmem mtr)] concl in
  let juc, n1 = new_goal juc (hyps,concl) in
  let rule = {pr_name = RN_hl_skip; pr_hyps = [RA_node n1]} in
  upd_rule rule (juc,n)

let t_skip = t_hS_or_eS t_hoare_skip t_equiv_skip 



let t_app (i,phi) _loc (juc,n as g) =
      let hyps,concl = get_goal g in
      let hs = destr_hoareS concl in
      let s1,s2 = split_stmt i hs.hs_s.s_node  in
      let a = f_hoareS hs.hs_me hs.hs_pre (stmt s1) phi  in
      let b = f_hoareS hs.hs_me phi (stmt s2) hs.hs_post in
      let juc,n1 = new_goal juc (hyps,a) in
      let juc,n2 = new_goal juc (hyps,b) in
      let rule = { pr_name = RN_app (Pos_single i,phi) ; pr_hyps = [RA_node n1; RA_node n2]} in
      upd_rule rule (juc,n)

    
(* -------------------------------------------------------------------- *)












let skip_tac env (juc,n as g) =
  let hyps,concl = get_goal g in
  let _mem,pre,s,post = destr_hl env concl in
  match s.EcModules.s_node with
    | _ :: _ ->
      raise NotSkipStmt
    | [] ->
      let conc = f_imp pre post in
      let conc = quantify_out_local_pvars env conc in
      let juc,n1 = new_goal juc (hyps,conc) in
      let rule = {pr_name = RN_fixme; pr_hyps=[RA_node n1]} in
      upd_rule rule (juc,n)


let wp_tac i _loc env (juc,n as g) =
  let hyps,concl = get_goal g in
  let menv,pre,s,post = destr_hl env concl in
  let s_fix,s_wp = split_stmt i s.EcModules.s_node  in
  let s_wp,post = wp env (EcMemory.memory menv) (EcModules.stmt s_wp) post in
  let s = EcModules.stmt (s_fix @ s_wp) in
  let a = f_hoareS menv pre s post  in
  let juc,n' = new_goal juc (hyps,a) in
  let rule = { pr_name = RN_fixme; pr_hyps = [RA_node n']} in
  upd_rule rule (juc,n)






let while_tac env inv vrnt bnd (juc,n as g) = 
  let hyps,concl = get_goal g in
  let menv,pre,s,post = destr_hl env concl in
  let rev_s = List.rev s.EcModules.s_node in
  match rev_s with
    | [] -> cannot_apply "while_tac" "empty statements"
    | i :: rev_s' ->
      match i.EcModules.i_node with
        | EcModules.Swhile (e,c) ->
          (* initialization *)
          (* {P} s' {Inv /\ v <= bdn /\ A mod(s) (Inv /\ ~e => post) } *)
          let mods = modified_pvars c in
          let f (pv,ty) pvs  = PVset.add (pv,EcFol.mhr,ty) pvs in
          let mods = PVset'.fold f mods PVset.empty in
          let e = form_of_expr (EcMemory.memory menv) e in
          let p = quantify_pvars env mods (f_imp (f_and inv (f_not e)) post) in
          let post1 = f_and inv (f_and (f_int_le vrnt bnd) p) in
          let j1 = f_hoareS menv pre (EcModules.stmt (List.rev rev_s')) post1 in
          let juc,n1 = new_goal juc (hyps,j1) in

          (* termination goal *)
          let vrnt_local = EcIdent.create "k" in
          let bnd_local = EcIdent.create "b" in
          let vrnt_eq = f_eq vrnt (f_local vrnt_local EcTypes.tint) in
          let vrnt_lt = f_int_lt vrnt (f_local vrnt_local EcTypes.tint) in
          let bnd_eq = f_eq bnd (f_local bnd_local EcTypes.tint) in
          let pre2 = f_and (f_and inv e) (f_and vrnt_eq bnd_eq) in
          let post2 = f_and vrnt_lt bnd_eq in
          let j2 = f_hoareS menv pre2 c post2 in
          let juc,n2 = new_goal juc (hyps,j2) in

          (* invariant preservation *)
          (* TODO: if prob=1 then the next goal can be merged with previous one,
             otw one cannot *)
          let pre3, post3 = f_and inv e, inv in
          let j3 = f_hoareS menv pre3 c post3 in
          let juc,n3 = new_goal juc (hyps,j3) in

          let rule = { pr_name = RN_fixme; pr_hyps=[RA_node n1;RA_node n2;RA_node n3]} in
          upd_rule rule (juc,n)
        | _ -> cannot_apply "while_tac" "a while loop is expected"


let unfold_hoare_tac env (juc,n as g) =
  let hyps,concl = get_goal g in
  let menv,pre,c,post = destr_hl env concl in
  let j = f_hoareS menv pre c post in
  let juc,n' = new_goal juc (hyps,j) in
  let rule = { pr_name = RN_fixme; pr_hyps=[RA_node n']} in
  upd_rule rule (juc,n)





let process_phl env process_form tac loc (_juc,_n as g) = 
  let hyps,concl = get_goal g in
  let menv,_pre,_s,_post = destr_hl env concl in
  let env = EcEnv.Memory.set_active (EcMemory.memory menv) 
    (EcEnv.Memory.push menv env) in
  match tac with 
    | Phoare ->
      unfold_hoare_tac env g
    (* | Papp (i,pf) ->  *)
    (*   let f = process_form env hyps pf EcTypes.tbool in *)
    (*   app_tac (i,f) loc env g *)
    | Pwp i -> 
      wp_tac i loc env g
    | Pskip -> 
      skip_tac env g
    | Pwhile (inv,varnt,bnd) ->
      let inv = process_form env hyps inv EcTypes.tbool in
      let varnt = process_form env hyps varnt EcTypes.tint in
      let bnd = process_form env hyps bnd EcTypes.tint in
      while_tac env inv varnt bnd g



