open EcParsetree
open EcUtils
open EcTypes
open EcFol
open EcModules
open EcBaseLogic
open EcEnv
open EcLogic
open EcModules


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
        if r = 0 then pv_compare_p p1 p2
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

module PV = struct 
  module M = EcMaps.Map.Make (struct
    (* We assume that the mpath are in normal form *)  
    type t = prog_var 
    let compare = pv_compare_p
  end)

  type pv_fv = ty M.t

  let empty = M.empty 

  let add env pv ty fv = M.add (NormMp.norm_pvar env pv) ty fv

  let remove env pv fv =
    M.remove (NormMp.norm_pvar env pv) fv

  let union _env fv1 fv2 =
    M.merge (fun _ o1 o2 -> if o2 = None then o1 else o2) fv1 fv2

  let mem env pv fv = 
    M.mem (NormMp.norm_pvar env pv) fv

  let elements = M.bindings 

end

let lp_write env w lp = 
  let add w (pv,ty) = PV.add env pv ty w in
  match lp with
  | LvVar pvt -> add w pvt 
  | LvTuple pvs -> List.fold_left add w pvs 
  | LvMap ((_p,_tys),pv,_,ty) -> add w (pv,ty) 

let rec s_write env w s = List.fold_left (i_write env) w s.s_node 

and i_write env w i = 
  match i.i_node with
  | Sasgn (lp,_) -> lp_write env w lp
  | Srnd (lp,_) -> lp_write env w lp
  | Scall(lp,f,_) -> 
    let wf = f_write env f in
    let w  = match lp with None -> w | Some lp -> lp_write env w lp in
    PV.union env w wf 
  | Sif (_,s1,s2) -> s_write env (s_write env w s1) s2
  | Swhile (_,s) -> s_write env w s
  | Sassert _ -> w 
    
and f_write env f =   
  let func = Fun.by_mpath f env in
  match func.f_def with
  | None -> assert false (* Not implemented *)
  | Some fdef ->
    let remove_local w {v_name = v } =
      PV.remove env {pv_name = EcPath.mqname f EcPath.PKother v []; 
                     pv_kind = PVloc } w in
    let wf = s_write env PV.empty fdef.f_body in
    let wf = List.fold_left remove_local wf fdef.f_locals in
    List.fold_left remove_local wf (fst func.f_sig.fs_sig) 
   

  
 
(* -------------------------------------------------------------------- *)
(* -------------------------------  Wp -------------------------------- *)
(* -------------------------------------------------------------------- *)

let id_of_pv pv = 
  EcIdent.create (EcPath.basename pv.pv_name.EcPath.m_path) 

let generalize_mod env m modi f = 
  let elts = PV.elements modi in
  let create (pv,ty) = id_of_pv pv, GTty ty in
  let b = List.map create elts in
  let s = List.fold_left2 (fun s (pv,ty) (id, _) ->
    PVM.add env pv m (f_local id ty) s) PVM.empty elts b in
  let f = PVM.subst env s f in
  f_forall_simpl b f


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


module Pvar = struct
  type t = EcTypes.prog_var * EcMemory.memory * EcTypes.ty
  let compare lv1 lv2 = compare lv1 lv2
end
module PVset = Set.Make(Pvar)

let quantify_pvars env pvars phi = 
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



let rec modified_pvars_i m instr = 
  let f_lval = function 
    | EcModules.LvVar (pv,ty ) -> PVset.singleton (pv,m,ty)
    | EcModules.LvTuple pvs -> 
      List.fold_left (fun s (pv,ty) -> PVset.add (pv,m,ty) s) PVset.empty pvs
    | EcModules.LvMap ((_p,_tys),pv,_,ty) -> 
      (* FIXME: What are p and tys for? *)
      PVset.singleton (pv,m,ty)
  in
  match instr.EcModules.i_node with
  | EcModules.Sasgn (lval,_) -> f_lval lval
  | EcModules.Srnd (lval,_) -> f_lval lval
  | EcModules.Scall _ -> assert false
  | EcModules.Sif (_,s1,s2) -> 
    PVset.union (modified_pvars m s1) (modified_pvars m s2)
  | EcModules.Swhile (_,s) -> modified_pvars m s
  | EcModules.Sassert _ -> PVset.empty

and modified_pvars m stmt = 
  List.fold_left (fun s i -> PVset.union s (modified_pvars_i m i))
    PVset.empty stmt.EcModules.s_node


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

(* -------------------------------------------------------------------- *)
  
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

(* -------------------------------------------------------------------- *)

let s_split i s =
  if i < 1 || List.length s.s_node < i then tacerror (InvalidCodePosition i)
  else s_split i s

let t_hoare_app i phi (juc,n as g) =
  let hyps,concl = get_goal g in
  let hs = destr_hoareS concl in
  let s1,s2 = s_split i hs.hs_s in
  let a = f_hoareS hs.hs_me hs.hs_pre (stmt s1) phi  in
  let b = f_hoareS hs.hs_me phi (stmt s2) hs.hs_post in
  let juc,n1 = new_goal juc (hyps,a) in
  let juc,n2 = new_goal juc (hyps,b) in
  let rule = { pr_name = RN_hl_append (Single i,phi) ; 
               pr_hyps = [RA_node n1; RA_node n2]} in
  upd_rule rule (juc,n)

let t_equiv_app (i,j) phi (juc,n as g) =
  let hyps,concl = get_goal g in
  let es = destr_equivS concl in
  let sl1,sl2 = s_split i es.eqs_sl in
  let sr1,sr2 = s_split j es.eqs_sr in
  let a = f_equivS es.eqs_mel es.eqs_mer es.eqs_pre (stmt sl1) (stmt sr1) phi in
  let b = 
    f_equivS es.eqs_mel es.eqs_mer phi (stmt sl2) (stmt sr2) es.eqs_post in
  let juc,n1 = new_goal juc (hyps,a) in
  let juc,n2 = new_goal juc (hyps,b) in
  let rule = { pr_name = RN_hl_append (Double (i,j), phi) ; 
               pr_hyps = [RA_node n1; RA_node n2]} in
  upd_rule rule (juc,n)

  
(* -------------------------------------------------------------------- *)

let s_skip_last i s =
  let len = List.length s.s_node in
  match i with
  | None -> [], s.s_node 
  | Some i ->
    assert (0 <= i && i < len); (* FIXME error message *)
    s_split (len - i) s 

let check_wp_progress i s remain =
  match i with
  | None -> List.length s.s_node - List.length remain
  | Some i ->
      assert (remain = []); (* FIXME error message *)
      i 

let t_hoare_wp env i (juc,n as g) =
  let hyps,concl = get_goal g in
  let hs = destr_hoareS concl in
  let s_hd,s_wp = s_skip_last i hs.hs_s in
  let s_wp,post = 
    wp env (EcMemory.memory hs.hs_me) (EcModules.stmt s_wp) hs.hs_post in
  let i = check_wp_progress i hs.hs_s s_wp in
  let s = EcModules.stmt (s_hd @ s_wp) in
  let concl = f_hoareS hs.hs_me hs.hs_pre s post  in
  let juc,n' = new_goal juc (hyps,concl) in
  let rule = { pr_name = RN_hl_wp (Single i); pr_hyps = [RA_node n']} in
  upd_rule rule (juc,n)

let t_equiv_wp env ij (juc,n as g) = 
  let hyps,concl = get_goal g in
  let es = destr_equivS concl in
  let i = omap ij fst and j = omap ij snd in
  let s_hdl,s_wpl = s_skip_last i es.eqs_sl in
  let s_hdr,s_wpr = s_skip_last j es.eqs_sr in
  let s_wpl,post = 
    wp env (EcMemory.memory es.eqs_mel) (EcModules.stmt s_wpl) es.eqs_post in
  let s_wpr, post =
    wp env (EcMemory.memory es.eqs_mer) (EcModules.stmt s_wpr) post in
  let i = check_wp_progress i es.eqs_sl s_wpl in
  let j = check_wp_progress j es.eqs_sr s_wpr in
  let sl = EcModules.stmt (s_hdl @ s_wpl) in
  let sr = EcModules.stmt (s_hdr @ s_wpr) in
  let concl = f_equivS es.eqs_mel es.eqs_mer es.eqs_pre sl sr post in
  let juc,n' = new_goal juc (hyps,concl) in
  let rule = { pr_name = RN_hl_wp (Double(i,j)); pr_hyps = [RA_node n']} in
  upd_rule rule (juc,n)

let t_wp env k =
  match k with
  | None -> t_hS_or_eS (t_hoare_wp env None) (t_equiv_wp env None)
  | Some (Single i) -> t_hoare_wp env (Some i)
  | Some (Double(i,j)) -> t_equiv_wp env (Some (i,j))

(* -------------------------------------------------------------------- *)
  
let t_hoare_while env inv (juc,n1 as g) =
  let hyps,concl = get_goal g in
  let hs = destr_hoareS concl in
  let error_message () = 
    cannot_apply "while" "the last instruction should be a while" in
  match List.rev hs.hs_s.s_node with
  | [] -> error_message ()
  | i :: r ->
    match i.i_node with
    | Swhile (e,c) ->
      let m = EcMemory.memory hs.hs_me in
      let e = form_of_expr m e in
      (* the body preserve the invariant *)
      let b_pre  = f_and_simpl inv e in
      let b_post = inv in
      let b_concl = f_hoareS hs.hs_me b_pre c b_post in
      let (juc,nb) = new_goal juc (hyps,b_concl) in
      (* the wp of the while *)
      let post = f_imp_simpl (f_not_simpl e) (f_imp_simpl inv hs.hs_post) in
      let post = generalize_mod env m (s_write env PV.empty c) post in
      let post = f_and_simpl inv post in
      let concl = f_hoareS hs.hs_me hs.hs_pre (stmt (List.rev r)) post in
      let (juc,n) = new_goal juc (hyps,concl) in
      let rule = { pr_name = RN_hl_while inv; 
                   pr_hyps=[RA_node nb;RA_node n;]} in
      upd_rule rule (juc, n1)
    | _ -> error_message ()




(*
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
          let mods = modified_pvars EcFol.mhr c in
          let f (pv,m,ty) pvs  = PVset.add (pv,m,ty) pvs in
          (* let mods = PVset.fold f mods PVset.empty in *)
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






*)
