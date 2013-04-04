open EcParsetree
open EcUtils
open EcIdent
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

let s_last destr_i error s =
  match List.rev s.s_node with
  | [] -> error ()
  | i :: r ->
    try destr_i i, rstmt r 
    with Not_found -> error ()

let s_lasts destr_i error sl sr =
  let hl,tl = s_last destr_i error sl in
  let hr,tr = s_last destr_i error sr in
  hl,hr,tl,tr

let last_error si st () = 
  cannot_apply st ("the last instruction should be a"^si)

let s_last_rnd     st = s_last  destr_rnd    (last_error " rnd" st)
let s_last_rnds    st = s_lasts destr_rnd    (last_error " rnd" st)
let s_last_call    st = s_last  destr_call   (last_error " call" st)
let s_last_calls   st = s_lasts destr_call   (last_error " call" st)
let s_last_if      st = s_last  destr_if     (last_error "n if" st)
let s_last_ifs     st = s_lasts destr_if     (last_error "n if" st)
let s_last_while   st = s_last  destr_while  (last_error " while" st)
let s_last_whiles  st = s_lasts destr_while  (last_error " while" st)
let s_last_assert  st = s_last  destr_assert (last_error "n assert" st)
let s_last_asserts st = s_lasts destr_assert (last_error "n assert" st)
 
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
      rstmt r', mk_let env letsf
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
    rstmt r', mk_let env letsf

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

(* -------------------------------------------------------------------- *)
(* -------------------------  Tactics --------------------------------- *)
(* -------------------------------------------------------------------- *)

let prove_goal_by sub_gs rule (juc, n as g) =
  let hyps,_ = get_goal g in
  let add_sgoal (juc,ns) sg = 
    let juc,n = new_goal juc (hyps,sg) in juc, RA_node n::ns
  in
  let juc,ns = List.fold_left add_sgoal (juc,[]) sub_gs in
  let rule = { pr_name = rule ; pr_hyps = List.rev ns} in
  upd_rule rule (juc,n)


let t_hoareF_fun_def env g = 
  let concl = get_concl g in
  let hf = destr_hoareF concl in
  let memenv, fdef, env = Fun.hoareS hf.hf_f env in (* FIXME catch exception *)
  let m = EcMemory.memory memenv in
  let fres = 
    match fdef.f_ret with
    | None -> f_tt
    | Some e -> form_of_expr m e in
  let post = PVM.subst1 env (pv_res hf.hf_f) m fres hf.hf_po in
  let concl' = f_hoareS memenv hf.hf_pr fdef.f_body post in
  prove_goal_by [concl'] RN_hl_fun_def g


let t_equivF_fun_def env g = 
  let concl = get_concl g in
  let ef = destr_equivF concl in
  let memenvl,fdefl,memenvr,fdefr,env = Fun.equivS ef.ef_fl ef.ef_fr env in 
                                (* FIXME catch exception *)
  let ml, mr = EcMemory.memory memenvl, EcMemory.memory memenvr in
  let fresl = 
    match fdefl.f_ret with
    | None -> f_tt
    | Some e -> form_of_expr ml e in
  let fresr = 
    match fdefr.f_ret with
    | None -> f_tt
    | Some e -> form_of_expr mr e in
  let s = PVM.add env (pv_res ef.ef_fl) ml fresl PVM.empty in
  let s = PVM.add env (pv_res ef.ef_fr) mr fresr s in
  let post = PVM.subst env s ef.ef_po in
  let concl' = 
    f_equivS memenvl memenvr ef.ef_pr fdefl.f_body fdefr.f_body post in
  prove_goal_by [concl'] RN_hl_fun_def g


let t_fun_def env g =
  let concl = get_concl g in
  if is_hoareF concl then t_hoareF_fun_def env g
  else if is_equivF concl then t_equivF_fun_def env g
  else tacerror (NotPhl None)

(* -------------------------------------------------------------------- *)
  
let t_hoare_skip g =
  let concl = get_concl g in
  let hs = destr_hoareS concl in
  if hs.hs_s.s_node <> [] then tacerror NoSkipStmt;
  let concl = f_imp hs.hs_pr hs.hs_po in
  let (m,mt) = hs.hs_m in 
  let concl = f_forall [(m,GTmem mt)] concl in
  prove_goal_by [concl] RN_hl_skip g


let t_equiv_skip g =
  let concl = get_concl g in
  let es = destr_equivS concl in
  if es.es_sl.s_node <> [] then tacerror NoSkipStmt;
  if es.es_sr.s_node <> [] then tacerror NoSkipStmt;
  let concl = f_imp es.es_pr es.es_po in
  let (ml,mtl) = es.es_ml in 
  let (mr,mtr) = es.es_mr in 
  let concl = f_forall [(ml,GTmem mtl); (mr,GTmem mtr)] concl in
  prove_goal_by [concl] RN_hl_skip g


let t_skip = t_hS_or_eS t_hoare_skip t_equiv_skip 

(* -------------------------------------------------------------------- *)

let s_split_i msg i s = 
  let len = List.length s.s_node in
  if not (0 < i && i <= len) then tacerror (InvalidCodePosition (msg,i,1,len));
  let hd,tl = s_split (i-1) s in
  hd, List.hd tl, (List.tl tl)

let s_split msg i s =
  let len = List.length s.s_node in
  if i < 0 ||  len < i then tacerror (InvalidCodePosition (msg,i,0,len))
  else s_split i s

let s_split_o msg i s = 
  match i with
  | None -> [], s.s_node
  | Some i -> s_split msg i s 

(* -------------------------------------------------------------------- *)

let t_hoare_app i phi g =
  let concl = get_concl g in
  let hs = destr_hoareS concl in
  let s1,s2 = s_split "app" i hs.hs_s in
  let a = f_hoareS_r { hs with hs_s = stmt s1; hs_po = phi }  in
  let b = f_hoareS_r { hs with hs_pr = phi; hs_s = stmt s2 } in
  prove_goal_by [a;b] (RN_hl_append (Single i,phi)) g


let t_equiv_app (i,j) phi g =
  let concl = get_concl g in
  let es = destr_equivS concl in
  let sl1,sl2 = s_split "app" i es.es_sl in
  let sr1,sr2 = s_split "app" j es.es_sr in
  let a = f_equivS_r {es with es_sl=stmt sl1; es_sr=stmt sr1; es_po=phi} in
  let b = f_equivS_r {es with es_pr=phi; es_sl=stmt sl2; es_sr=stmt sr2} in
  prove_goal_by [a;b] (RN_hl_append (Double (i,j), phi)) g

  
(* -------------------------------------------------------------------- *)


let check_wp_progress msg i s remain =
  match i with
  | None -> List.length s.s_node - List.length remain
  | Some i ->
    let len = List.length remain in
    if len = 0 then i
    else
      cannot_apply msg 
        (Format.sprintf "remaining %i instruction%s" len 
           (if len = 1 then "" else "s"))

let t_hoare_wp env i g =
  let concl = get_concl g in
  let hs = destr_hoareS concl in
  let s_hd,s_wp = s_split_o "wp" i hs.hs_s in
  let s_wp,post = 
    wp env (EcMemory.memory hs.hs_m) (EcModules.stmt s_wp) hs.hs_po in
  let i = check_wp_progress "wp" i hs.hs_s s_wp in
  let s = EcModules.stmt (s_hd @ s_wp) in
  let concl = f_hoareS_r { hs with hs_s = s; hs_po = post} in
  prove_goal_by [concl] (RN_hl_wp (Single i)) g


let t_equiv_wp env ij g = 
  let concl = get_concl g in
  let es = destr_equivS concl in
  let i = omap ij fst and j = omap ij snd in
  let s_hdl,s_wpl = s_split_o "wp" i es.es_sl in
  let s_hdr,s_wpr = s_split_o "wp" j es.es_sr in
  let s_wpl,post = 
    wp env (EcMemory.memory es.es_ml) (EcModules.stmt s_wpl) es.es_po in
  let s_wpr, post =
    wp env (EcMemory.memory es.es_mr) (EcModules.stmt s_wpr) post in
  let i = check_wp_progress "wp" i es.es_sl s_wpl in
  let j = check_wp_progress "wp" j es.es_sr s_wpr in
  let sl = EcModules.stmt (s_hdl @ s_wpl) in
  let sr = EcModules.stmt (s_hdr @ s_wpr) in
  let concl = f_equivS_r {es with es_sl = sl; es_sr=sr; es_po = post} in
  prove_goal_by [concl] (RN_hl_wp (Double(i,j))) g

let t_wp env k =
  match k with
  | None -> t_hS_or_eS (t_hoare_wp env None) (t_equiv_wp env None)
  | Some (Single i) -> t_hoare_wp env (Some i)
  | Some (Double(i,j)) -> t_equiv_wp env (Some (i,j))

(* -------------------------------------------------------------------- *)
  
let t_hoare_while env inv g =
  let concl = get_concl g in
  let hs = destr_hoareS concl in
  let ((e,c),s) = s_last_while "while" hs.hs_s in
  let m = EcMemory.memory hs.hs_m in
  let e = form_of_expr m e in
      (* the body preserve the invariant *)
  let b_pre  = f_and_simpl inv e in
  let b_post = inv in
  let b_concl = f_hoareS hs.hs_m b_pre c b_post in
      (* the wp of the while *)
  let post = f_imps_simpl [f_not_simpl e; inv] hs.hs_po in
  let modi = s_write env PV.empty c in
  let post = generalize_mod env m modi post in
  let post = f_and_simpl inv post in
  let concl = f_hoareS_r { hs with hs_s = s; hs_po=post} in
  prove_goal_by [b_concl;concl] (RN_hl_while inv) g

let t_equiv_while env inv g =
  let concl = get_concl g in
  let es = destr_equivS concl in
  let (el,cl), (er,cr), sl, sr = s_last_whiles "while" es.es_sl es.es_sr in
  let ml = EcMemory.memory es.es_ml in
  let mr = EcMemory.memory es.es_mr in
  let el = form_of_expr ml el in
  let er = form_of_expr mr er in
  let sync_cond = f_iff_simpl el er in
      (* the body preserve the invariant *)
  let b_pre  = f_ands_simpl [inv; el] er in
  let b_post = f_and_simpl inv sync_cond in
  let b_concl = f_equivS es.es_ml es.es_mr b_pre cl cr b_post in
      (* the wp of the while *)
  let post = 
    f_imps_simpl [f_not_simpl el;f_not_simpl er; inv] es.es_po in
  let modil = s_write env PV.empty cl in
  let modir = s_write env PV.empty cr in
  let post = generalize_mod env mr modir post in
  let post = generalize_mod env ml modil post in
  let post = f_and_simpl inv post in
  let concl = f_equivS_r {es with es_sl = sl; es_sr = sr; es_po = post} in
  prove_goal_by [b_concl; concl] (RN_hl_while inv) g 

(* -------------------------------------------------------------------- *)

let wp_asgn_call env m lv res post =
  match lv with
  | None -> post
  | Some lv ->
    let lpe,se = lv_subst env m lv res in
    mk_let env ([lpe],se,post)

let subst_args_call env m f =
  List.fold_right2 (fun v e s ->
    PVM.add_none env (pv_loc f v.v_name) m (form_of_expr m e) s)
  
let t_hoare_call env fpre fpost (juc,n1 as g) =
  (* FIXME : check the well formess of the pre and the post ? *)
  let hyps,concl = get_goal g in
  let hs = destr_hoareS concl in
  let (lp,f,args),s = s_last_call "call" hs.hs_s in
  let m = EcMemory.memory hs.hs_m in
  let fsig = (Fun.by_mpath f env).f_sig in
  (* The function satisfies the specification *)
  let f_concl = f_hoareF fpre f fpost in
  let juc,nf = new_goal juc (hyps, f_concl) in
  (* The wp *)
  let pvres = pv_res f in
  let vres = EcIdent.create "result" in
  let fres = f_local vres (snd fsig.fs_sig) in
  let post = wp_asgn_call env m lp fres hs.hs_po in
  let fpost = PVM.subst1 env pvres m fres fpost in 
  let modi = f_write env f in
  let post = generalize_mod env m modi (f_imp_simpl fpost post) in
  let spre = subst_args_call env m f (fst fsig.fs_sig) args PVM.empty in
  let post = f_anda_simpl (PVM.subst env spre fpre) post in
  let concl = f_hoareS_r { hs with hs_s = s; hs_po=post} in
  let (juc,n) = new_goal juc (hyps,concl) in
  let rule = { pr_name = RN_hl_call (fpre, fpost); 
               pr_hyps =[RA_node nf;RA_node n;]} in
  upd_rule rule (juc, n1)

let t_equiv_call env fpre fpost (juc,n1 as g) =
  (* FIXME : check the well formess of the pre and the post ? *)
  let hyps,concl = get_goal g in
  let es = destr_equivS concl in
  let (lpl,fl,argsl),(lpr,fr,argsr),sl,sr = 
    s_last_calls "call" es.es_sl es.es_sr in
  let ml = EcMemory.memory es.es_ml in
  let mr = EcMemory.memory es.es_mr in
  let fsigl = (Fun.by_mpath fl env).f_sig in
  let fsigr = (Fun.by_mpath fr env).f_sig in
  (* The functions satisfies the specification *)
  let f_concl = f_equivF fpre fl fr fpost in
  let juc,nf = new_goal juc (hyps, f_concl) in
  (* The wp *)
  let pvresl = pv_res fl and pvresr = pv_res fr in
  let vresl = EcIdent.create "result_L" in
  let vresr = EcIdent.create "result_R" in
  let fresl = f_local vresl (snd fsigl.fs_sig) in
  let fresr = f_local vresr (snd fsigr.fs_sig) in
  let post = wp_asgn_call env ml lpl fresl es.es_po in
  let post = wp_asgn_call env mr lpr fresr post in
  let s    = 
    PVM.add env pvresl ml fresl (PVM.add env pvresr mr fresr PVM.empty) in   
  let fpost = PVM.subst env s fpost in 
  let modil = f_write env fl in
  let modir = f_write env fr in
  let post = generalize_mod env mr modir (f_imp_simpl fpost post) in
  let post = generalize_mod env ml modil post in
  let spre = subst_args_call env ml fl (fst fsigl.fs_sig) argsl PVM.empty in
  let spre = subst_args_call env mr fr (fst fsigr.fs_sig) argsr spre in
  let post = f_anda_simpl (PVM.subst env spre fpre) post in
  let concl = f_equivS_r { es with es_sl = sl; es_sr = sr; es_po=post} in
  let (juc,n) = new_goal juc (hyps,concl) in
  let rule = { pr_name = RN_hl_call (fpre, fpost); 
               pr_hyps =[RA_node nf;RA_node n;]} in
  upd_rule rule (juc, n1)







(* -------------------------------------------------------------------- *)


let gen_rcond b m at_pos s =
  let head, i, tail = s_split_i "rcond" at_pos s in 
  let e, s = 
    match i.i_node with
    | Sif(e,s1,s2) -> e, if b then s1.s_node else s2.s_node
    | Swhile(e,s1) -> e, if b then s1.s_node@[i] else [] 
    | _ -> 
      cannot_apply "rcond" 
        (Format.sprintf "the %ith instruction is not a conditionnal" at_pos) in
  let e = form_of_expr m e in
  let e = if b then e else f_not e in
  stmt head, e, stmt (head@s@tail)
  
let t_hoare_rcond b at_pos g = 
  (* TODO: generalize the rule using assume *)
  let concl = get_concl g in
  let hs = destr_hoareS concl in
  let m  = EcMemory.memory hs.hs_m in 
  let hd,e,s = gen_rcond b m at_pos hs.hs_s in
  let concl1  = f_hoareS_r { hs with hs_s = hd; hs_po = e } in
  let concl2  = f_hoareS_r { hs with hs_s = s } in
  prove_goal_by [concl1;concl2] (RN_hl_rcond (None, b,at_pos)) g  

let t_equiv_rcond side b at_pos g =
  let concl = get_concl g in
  let es = destr_equivS concl in
  let m,mo,s = 
    if side then es.es_ml,es.es_mr, es.es_sl 
    else         es.es_mr,es.es_ml, es.es_sr in
  let hd,e,s = gen_rcond b EcFol.mhr at_pos s in 
  let mo' = EcIdent.create "m" in
  let s1 = 
    Mid.add (EcMemory.memory mo) mo' 
      (Mid.add (EcMemory.memory m) EcFol.mhr Mid.empty) in
  let pre1  = f_subst {f_subst_id with fs_mem = s1} es.es_pr in
  let concl1 = 
    f_forall [mo',GTmem (EcMemory.memtype mo)] 
      (f_hoareS (EcFol.mhr,EcMemory.memtype m) pre1 hd e) in
  let sl,sr = if b then s, es.es_sr else es.es_sl, s in
  let concl2 = f_equivS_r { es with es_sl = sl; es_sr = sr } in
  prove_goal_by [concl1;concl2] (RN_hl_rcond (Some side,b,at_pos)) g 

let t_rcond side b at_pos g =
  match side with
  | None -> t_hoare_rcond b at_pos g
  | Some side -> t_equiv_rcond side b at_pos g

(* -------------------------------------------------------------------- *)

let t_hoare_case f g =
  let concl = get_concl g in
  let hs = destr_hoareS concl in
  let concl1 = f_hoareS_r { hs with hs_pr = f_and_simpl hs.hs_pr f } in
  let concl2 = f_hoareS_r { hs with hs_pr = f_and_simpl hs.hs_pr (f_not f) } in
  prove_goal_by [concl1;concl2] (RN_hl_case f) g

let t_equiv_case f g = 
  let concl = get_concl g in
  let es = destr_equivS concl in
  let concl1 = f_equivS_r { es with es_pr = f_and_simpl es.es_pr f } in
  let concl2 = f_equivS_r { es with es_pr = f_and_simpl es.es_pr (f_not f) } in
  prove_goal_by [concl1;concl2] (RN_hl_case f) g

(* -------------------------------------------------------------------- *)

(* TODO : define it in term of case and rcond *)
let t_hoare_cond g =
  let concl = get_concl g in
  let hs = destr_hoareS concl in 
  let s = hs.hs_s.s_node in
  match s with 
    | [] -> assert false (* FIXME *)
    | c :: s_tail' ->
      match c.i_node with 
        | Sif (e,ct,cf) ->
          let e = form_of_expr EcFol.mhr e in
          let st = stmt (ct.s_node @ s_tail') in
          let sf = stmt (cf.s_node @ s_tail') in
          let f1 = f_hoareS hs.hs_m (f_and hs.hs_pr e) st hs.hs_po in
          let f2 = f_hoareS hs.hs_m (f_and hs.hs_pr (f_not e)) sf hs.hs_po in
          prove_goal_by [f1;f2] RN_hl_cond g
        | _ -> assert false (* FIXME *)


let t_equiv_cond side g =
  let concl = get_concl g in
  let es = destr_equivS concl in
  match side with
    | Some _ -> assert false
    | None -> 
      let sl,sr = es.es_sl, es.es_sr in
      match sl.s_node,sr.s_node with
        | [],_ | _,[] -> assert false (* FIXME *)
        | il::sl, ir::sr ->
          match il.i_node, ir.i_node with
            | Sif(el,ctl,cfl), Sif(er,ctr,cfr) ->
              let el = form_of_expr (EcMemory.memory es.es_ml) el in
              let er = form_of_expr (EcMemory.memory es.es_mr) er in
              let stl = stmt (ctl.s_node @ sl) in
              let sfl = stmt (cfl.s_node @ sl) in
              let str = stmt (ctr.s_node @ sr) in
              let sfr = stmt (cfr.s_node @ sr) in
              let f = f_imp es.es_pr (f_eq el er) in
              let f1 = f_equivS es.es_ml es.es_mr 
                (f_and es.es_pr (f_and el er)) 
                stl str es.es_po in
              let f2 = f_equivS es.es_ml es.es_mr 
                (f_and es.es_pr (f_and (f_not el) (f_not er))) 
                sfl sfr es.es_po in
              prove_goal_by [f;f1;f2] RN_hl_cond g

            | _ -> assert false (* FIXME *)

(* -------------------------------------------------------------------- *)
