open EcParsetree
open EcUtils
open EcIdent
open EcCoreLib
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

  type mem_sel = 
  | MSvar of prog_var
  | MSmod of EcPath.mpath (* Only abstract module *)
      
  module M = EcMaps.Map.Make(struct
    (* We assume that the mpath are in normal form *) 
 
    type t = mem_sel * EcMemory.memory

    let ms_compare ms1 ms2 = 
      match ms1, ms2 with
      | MSvar v1, MSvar v2 -> pv_compare_p v1 v2
      | MSmod m1, MSmod m2 -> EcPath.m_compare m1 m2
      | MSvar _, MSmod _ -> -1
      | MSmod _, MSvar _ -> 1

    let compare (p1,m1) (p2,m2) = 
      let r = EcIdent.id_compare m1 m2 in
      if r = 0 then ms_compare p1 p2 
      else r
  end)

  type subst = form M.t

  let empty = M.empty 

  let pvm env pv m = 
    let pv = EcEnv.NormMp.norm_pvar env pv in 
    (MSvar pv, m)

  let add env pv m f s = M.add (pvm env pv m) f s 

  let add_glob _env mp m f s = M.add (MSmod mp, m) f s

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
      | Fglob(mp,m) ->
        let f' = EcEnv.NormMp.norm_glob env m mp in
        if f_equal f f' then
          (try M.find (MSmod mp,m) s with Not_found -> f)
        else aux f'
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

  type pv_fv = 
    { pv : ty M.t;         (* The key are in normal form *)
      glob : EcPath.Sm.t;  (* The set of abstract module *)
    }

  let empty = 
    { pv = M.empty;
      glob = EcPath.Sm.empty }

  let add env pv ty fv = 
    { fv with pv = M.add (NormMp.norm_pvar env pv) ty fv.pv }

  let add_glob env mp fv =
    { fv with glob = EcPath.Sm.add (NormMp.norm_mpath env mp) fv.glob}

  let remove env pv fv =
    { fv with pv = M.remove (NormMp.norm_pvar env pv) fv.pv }

  let union _env fv1 fv2 =
    { pv = M.merge (fun _ o1 o2 -> if o2 = None then o1 else o2) fv1.pv fv2.pv;
      glob = EcPath.Sm.union fv1.glob fv2.glob }

  let disjoint _env fv1 fv2 = 
    M.set_disjoint fv1.pv fv2.pv &&
      (* FIXME not suffisant use disjoint_g *)
      EcPath.Sm.disjoint fv1.glob fv2.glob

  let diff _env fv1 fv2 = 
    { pv = M.set_diff fv1.pv fv2.pv;
      glob = EcPath.Sm.diff fv1.glob fv2.glob }

  let inter _env fv1 fv2 = 
    { pv = M.set_inter fv1.pv fv2.pv;
      glob = EcPath.Sm.inter fv1.glob fv2.glob }

  let elements fv = M.bindings fv.pv, EcPath.Sm.elements fv.glob (* FIXME *)

  let fv env m f =
    let rec aux fv f = 
      match f.f_node with
      | Fquant(_,_,f1) -> aux fv f1
      | Fif(f1,f2,f3) -> aux (aux (aux fv f1) f2) f3
      | Flet(_,f1,f2) -> aux (aux fv f1) f2
      | Fpvar(x,m') -> 
        if EcIdent.id_equal m m' then add env x f.f_ty fv else fv
      | Fglob (mp,m') ->
        if EcIdent.id_equal m m' then 
          let f' = EcEnv.NormMp.norm_glob env m mp in
          if f_equal f f' then add_glob env mp fv
          else aux fv f'
        else fv
      | Fint _ | Flocal _ | Fop _ -> fv
      | Fapp(e, es) -> List.fold_left aux (aux fv e) es
      | Ftuple es   -> List.fold_left aux fv es
      | FhoareF _  | FhoareS _ | FbdHoareF _  | FbdHoareS _ 
      | FequivF _ | FequivS _ | Fpr _ -> assert false 
    in
    aux empty f

  let disjoint_g env mp1 mp2 = 
    let me1, me2 = EcEnv.Mod.by_mpath mp1 env, EcEnv.Mod.by_mpath mp2 env in
    match me1.me_body, me2.me_body with
    | ME_Decl(_,nu1), ME_Decl(_,nu2) ->
      EcPath.Sm.mem mp2 nu1 || EcPath.Sm.mem mp1 nu2
    | ME_Decl(_,nu1), ME_Structure ms2 ->
      EcPath.Sm.mem mp2 nu1 &&
        EcPath.Sm.for_all (fun m -> EcPath.Sm.mem m nu1) ms2.ms_uses
    | ME_Structure ms1, ME_Decl(_,nu2) ->
      EcPath.Sm.mem mp1 nu2 &&
        EcPath.Sm.for_all (fun m -> EcPath.Sm.mem m nu2) ms1.ms_uses
    | ME_Structure ms1, ME_Structure ms2 ->
      let us1 = EcPath.Sm.add mp1 ms1.ms_uses in
      let us2 = EcPath.Sm.add mp2 ms2.ms_uses in
      EcPath.Sm.disjoint us1 us2 
    | _, _ -> assert false 
      
  let check env modi fv = 
    let not_gen = diff env fv modi in 
    let mk_topv s = 
      M.fold (fun x _ topv ->
        if is_loc x then topv 
        else
          let x=x.pv_name in
          let top = EcPath.m_functor x.EcPath.x_top in
          EcPath.Sm.add top topv) s EcPath.Sm.empty in
    let topv = mk_topv not_gen.pv in
    let topvg = mk_topv modi.pv in
    let topm = not_gen.glob in
    
    let check s1 s2 = 
      EcPath.Sm.for_all (fun mp1 ->
        EcPath.Sm.for_all (fun mp2 -> disjoint_g env mp1 mp2) s1) s2 in

    (* FIXME error message *)
    assert (check modi.glob topv);
    assert (check modi.glob topm);
    assert (check topvg topm)
      
  let check_depend env fv mp = 
    (* FIXME error message *)
    let check_v v _ty =
      assert (is_glob v);
      let top = EcPath.m_functor v.pv_name.EcPath.x_top in
      assert (disjoint_g env mp top) in
    M.iter check_v fv.pv;
    let check_m m = assert (disjoint_g env mp m) in
    EcPath.Sm.iter check_m fv.glob 

end

let get_abs_functor f = 
  let f = f.EcPath.x_top in
  match f.EcPath.m_top with
  | `Abstract _ -> EcPath.mpath (f.EcPath.m_top) []
  | _ -> assert false

let rec f_write env w f =
  let f = NormMp.norm_xpath env f in
  let func = Fun.by_xpath f env in
  match func.f_def with
  | FBabs oi ->
    let mp = get_abs_functor f in
    List.fold_left (f_write env) (PV.add_glob env mp w) oi.oi_calls
  | FBdef fdef ->
    let add x w = 
      let vb = Var.by_xpath x env in
      PV.add env (pv_glob x) vb.vb_type w in
    let w = EcPath.Sx.fold add fdef.f_uses.us_writes w in
    List.fold_left (f_write env) w fdef.f_uses.us_calls

(* computes the program variables occurring free in f with memory m *)
let rec free_pv_form m env f = 
  let fv = free_pv_form m env in
  match f.f_node with
  | Fpvar (pv,m') when m=m' -> PV.add env pv f.f_ty PV.empty
  | Fquant (_,_,f) 
    -> fv f
  | Fif (f1,f2,f3) 
    -> PV.union env (fv f1) (PV.union env (fv f2) (fv f3))
  | Flet (_,f1,f2)
    -> PV.union env (fv f1) (fv f2)
  | Fapp (f,fs) 
    -> List.fold_left (fun s f -> PV.union env (fv f) s) (fv f) fs
  | Ftuple fs 
    -> List.fold_left (fun s f -> PV.union env (fv f) s) PV.empty fs
  | Fint _ | Flocal _ | Fglob _ | Fop _ | Fpvar _ 
    -> PV.empty
  | FhoareF _ | FhoareS _
  | FbdHoareF _ | FbdHoareS _
  | FequivF _ | FequivS _
  | Fpr _ -> assert false (* FIXME: extend if necessary *)

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
    let w  = match lp with None -> w | Some lp -> lp_write env w lp in    
    f_write env w f 
  | Sif (_,s1,s2) -> s_write env (s_write env w s1) s2
  | Swhile (_,s) -> s_write env w s
  | Sassert _ -> w 
    
let rec f_read env r f = 
  let f = NormMp.norm_xpath env f in
  let func = Fun.by_xpath f env in
  match func.f_def with
  | FBabs oi ->
    let mp = get_abs_functor f in
    List.fold_left (f_read env) (PV.add_glob env mp r) oi.oi_calls
  | FBdef fdef ->
    let add x r = 
      let vb = Var.by_xpath x env in
      PV.add env (pv_glob x) vb.vb_type r in
    let r = EcPath.Sx.fold add fdef.f_uses.us_reads r in
    List.fold_left (f_read env) r fdef.f_uses.us_calls

let rec e_read env r e = 
  match e.e_node with
  | Evar pv -> PV.add env pv e.e_ty r
  | _ -> e_fold (e_read env) r e

let lp_read env r lp = 
  match lp with
  | LvVar _ -> r
  | LvTuple _ -> r
  | LvMap ((_,_),pv,e,ty) -> e_read env (PV.add env pv ty r) e

let rec s_read env w s = List.fold_left (i_read env) w s.s_node 

and i_read env r i = 
  match i.i_node with
  | Sasgn (lp,e) -> e_read env (lp_read env r lp) e
  | Srnd (lp,e)  -> e_read env (lp_read env r lp) e 
  | Scall(lp,f,es) -> 
    let r = List.fold_left (e_read env) r es in
    let r  = match lp with None -> r | Some lp -> lp_read env r lp in
    f_read env r f 
  | Sif (e,s1,s2) -> s_read env (s_read env (e_read env r e) s1) s2
  | Swhile (e,s) -> s_read env (e_read env r e) s
  | Sassert e -> e_read env r e
    

let f_write env f = f_write env PV.empty f
let f_read  env f = f_read  env PV.empty f
let s_write env s = s_write env PV.empty s
let s_read  env s = s_read  env PV.empty s

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
  EcIdent.create (EcPath.basename pv.pv_name.EcPath.x_sub) 

let id_of_mp mp = 
  match mp.EcPath.m_top with
  | `Abstract id -> EcIdent.fresh id
  | _ -> assert false 

let generalize_mod env m modi f =
  let fv = PV.fv env m f in
  PV.check env modi fv;
  let elts,glob = PV.elements modi in
  let create (pv,ty) = id_of_pv pv, GTty ty in
  let b = List.map create elts in
  let s = List.fold_left2 (fun s (pv,ty) (id, _) ->
    PVM.add env pv m (f_local id ty) s) PVM.empty elts b in
  let create mp = id_of_mp mp, GTty (tglob mp) in
  let b' = List.map create glob in
  let s = List.fold_left2 (fun s mp (id,_) ->
    PVM.add_glob env mp m (f_local id (tglob mp)) s) s glob b' in
  let f = PVM.subst env s f in
  f_forall_simpl (b'@b) f


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

(* wp functions operates only over assignments and conditional statements.
   Any weakening on this restriction may break the soundness of bounded hoare logic 
*)
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



(* let subst_form env m lv e f = *)
(*   let s = PVM.add env "pv" PVM.empty in *)
(*   mk_let env letsf *)

let subst_form_lv env m lv t f =
  let lpe, se = lv_subst env m lv t in
  let s = PVM.merge se PVM.empty in
  mk_let env ([lpe], s,f)

  

(* -------------------------------------------------------------------- *)
(* ----------------------  Auxiliary functions  ----------------------- *)
(* -------------------------------------------------------------------- *)

let destr_hoareF c =
  try destr_hoareF c with DestrError _ -> tacerror (NotPhl (Some true))
let destr_hoareS c =
  try destr_hoareS c with DestrError _ -> tacerror (NotPhl (Some true))
let destr_bdHoareF c =
  try destr_bdHoareF c with DestrError _ -> tacerror (NotPhl (Some true))
let destr_bdHoareS c =
  try destr_bdHoareS c with DestrError _ -> tacerror (NotPhl (Some true))
let destr_equivF c =
  try destr_equivF c with DestrError _ -> tacerror (NotPhl (Some false))
let destr_equivS c =
  try destr_equivS c with DestrError _ -> tacerror (NotPhl (Some false))

let t_hS_or_eS th te g =
  let concl = get_concl g in
  if is_hoareS concl then th g
  else if is_equivS concl then te g
  else tacerror (NotPhl None)

let t_hS_or_bhS th te g =
  let concl = get_concl g in
  if is_hoareS concl then th g
  else if is_bdHoareS concl then te g
  else tacerror (NotPhl None)

let t_hS_or_bhS_or_eS th tbh te g =
  let concl = get_concl g in
  if is_hoareS concl then th g
  else if is_bdHoareS concl then tbh g
  else if is_equivS concl then te g
  else tacerror (NotPhl None)



let prove_goal_by sub_gs rule (juc,n as g) =
  let hyps,_ = get_goal g in
  let add_sgoal (juc,ns) sg = 
    let juc,n = new_goal juc (hyps,sg) in juc, RA_node n::ns
  in
  let juc,ns = List.fold_left add_sgoal (juc,[]) sub_gs in
  let rule = { pr_name = rule ; pr_hyps = List.rev ns} in
  upd_rule rule (juc,n)

let gen_mems m f = 
  let bds = List.map (fun (m,mt) -> (m,GTmem mt)) m in
  f_forall bds f

(* -------------------------------------------------------------------- *)
(* -------------------------  Tactics --------------------------------- *)
(* -------------------------------------------------------------------- *)

(* {spre} . {spost}     pre => spre  spost => post
   --------------------------------------------------
       {pre} . {post} 
*)
let conseq_cond pre post spre spost = 
  f_imp pre spre, f_imp spost post
 
let t_hoareF_conseq env pre post g =
  let hyps,concl = get_goal g in
  let hf = destr_hoareF concl in
  let env = tyenv_of_hyps env hyps in
  let mpr,mpo = EcEnv.Fun.hoareF_memenv hf.hf_f env in
  let cond1, cond2 = conseq_cond hf.hf_pr hf.hf_po pre post in
  let concl1 = gen_mems [mpr] cond1 in
  let concl2 = gen_mems [mpo] cond2 in
  let concl3 = f_hoareF pre hf.hf_f post in
  prove_goal_by [concl1; concl2; concl3] (RN_hl_conseq) g  
    

let t_hoareS_conseq _env pre post g =
  let concl = get_concl g in
  let hs = destr_hoareS concl in
  let cond1, cond2 = conseq_cond hs.hs_pr hs.hs_po pre post in
  let concl1 = gen_mems [hs.hs_m] cond1 in
  let concl2 = gen_mems [hs.hs_m] cond2 in
  let concl3 = f_hoareS_r { hs with hs_pr = pre; hs_po = post } in
  prove_goal_by [concl1; concl2; concl3] (RN_hl_conseq) g


let t_equivF_conseq env pre post g =
  let hyps,concl = get_goal g in
  let ef = destr_equivF concl in
  let env = tyenv_of_hyps env hyps in
  let (mprl,mprr),(mpol,mpor) = EcEnv.Fun.equivF_memenv ef.ef_fl ef.ef_fr env in
  let cond1, cond2 = conseq_cond ef.ef_pr ef.ef_po pre post in
  let concl1 = gen_mems [mprl;mprr] cond1 in
  let concl2 = gen_mems [mpol;mpor] cond2 in
  let concl3 = f_equivF pre ef.ef_fl ef.ef_fr post in
  prove_goal_by [concl1; concl2; concl3] (RN_hl_conseq) g  

let t_equivS_conseq _env pre post g =
  let concl = get_concl g in
  let es = destr_equivS concl in
  let cond1, cond2 = conseq_cond es.es_pr es.es_po pre post in
  let concl1 = gen_mems [es.es_ml;es.es_mr] cond1 in
  let concl2 = gen_mems [es.es_ml;es.es_mr] cond2 in
  let concl3 = f_equivS_r { es with es_pr = pre; es_po = post } in
  prove_goal_by [concl1; concl2; concl3] (RN_hl_conseq) g
 
(* -------------------------------------------------------------------- *)

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

let t_bdHoareF_fun_def env g = 
  let concl = get_concl g in
  let bhf = destr_bdHoareF concl in
  let memenv, fdef, env = Fun.hoareS bhf.bhf_f env in (* FIXME catch exception *)
  let m = EcMemory.memory memenv in
  let fres = 
    match fdef.f_ret with
    | None -> f_tt
    | Some e -> form_of_expr m e in
  let post = PVM.subst1 env (pv_res bhf.bhf_f) m fres bhf.bhf_po in
  let concl' = f_bdHoareS memenv bhf.bhf_pr fdef.f_body post bhf.bhf_cmp bhf.bhf_bd  in
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
  else if is_bdHoareF concl then t_bdHoareF_fun_def env g
  else if is_equivF concl then t_equivF_fun_def env g
  else tacerror (NotPhl None)

  
(* TODO FIXME : oracle should ensure that the adversary state still equal:
   two solutions : 
     - add the equality in the pre and post.
     - ensure that oracle do not write the adversary state
 *)

let check_adv env fl fr = 
  let fl = EcEnv.NormMp.norm_xpath env fl in
  let fr = EcEnv.NormMp.norm_xpath env fr in
  let subl = fl.EcPath.x_sub in
  let subr = fr.EcPath.x_sub in
  let topl = EcPath.m_functor fl.EcPath.x_top in
  let topr = EcPath.m_functor fr.EcPath.x_top in
  assert (EcPath.p_equal subl subr && EcPath.m_equal topl topr);  
  fl,topl,fr,topr
                                               (* FIXME error message *)
 
let equivF_abs_spec env fl fr inv = 
  let fl,topl,fr,topr = check_adv env fl fr in
  let ml, mr = mleft, mright in
  let fvl = PV.fv env ml inv in
  let fvr = PV.fv env mr inv in
  PV.check_depend env fvl topl;
  PV.check_depend env fvr topr;
  (* TODO check there is only global variable *)
  let defl, defr = EcEnv.Fun.by_xpath fl env, EcEnv.Fun.by_xpath fr env in
  let oil, oir = 
    match defl.f_def, defr.f_def with
    | FBabs oil, FBabs oir -> oil, oir
    | _ -> assert false (* FIXME error message *)
  in
  let ospec o_l o_r = 
    let fo_l = EcEnv.Fun.by_xpath o_l env in
    let fo_r = EcEnv.Fun.by_xpath o_r env in
    let eq_params = 
      f_eqparams o_l fo_l.f_sig.fs_params ml o_r fo_r.f_sig.fs_params mr in
    let eq_res = f_eqres o_l fo_l.f_sig.fs_ret ml o_r fo_r.f_sig.fs_ret mr in
    let pre = EcFol.f_and eq_params inv in
    let post = EcFol.f_and eq_res inv in
    f_equivF pre o_l o_r post in
  let sg = List.map2 ospec oil.oi_calls oir.oi_calls in
  let eq_params = 
    f_eqparams fl defl.f_sig.fs_params ml fr defr.f_sig.fs_params mr in
  let eq_res = f_eqres fl defl.f_sig.fs_ret ml fr defr.f_sig.fs_ret mr in
  let eqglob = f_eqglob topl ml topr mr in
  let pre = f_ands [eq_params; eqglob; inv] in
  let post = f_ands [eq_res; eqglob; inv] in
  pre, post, sg

let t_equivF_abs env inv g = 
  let hyps, concl = get_goal g in
  let ef = destr_equivF concl in
  let env' = tyenv_of_hyps env hyps in
  let pre, post, sg = equivF_abs_spec env' ef.ef_fl ef.ef_fr inv in
  let tac g' = prove_goal_by sg (RN_hl_fun_abs inv) g' in
  t_on_last (t_equivF_conseq env pre post g) tac

let equivF_abs_upto env fl fr bad invP invQ = 
  let fl,topl,fr,topr = check_adv env fl fr in
  let ml, mr = mleft, mright in
  let bad2 = f_subst_mem mhr mr bad in
  let allinv = f_ands [bad2; invP; invQ] in
  let fvl = PV.fv env ml allinv in
  let fvr = PV.fv env mr allinv in
  PV.check_depend env fvl topl;
  PV.check_depend env fvr topr;
  (* TODO check there is only global variable *)
  let defl, defr = EcEnv.Fun.by_xpath fl env, EcEnv.Fun.by_xpath fr env in
  let oil, oir = 
    match defl.f_def, defr.f_def with
    | FBabs oil, FBabs oir -> oil, oir
    | _ -> assert false (* FIXME error message *)
  in
  let eqglob = f_eqglob topl ml topr mr in
  let egP    = f_and eqglob invP in
  let ospec o_l o_r = 
    let fo_l = EcEnv.Fun.by_xpath o_l env in
    let fo_r = EcEnv.Fun.by_xpath o_r env in
    let eq_params = 
      f_eqparams o_l fo_l.f_sig.fs_params ml o_r fo_r.f_sig.fs_params mr in
    let eq_res = f_eqres o_l fo_l.f_sig.fs_ret ml o_r fo_r.f_sig.fs_ret mr in
    let pre = EcFol.f_ands [EcFol.f_not bad2; eq_params; egP] in
    let post = EcFol.f_if bad2 invQ (f_and eq_res egP) in
    let cond1 = f_equivF pre o_l o_r post in
    let cond2 =
      let q = f_subst_mem ml EcFol.mhr invQ in
      f_forall [mr,GTmem None] (f_imp bad2 (f_hoareF q o_l q)) in
    let cond3 = 
      let q = f_subst_mem mr EcFol.mhr invQ in
      let bq = f_and bad q in
      f_forall [ml,GTmem None] (f_hoareF bq o_r bq) in
    let cond4 = f_losslessF o_l in
    let cond5 = f_losslessF o_r in
    [cond1;cond2;cond3;cond4;cond5] in
  let sg = List.map2 ospec oil.oi_calls oir.oi_calls in
  let sg = List.flatten sg in
  let lossless_a = 
    let _sig = (EcEnv.Mod.by_mpath topl env).me_sig in
    let bd = 
      List.map (fun (id,mt) -> (id,GTmodty(mt,EcPath.Sm.empty))) 
        _sig.mis_params in               (* Should we put restriction here *)
    let args = List.map (fun (id,_) -> EcPath.mident id) _sig.mis_params in
    let sub = fl.EcPath.x_sub in
    let concl = 
      f_losslessF (EcPath.xpath (EcPath.m_apply topl args) sub ) in
    let calls = 
      let name = EcPath.basename sub in
      let Tys_function(_,oi) = 
        List.find (fun (Tys_function(fs,_)) -> fs.fs_name = name)
          _sig.mis_body in
      oi.oi_calls in
    let hyps = List.map f_losslessF calls in
    f_forall bd (f_imps hyps concl) in
  let sg = lossless_a :: sg in
  let eq_params = 
    f_eqparams fl defl.f_sig.fs_params ml fr defr.f_sig.fs_params mr in
  let eq_res = f_eqres fl defl.f_sig.fs_ret ml fr defr.f_sig.fs_ret mr in
  let pre = f_if bad2 invQ (f_and eq_params egP) in
  let post = f_if bad2 invQ (f_and eq_res egP) in
  pre, post, sg

let t_equivF_abs_upto env bad invP invQ g = 
  let hyps, concl = get_goal g in
  let ef = destr_equivF concl in
  let env' = tyenv_of_hyps env hyps in
  let pre, post, sg = equivF_abs_upto env' ef.ef_fl ef.ef_fr bad invP invQ in
  let tac g' = prove_goal_by sg (RN_hl_fun_upto(bad,invP,invQ)) g' in
  t_on_last (t_equivF_conseq env pre post g) tac


  

  
  
  


(* -------------------------------------------------------------------- *)
  
let t_hoare_skip g =
  let concl = get_concl g in
  let hs = destr_hoareS concl in
  if hs.hs_s.s_node <> [] then tacerror NoSkipStmt;
  let concl = f_imp hs.hs_pr hs.hs_po in
  let concl = gen_mems [hs.hs_m] concl in
  prove_goal_by [concl] RN_hl_skip g

let t_bdHoare_skip g =
  let concl = get_concl g in
  let bhs = destr_bdHoareS concl in
  if bhs.bhs_s.s_node <> [] then tacerror NoSkipStmt;
  if (bhs.bhs_cmp <> FHeq && bhs.bhs_cmp <> FHge) ||
     not (f_equal bhs.bhs_bd f_r1) then
    cannot_apply "skip" "bound must be \">= 1\"";
  let concl = f_imp bhs.bhs_pr bhs.bhs_po in
  let concl = gen_mems [bhs.bhs_m] concl in
  prove_goal_by [concl] RN_hl_skip g

let t_equiv_skip g =
  let concl = get_concl g in
  let es = destr_equivS concl in
  if es.es_sl.s_node <> [] then tacerror NoSkipStmt;
  if es.es_sr.s_node <> [] then tacerror NoSkipStmt;
  let concl = f_imp es.es_pr es.es_po in
  let concl = gen_mems [es.es_ml; es.es_mr] concl in
  prove_goal_by [concl] RN_hl_skip g


let t_skip = t_hS_or_bhS_or_eS t_hoare_skip t_bdHoare_skip t_equiv_skip 

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

let t_bdHoare_wp env i g =
  let concl = get_concl g in
  let bhs = destr_bdHoareS concl in
  let s_hd,s_wp = s_split_o "wp" i bhs.bhs_s in
  let s_wp = EcModules.stmt s_wp in

  let m = EcMemory.memory bhs.bhs_m in

  let fv_bd = free_pv_form m env bhs.bhs_bd in
  let modi = s_write env s_wp in

  if not (PV.disjoint env fv_bd modi) then 
    cannot_apply "wp" "Not_implemented: bound is modified by the statement";

  let s_wp,post = 
    wp env m s_wp bhs.bhs_po in
  let i = check_wp_progress "wp" i bhs.bhs_s s_wp in
  let s = EcModules.stmt (s_hd @ s_wp) in
  let concl = f_bdHoareS_r { bhs with bhs_s = s; bhs_po = post} in
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


let t_wp env k = match k with
  | None -> t_hS_or_bhS_or_eS (t_hoare_wp env None) (t_bdHoare_wp env None) (t_equiv_wp env None)
  | Some (Single i) -> t_hS_or_bhS (t_hoare_wp env (Some i)) (t_bdHoare_wp env (Some i))
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
  let modi = s_write env c in
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
  let post = f_imps_simpl [f_not_simpl el;f_not_simpl er; inv] es.es_po in
  let modil = s_write env cl in
  let modir = s_write env cr in
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
  let fsig = (Fun.by_xpath f env).f_sig in
  (* The function satisfies the specification *)
  let f_concl = f_hoareF fpre f fpost in
  let juc,nf = new_goal juc (hyps, f_concl) in
  (* The wp *)
  let pvres = pv_res f in
  let vres = EcIdent.create "result" in
  let fres = f_local vres fsig.fs_ret in
  let post = wp_asgn_call env m lp fres hs.hs_po in
  let fpost = PVM.subst1 env pvres m fres fpost in 
  let modi = f_write env f in
  let post = generalize_mod env m modi (f_imp_simpl fpost post) in
  let post = f_forall_simpl [(vres, GTty fsig.fs_ret)] post in
  let spre = subst_args_call env m f fsig.fs_params args PVM.empty in
  let post = f_anda_simpl (PVM.subst env spre fpre) post in
  let concl = f_hoareS_r { hs with hs_s = s; hs_po=post} in
  let (juc,n) = new_goal juc (hyps,concl) in
  let rule = { pr_name = RN_hl_call (None, fpre, fpost); 
               pr_hyps =[RA_node nf;RA_node n;]} in
  upd_rule rule (juc, n1)

let t_equiv_call env fpre fpost g =
  (* FIXME : check the well formess of the pre and the post ? *)
  let hyps, concl = get_goal g in
  let env = tyenv_of_hyps env hyps in
  let es = destr_equivS concl in
  let (lpl,fl,argsl),(lpr,fr,argsr),sl,sr = 
    s_last_calls "call" es.es_sl es.es_sr in
  let ml = EcMemory.memory es.es_ml in
  let mr = EcMemory.memory es.es_mr in
  let fsigl = (Fun.by_xpath fl env).f_sig in
  let fsigr = (Fun.by_xpath fr env).f_sig in
  (* The functions satisfy their specification *)
  let f_concl = f_equivF fpre fl fr fpost in
  (* The wp *)
  let pvresl = pv_res fl and pvresr = pv_res fr in
  let vresl = LDecl.fresh_id (get_hyps g) "result_L" in
  let vresr = LDecl.fresh_id (get_hyps g) "result_R" in
  let fresl = f_local vresl fsigl.fs_ret in
  let fresr = f_local vresr fsigr.fs_ret in
  let post = wp_asgn_call env ml lpl fresl es.es_po in
  let post = wp_asgn_call env mr lpr fresr post in
  let s    = 
    PVM.add env pvresl ml fresl (PVM.add env pvresr mr fresr PVM.empty) in   
  let fpost = PVM.subst env s fpost in 
  let modil = f_write env fl in
  let modir = f_write env fr in
  let post = generalize_mod env mr modir (f_imp_simpl fpost post) in
  let post = generalize_mod env ml modil post in
  let post = 
    f_forall_simpl
      [(vresl, GTty fsigl.fs_ret);
       (vresr, GTty fsigr.fs_ret)]
      post in
  let spre = subst_args_call env ml fl fsigl.fs_params argsl PVM.empty in
  let spre = subst_args_call env mr fr fsigr.fs_params argsr spre in
  let post = f_anda_simpl (PVM.subst env spre fpre) post in
  let concl = f_equivS_r { es with es_sl = sl; es_sr = sr; es_po=post} in
  prove_goal_by [f_concl;concl] (RN_hl_call (None, fpre, fpost)) g

let t_equiv_call1 env side fpre fpost g =
  let concl = get_concl g in
  let equiv = destr_equivS concl in

  let (me, stmt) =
    match side with
    | true  -> (EcMemory.memory equiv.es_ml, equiv.es_sl)
    | false -> (EcMemory.memory equiv.es_mr, equiv.es_sr)
  in

  let (lp, f, args), fstmt = s_last_call "call" stmt in
  let fsig = (Fun.by_xpath f env).f_sig in

  (* The function satisfies its specification *)
  let fconcl = f_hoareF fpre f fpost in

  (* WP *)
  let pvres  = pv_res f in
  let vres   = LDecl.fresh_id (get_hyps g) "result" in
  let fres   = f_local vres fsig.fs_ret in
  let post   = wp_asgn_call env me lp fres equiv.es_po in
  let subst  = PVM.add env pvres me fres PVM.empty in
  let msubst = EcFol.f_bind_mem EcFol.f_subst_id EcFol.mhr me in
  let fpost  = PVM.subst env subst (f_subst msubst fpost) in
  let modi   = f_write env f in
  let post   = f_imp_simpl fpost post in
  let post   = generalize_mod env me modi post in
  let spre   = PVM.empty in
  let spre   = subst_args_call env me f fsig.fs_params args spre in
  let post   = f_anda_simpl (PVM.subst env spre (f_subst msubst fpre)) post in
  let concl  =
    match side with
    | true  -> { equiv with es_sl = fstmt; es_po = post; }
    | false -> { equiv with es_sr = fstmt; es_po = post; } in
  let concl  = f_equivS_r concl in
  let concl  = f_forall [(vres, GTty fsig.fs_ret)] concl in
  prove_goal_by [fconcl; concl] (RN_hl_call (Some side, fpre, fpost)) g

(* --------------------------------------------------------------------- *)

let t_hoare_equiv _env p q p1 q1 p2 q2 g =
  let concl = get_concl g in
  let es = destr_equivS concl in
  let s1 = f_bind_mem f_subst_id mhr (fst es.es_ml) in
  let s2 = f_bind_mem f_subst_id mhr (fst es.es_mr) in
  let concl1 = 
    gen_mems [es.es_ml;es.es_mr] 
      (f_imp es.es_pr (f_and p (f_and (f_subst s1 p1) (f_subst s2 p2)))) in
  let concl2 = 
    gen_mems [es.es_ml;es.es_mr]
      (f_imps [q;f_subst s1 q1;f_subst s2 q2] es.es_po) in
  let concl3 = 
    f_hoareS (mhr,snd es.es_ml) p1 es.es_sl q1 in
  let concl4 = 
    f_hoareS (mhr,snd es.es_mr) p2 es.es_sr q2 in
  let concl5 = 
    f_equivS_r { es with es_pr = p; es_po = q } in
  prove_goal_by [concl1; concl2; concl3; concl4; concl5] 
    RN_hl_hoare_equiv g

(*
let t_equiv_mod 
{P} c1 ~ c2 {Q}
P => forall mod, Q => Q' 
-------------------------
{P} c1 ~ c2 {Q'}
*)

(*
let t_equiv_true 
lossless c1
lossless c2
------------------
{P} c1 ~ c2 {true}

*)


(* --------------------------------------------------------------------- *)

let t_hoare_case f g =
  let concl = get_concl g in
  let hs = destr_hoareS concl in
  let concl1 = f_hoareS_r { hs with hs_pr = f_and_simpl hs.hs_pr f } in
  let concl2 = f_hoareS_r { hs with hs_pr = f_and_simpl hs.hs_pr (f_not f) } in
  prove_goal_by [concl1;concl2] (RN_hl_case f) g

let t_bdHoare_case f g =
  let concl = get_concl g in
  let bhs = destr_bdHoareS concl in
  let concl1 = f_bdHoareS_r { bhs with bhs_pr = f_and_simpl bhs.bhs_pr f } in
  let concl2 = f_bdHoareS_r { bhs with bhs_pr = f_and_simpl bhs.bhs_pr (f_not f) } in
  prove_goal_by [concl1;concl2] (RN_hl_case f) g

let t_equiv_case f g = 
  let concl = get_concl g in
  let es = destr_equivS concl in
  let concl1 = f_equivS_r { es with es_pr = f_and es.es_pr f } in
  let concl2 = f_equivS_r { es with es_pr = f_and es.es_pr (f_not f) } in
  prove_goal_by [concl1;concl2] (RN_hl_case f) g

let t_he_case f g =
  t_hS_or_bhS_or_eS (t_hoare_case f) (t_bdHoare_case f) (t_equiv_case f) g 

(* --------------------------------------------------------------------- *)

let _inline_freshen me v =
  let rec for_idx idx =
    let x = Printf.sprintf "%s%d" v.v_name idx in
      if EcMemory.is_bound x me then
        for_idx (idx+1)
      else
        (EcMemory.bind x v.v_type me, x)
  in
    if EcMemory.is_bound v.v_name me then
      for_idx 0
    else
      (EcMemory.bind v.v_name v.v_type me, v.v_name)

let _inline env hyps me sp s =
  let env = tyenv_of_hyps env hyps in
  let module P = EcPath in

  let inline1 me lv p args = 
    let p = EcEnv.NormMp.norm_xpath env p in
    let f = EcEnv.Fun.by_xpath p env in
    let fdef = 
      match f.f_def with
      | FBdef def -> def 
      | _ -> assert false in (* FIXME error message *)
    let me, anames = 
      List.map_fold _inline_freshen me f.f_sig.fs_params in
    let me, lnames = 
      List.map_fold _inline_freshen me fdef.f_locals in
    let subst =
      let for1 mx v x =
        (* Remark p is in normal form so (P.xqname p v.v_name) is *)
        P.Mx.add
          (P.xqname p v.v_name)
          (P.xqname (EcMemory.xpath me) x)
          mx
      in
      let mx = P.Mx.empty in
      let mx = List.fold_left2 for1 mx f.f_sig.fs_params anames in
      let mx = List.fold_left2 for1 mx fdef.f_locals lnames in
      let on_xp xp =
        let xp' = EcEnv.NormMp.norm_xpath env xp in
        P.Mx.find_def xp xp' mx 
      in
      { e_subst_id with es_xp = on_xp }
    in

    let prelude =
      List.map2
        (fun (v, newx) e ->
          let newpv = pv_loc (EcMemory.xpath me) newx in
          i_asgn (LvVar (newpv, v.v_type), e))
        (List.combine f.f_sig.fs_params anames)
        args in

    let body  = s_subst subst fdef.f_body in

    let resasgn =
      match fdef.f_ret with
      | None   -> None
      | Some r -> Some (i_asgn (oget lv, e_subst subst r)) in

    me, prelude @ body.s_node @ (otolist resasgn) in

  let rec inline_i me ip i = 
    match ip, i.i_node with
    | IPpat, Scall (lv, p, args) -> 
      inline1 me lv p args 
    | IPif(sp1, sp2), Sif(e,s1,s2) ->
      let me,s1 = inline_s me sp1 s1.s_node in
      let me,s2 = inline_s me sp2 s2.s_node in
      me, [i_if(e,stmt s1, stmt s2)]
    | IPwhile sp, Swhile(e,s) ->
      let me,s = inline_s me sp s.s_node in
      me, [i_while(e,stmt s)]
    | _, _ -> assert false (* FIXME error message *)
  and inline_s me sp s = 
    match sp with
    | [] -> me, s
    | (toskip,ip)::sp ->
      let r,i,s = List.split_n toskip s in
      let me,si = inline_i me ip i in
      let me,s = inline_s me sp s in
      me, List.rev_append r (si@ s) in
  let me, s = inline_s me sp s.s_node in
  me, stmt s 


let t_inline_hoare env sp g =
  let hyps,concl = get_goal g in
  let hoare      = destr_hoareS concl in
  let (me, stmt) = _inline env hyps hoare.hs_m sp hoare.hs_s in
  let concl      = f_hoareS_r { hoare with hs_m = me; hs_s = stmt; } in
  prove_goal_by [concl] (RN_hl_inline (None, sp)) g

let t_inline_equiv env side sp g =
  let hyps, concl = get_goal g in
  let equiv = destr_equivS concl in
  let concl =
    match side with
    | true  ->
      let (me, stmt) = _inline env hyps equiv.es_ml sp equiv.es_sl in
      f_equivS_r { equiv with es_ml = me; es_sl = stmt; }
    | false ->
      let (me, stmt) = _inline env hyps equiv.es_mr sp equiv.es_sr in
      f_equivS_r { equiv with es_mr = me; es_sr = stmt; }
  in
  prove_goal_by [concl] (RN_hl_inline (Some side, sp)) g

(* -------------------------------------------------------------------- *)

let t_equiv_deno env pre post g =
  let concl = get_concl g in
  let cmp, f1, f2 =
    match concl.f_node with
    | Fapp({f_node = Fop(op,_)}, [f1;f2]) when is_pr f1 && is_pr f2 &&
        (EcPath.p_equal op EcCoreLib.p_eq || 
           EcPath.p_equal op EcCoreLib.p_real_le) ->
      EcPath.p_equal op EcCoreLib.p_eq, f1, f2
    | _ -> cannot_apply "equiv_deno" "" in (* FIXME error message *)
  let (ml,fl,argsl,evl) = destr_pr f1 in
  let (mr,fr,argsr,evr) = destr_pr f2 in
  let concl_e = f_equivF pre fl fr post in
  let funl = EcEnv.Fun.by_xpath fl env in
  let funr = EcEnv.Fun.by_xpath fr env in
  (* building the substitution for the pre *)
  (* we should substitute param by args and left by ml and right by mr *)
  let sargs = 
    List.fold_left2 (fun s v a -> PVM.add env (pv_loc fr v.v_name) mright a s)
      PVM.empty funr.f_sig.fs_params argsr in
  let sargs = 
    List.fold_left2 (fun s v a -> PVM.add env (pv_loc fl v.v_name) mleft a s)
      sargs funl.f_sig.fs_params argsl in
  let smem = { f_subst_id with 
    fs_mem = Mid.add mleft ml (Mid.singleton mright mr) } in
  let concl_pr  = f_subst smem (PVM.subst env sargs pre) in
  (* building the substitution for the post *)
  let smeml = { f_subst_id with fs_mem = Mid.singleton mhr mleft } in
  let smemr = { f_subst_id with fs_mem = Mid.singleton mhr mright } in
  let evl   = f_subst smeml evl and evr = f_subst smemr evr in
  let cmp   = if cmp then f_iff else f_imp in 
  let mel = EcEnv.Fun.actmem_post mleft fl funl in
  let mer = EcEnv.Fun.actmem_post mright fr funr in
  let concl_po = gen_mems [mel;mer] (f_imp post (cmp evl evr)) in
  prove_goal_by [concl_e;concl_pr;concl_po] RN_hl_deno g  


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

let t_bdHoare_rcond b at_pos g = 
  (* TODO: generalize the rule using assume *)
  if at_pos <> 1 then
    cannot_apply "rcond" "position must be 1 in bounded Hoare judgments";
  let concl = get_concl g in
  let bhs = destr_bdHoareS concl in
  let m  = EcMemory.memory bhs.bhs_m in 
  let hd,e,s = gen_rcond b m at_pos bhs.bhs_s in
  let concl1  = f_bdHoareS_r { bhs with bhs_s = hd; bhs_po = e } in
  let concl2  = f_bdHoareS_r { bhs with bhs_s = s } in
  prove_goal_by [concl1;concl2] (RN_hl_rcond (None, b,at_pos)) g  

let t_equiv_rcond side b at_pos g =
  let concl = get_concl g in
  let es = destr_equivS concl in
  let m,mo,s = 
    if side then es.es_ml,es.es_mr, es.es_sl 
    else         es.es_mr,es.es_ml, es.es_sr in
  let hd,e,s = gen_rcond b EcFol.mhr at_pos s in 
  let mo' = EcIdent.create "&m" in
  let s1 = 
    Mid.add (EcMemory.memory mo) mo' 
      (Mid.add (EcMemory.memory m) EcFol.mhr Mid.empty) in
  let pre1  = f_subst {f_subst_id with fs_mem = s1} es.es_pr in
  let concl1 = 
    gen_mems [mo', EcMemory.memtype mo] 
      (f_hoareS (EcFol.mhr,EcMemory.memtype m) pre1 hd e) in
  let sl,sr = if side then s, es.es_sr else es.es_sl, s in
  let concl2 = f_equivS_r { es with es_sl = sl; es_sr = sr } in
  prove_goal_by [concl1;concl2] (RN_hl_rcond (Some side,b,at_pos)) g 

let t_rcond side b at_pos g =
  let concl = get_concl g in
  match side with
    | None when is_bdHoareS concl -> t_bdHoare_rcond b at_pos g
    | None -> t_hoare_rcond b at_pos g
    | Some side -> t_equiv_rcond side b at_pos g

(* -------------------------------------------------------------------- *)
let check_swap env s1 s2 = 
  let m1,m2 = s_write env s1, s_write env s2 in
  let r1,r2 = s_read env s1, s_read env s2 in
  let m2r1 = PV.disjoint env m2 r1 in
  let m1m2 = PV.disjoint env m1 m2 in
  let m1r2 = PV.disjoint env m1 r2 in
  let error () = (* FIXME : better error message *)
    cannot_apply "swap" "the two statements are not independent" in
  if not m2r1 then error ();
  if not m1m2 then error ();
  if not m1r2 then error ()

let t_equiv_swap env side p1 p2 p3 g =
  let swap s = 
    let s = s.s_node in
    let len = List.length s in
    if not (1<= p1 && p1 < p2 && p2 <= p3 && p3 <= len) then
      cannot_apply "swap" 
        (Format.sprintf "invalid position, 1 <= %i < %i <= %i <= %i"
           p1 p2 p3 len);
    let hd,tl = List.take_n (p1-1) s in
    let s12,tl = List.take_n (p2-p1) tl in
    let s23,tl = List.take_n (p3-p2+1) tl in
    check_swap env (stmt s12) (stmt s23);
    stmt (List.flatten [hd;s23;s12;tl]) in
  let concl = get_concl g in
  let es    = destr_equivS concl in
  let sl,sr = 
    if side then swap es.es_sl, es.es_sr else es.es_sl, swap es.es_sr in
  let concl = f_equivS_r {es with es_sl = sl; es_sr = sr } in
  prove_goal_by [concl] (RN_hl_swap(side,p1,p2,p3)) g
    
(* -------------------------------------------------------------------- *)

let s_first_if s = 
  match s.s_node with
  | [] -> cannot_apply "if" "the first instruction should be a if"
  | i::_ -> 
    try destr_if i with Not_found -> 
      cannot_apply "if" "the first instruction should be a if"

let t_gen_cond env side e g =
  let hyps = get_hyps g in
  let m1,m2,h,h1,h2 = match LDecl.fresh_ids hyps ["&m";"&m";"_";"_";"_"] with
    | [m1;m2;h;h1;h2] -> m1,m2,h,h1,h2
    | _ -> assert false in
  let t_introm = if side <> None then t_intros_i env [m1] else t_id None in
  let t_sub b g = 
    t_seq_subgoal (t_rcond side b 1)
      [ t_lseq [t_introm; t_skip;t_intros_i env ([m2;h]);
                t_elim_hyp env h;
                t_intros_i env [h1; h2]; t_hyp env h2];
        t_id None] g in
  t_seq_subgoal (t_he_case e) [t_sub true; t_sub false] g

let t_hoare_cond env g = 
  let concl = get_concl g in
  let hs = destr_hoareS concl in 
  let (e,_,_) = s_first_if hs.hs_s in
  t_gen_cond env None (form_of_expr (EcMemory.memory hs.hs_m) e) g

let t_bdHoare_cond env g = 
  let concl = get_concl g in
  let bhs = destr_bdHoareS concl in 
  let (e,_,_) = s_first_if bhs.bhs_s in
  t_gen_cond env None (form_of_expr (EcMemory.memory bhs.bhs_m) e) g

let rec t_equiv_cond env side g =
  let hyps,concl = get_goal g in
  let es = destr_equivS concl in
  match side with
  | Some s ->
    let e = 
      if s then 
        let (e,_,_) = s_first_if es.es_sl in
        form_of_expr (EcMemory.memory es.es_ml) e
      else
        let (e,_,_) = s_first_if es.es_sr in
        form_of_expr (EcMemory.memory es.es_mr) e in
    t_gen_cond env side e g
  | None -> 
      let el,_,_ = s_first_if es.es_sl in
      let er,_,_ = s_first_if es.es_sr in
      let el = form_of_expr (EcMemory.memory es.es_ml) el in
      let er = form_of_expr (EcMemory.memory es.es_mr) er in
      let fiff = gen_mems [es.es_ml;es.es_mr] (f_imp es.es_pr (f_iff el er)) in
      let hiff,m1,m2,h,h1,h2 = 
        match LDecl.fresh_ids hyps ["hiff";"&m1";"&m2";"h";"h";"h"] with 
        | [hiff;m1;m2;h;h1;h2] -> hiff,m1,m2,h,h1,h2 
        | _ -> assert false in
      let t_aux = 
        t_lseq [t_intros_i env [m1];
                t_skip;
                t_intros_i env [m2;h];
                t_elim_hyp env h;
                t_intros_i env [h1;h2];
                t_seq_subgoal (t_rewrite_hyp env false hiff 
                                 [AAmem m1;AAmem m2;AAnode])
                  [t_hyp env h1; t_hyp env h2]] in
      t_seq_subgoal (t_cut env fiff)
        [ t_id None;
          t_seq (t_intros_i env [hiff])
            (t_seq_subgoal (t_equiv_cond env (Some true))
               [t_seq_subgoal (t_equiv_rcond false true  1) 
                   [t_aux; t_clear (Sid.singleton hiff)];
                t_seq_subgoal (t_equiv_rcond false false 1) 
                  [t_aux; t_clear (Sid.singleton hiff)]
               ])
        ] g


(* -------------------------------------------------------------------- *)




(* -------------------------------------------------------------------- *)



let (===) = f_eq 
let (==>) = f_imp
let (&&&) = f_anda

let t_hoare_rnd env g =
  let concl = get_concl g in
  let hs = destr_hoareS concl in
  let (lv,distr),s= s_last_rnd "rnd" hs.hs_s in
  (* FIXME: exception when not rnds found *)
  let ty_distr = proj_distr_ty (e_ty distr) in
  let x_id = EcIdent.create (symbol_of_lv lv) in
  let x = f_local x_id ty_distr in
  let distr = EcFol.form_of_expr (EcMemory.memory hs.hs_m) distr in
  let post = subst_form_lv env (EcMemory.memory hs.hs_m) lv x hs.hs_po in
  let post = (f_in_supp x distr) ==> post in
  let post = f_forall_simpl [(x_id,GTty ty_distr)] post in
  let concl = f_hoareS_r {hs with hs_s=s; hs_po=post} in
  prove_goal_by [concl] RN_hl_hoare_rnd g


let wp_equiv_disj_rnd side env g =
  let concl = get_concl g in
  let es = destr_equivS concl in
  let m,s = 
    if side then es.es_ml, es.es_sl 
    else         es.es_mr, es.es_sr 
  in
  let (lv,distr),s= s_last_rnd "rnd" s in

  (* FIXME: exception when not rnds found *)
  let ty_distr = proj_distr_ty (e_ty distr) in
  let x_id = EcIdent.create (symbol_of_lv lv) in
  let x = f_local x_id ty_distr in
  let distr = EcFol.form_of_expr (EcMemory.memory m) distr in
  let post = subst_form_lv env (EcMemory.memory m) lv x es.es_po in
  let post = (f_in_supp x distr) ==> post in
  let post = f_forall_simpl [(x_id,GTty ty_distr)] post in
  let concl = 
    if side then f_equivS_r {es with es_sl=s; es_po=post} 
    else  f_equivS_r {es with es_sr=s; es_po=post} 
  in
  prove_goal_by [concl] RN_hl_hoare_rnd g
  



let wp_equiv_rnd env (f,finv) g =
  let concl = get_concl g in
  let es = destr_equivS concl in
  let (lvL,muL),(lvR,muR),sl',sr'= s_last_rnds "rnd" es.es_sl es.es_sr in
  (* FIXME: exception when not rnds found *)
  let tyL = proj_distr_ty (e_ty muL) in
  let tyR = proj_distr_ty (e_ty muR) in
  let x_id = EcIdent.create (symbol_of_lv lvL ^ "L")
  and y_id = EcIdent.create (symbol_of_lv lvR ^ "R") in
  let x = f_local x_id tyL in
  let y = f_local y_id tyR in
  let muL = EcFol.form_of_expr (EcMemory.memory es.es_ml) muL in
  let muR = EcFol.form_of_expr (EcMemory.memory es.es_mr) muR in
  (* *)
  let tf = f tyL tyR in
  let tfinv = finv tyR tyL in
  let f t = f_app tf  [t] tyR in
  let finv t = f_app tfinv [t] tyL in
  let supp_cond1 = (f_in_supp x muL) ==> 
    ((f_mu_x muL x) === (f_mu_x muR (f x))) in
  let supp_cond2 = (f_in_supp y muR) ==> (f_in_supp (finv y) muL) in
  let inv_cond1 =  (f_in_supp x muL) ==> ((finv (f x)) === x) in
  let inv_cond2 =  (f_in_supp y muR) ==> ((f (finv y)) === y) in
  let post = subst_form_lv env (EcMemory.memory es.es_ml) lvL x es.es_po in
  let post = subst_form_lv env (EcMemory.memory es.es_mr) lvR (f x) post in
  let post = (f_in_supp x muL) ==> post in
  let post = supp_cond1 &&& supp_cond2 &&& inv_cond1 &&& inv_cond2 &&& post in
  let post = f_forall_simpl [(x_id,GTty tyL);(y_id,GTty tyR)] post in
  let concl = f_equivS_r {es with es_sl=sl'; es_sr=sr'; es_po=post} in
  prove_goal_by [concl] (RN_hl_equiv_rnd ((Some tf, Some tfinv))) g

let t_equiv_rnd side env bij_info = 
  match side with
    | Some side -> wp_equiv_disj_rnd side env 
    | None  ->
      let f,finv =  match bij_info with 
        | Some f, Some finv ->  f, finv
        | Some bij, None | None, Some bij -> bij, bij
        | None, None -> 
          let z_id = EcIdent.create "z" in
          let z = f_local z_id in
          let bij = fun tyL tyR -> f_lambda [z_id,GTty tyR] (z tyL) in 
          (* TODO Cezar : Can it be not well typed: normally tyL and tyR should
             be equal.
             I propose to replace tyL by tyR
            *)
          bij, bij
      in wp_equiv_rnd env (f, finv) 

let t_bd_hoare_rnd env (opt_bd,opt_event) g =
  let concl = get_concl g in
  let bhs = destr_bdHoareS concl in
  let (lv,distr),s = s_last_rnd "bd_hoare_rnd" bhs.bhs_s in
  let ty_distr = proj_distr_ty (e_ty distr) in
  let distr = EcFol.form_of_expr (EcMemory.memory bhs.bhs_m) distr in
  let event = match opt_event ty_distr with 
    | Some event -> event 
    | None -> cannot_apply "rnd" "Optional events still not supported"
  in
  let new_cmp_op,new_hoare_bd, bounded_distr =
    match bhs.bhs_cmp, opt_bd with
      | FHle, Some bd' when not (EcFol.f_equal bhs.bhs_bd bd') ->
        cannot_apply "bd_hoare_rnd"
          "Rule for upper-bounded hoare triples requires a total bound"
      | FHle, _ ->
          FHeq, EcFol.f_r1, f_real_le (f_mu distr event) bhs.bhs_bd
      | FHge, Some bd' when not (EcFol.f_equal bhs.bhs_bd bd') -> 
          bhs.bhs_cmp, EcFol.f_real_div bhs.bhs_bd bd', f_real_le bd' (f_mu distr event)
      | FHge, _ -> FHeq, EcFol.f_r1, f_real_le bhs.bhs_bd (f_mu distr event)
      | FHeq, Some bd' when not (EcFol.f_equal bhs.bhs_bd bd') -> 
          bhs.bhs_cmp, EcFol.f_real_div bhs.bhs_bd bd', f_eq (f_mu distr event) bd'
      | FHeq, _ -> FHeq, EcFol.f_r1, f_eq (f_mu distr event) bhs.bhs_bd
  in
  let v_id = EcIdent.create "v" in
  let v = f_local v_id ty_distr in
  let post_v = subst_form_lv env (EcMemory.memory bhs.bhs_m) lv v bhs.bhs_po in
  let event_v = f_app event [v] tbool in
  let post_equiv_event = f_forall_simpl [(v_id,GTty ty_distr)] (f_iff post_v (event_v)) in
  let post = bounded_distr &&& post_equiv_event in
  let concl = f_bdHoareS_r {bhs with bhs_s=s; bhs_po=post; bhs_cmp=new_cmp_op; 
    bhs_bd=new_hoare_bd} in
  prove_goal_by [concl] (RN_bhl_rnd (opt_bd,event) ) g



 
