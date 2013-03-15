
open EcUtils
open EcTypes
open EcFol
open EcBaseLogic
open EcLogic
open EcModules

exception CannotApply of string * string

let cannot_apply s1 s2 = raise (CannotApply(s1,s2))

type destr_error =
  | Destr_hl 

exception DestrError of destr_error

let destr_error e = raise (DestrError e)

let destr_hl f = 
  match f.f_node with
    | FhoareS (mem,pre,b,post) -> mem, pre, b, post
    | _ -> destr_error Destr_hl

let split_stmt n s = List.take_n n s


(* -------------------------------------------------------------------- *)
(* -------------------------  Substitution  --------------------------- *)
(* -------------------------------------------------------------------- *)

module PVM = struct
    
  module M = EcMaps.Map.Make(struct
    type t = prog_var * EcMemory.memory
    let compare (p1,m1) (p2,m2) = 
      let r = EcIdent.id_compare m1 m2 in
      if r = 0 then pv_compare p1 p2 
      else r
  end)

  type subst = form M.t

  let empty = M.empty 

  let pvm env pv m = EcEnv.norm_pvar env pv, m

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
      | FhoareF _ | FhoareS _ | FequivF _ | FequivS _ | Fpr _ -> assert false
      | _ -> EcFol.f_map (fun ty -> ty) aux f)

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

exception NotSkipStmt


let quantify_pvars _pvars _phi = assert false 
(*
  let f (pv,m,ty) (bds,phi) =
    if EcTypes.is_loc pv then
      let local = EcIdent.create (EcPath.name_mpath pv.EcTypes.pv_name) in
      let phi = EcFol.Subst.subst_form 
        (Subst.single_subst (Lvar.mk_pvar pv m) (f_local local ty)) phi in 
      let bds = (local,GTty ty) :: bds in
      bds,phi
    else (bds,phi)
  in
  let bds,phi = PVset.fold f pvars ([],phi) in
  f_forall bds phi
*)

let quantify_out_local_pvars _phi = assert false 
(*
  let free_pvars = EcFol.free_pvar phi in
  quantify_pvars free_pvars phi
*)

let skip_tac (juc,n as g) =
  let hyps,concl = get_goal g in
  let _mem,pre,s,post = destr_hl concl in
  match s.EcModules.s_node with
    | _ :: _ -> 
      raise NotSkipStmt
    | [] -> 
      let conc = f_imp pre post in
      let conc = quantify_out_local_pvars conc in
      let juc,n1 = new_goal juc (hyps,conc) in
      let rule = {pr_name = RN_skip; pr_hyps=[n1]} in
      upd_rule (juc,n) rule



let wp_tac _i _loc _env (_juc,_n as _g) =
  assert false
(*
  let hyps,concl = get_goal g in
  let mem,pre,s,post = destr_hl concl in
  let s_fix,s_wp = split_stmt i s.EcModules.s_node  in
  let s_wp,post = wp s_wp post in
  let s = EcModules.stmt (s_fix @ s_wp) in
  let a = f_hoareS mem pre s post  in
  let juc,n' = new_goal juc (hyps,a) in
  let rule = { pr_name = RN_wp i; pr_hyps = [n']} in
  upd_rule (juc,n) rule
*)

let app_tac (i,phi) _loc _env (juc,n as g) =
  let hyps,concl = get_goal g in
  let mem,pre,s,post = destr_hl concl in
  let s1,s2 = split_stmt i s.EcModules.s_node  in
  let a = f_hoareS mem pre (EcModules.stmt s1) phi  in
  let b = f_hoareS mem phi (EcModules.stmt s2) post in
  let juc,n1 = new_goal juc (hyps,a) in
  let juc,n2 = new_goal juc (hyps,b) in
  let rule = { pr_name = RN_app (i,phi); pr_hyps = [n1;n2]} in
  upd_rule (juc,n) rule




let upd_body body s = 
  {body with EcModules.f_body = s}

(* to EcModule *)

module Pvar' = struct
  type t = EcTypes.prog_var * EcTypes.ty

  let mk_pvar pv mem ty = (pv,mem,ty)

  let compare lv1 lv2 = compare lv1 lv2
end

module PVset' = Set.Make(Pvar')

(* let modified_pvars stmt -> (EcTypes.prog_var * ty) list *)

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

let while_tac _inv _vrnt _bnd (_juc,_n as _g) = assert false 
(*
  let hyps,concl = get_goal g in
  let mem,pre,s,post = destr_hl concl in
  let rev_s = List.rev s.EcModules.s_node in
  match rev_s with
    | [] -> cannot_apply "while_tac" ""
    | i :: rev_s' ->
      match i.EcModules.i_node with 
        | EcModules.Swhile (e,c) ->
          (* initialization *)
          (* {P} s' {Inv /\ v <= bdn /\ A mod(s) (Inv /\ ~e => post) } *)
          let mods = modified_pvars c in
          let f (pv,ty) pvs  = PVset.add (pv,mstd,ty) pvs in
          let mods = PVset'.fold f mods PVset.empty in
          let e = form_of_exp mstd e in 
          let p = quantify_pvars mods (f_imp (f_and inv (f_not e)) post) in
          let post1 = f_and inv (f_and (f_int_leq vrnt bnd) p) in
          let j1 = f_hoare mem pre (EcModules.stmt (List.rev rev_s')) post1 in
          let juc,n1 = new_goal juc (hyps,j1) in

          (* termination goal *)
          let vrnt_local = EcIdent.create "k" in
          let bnd_local = EcIdent.create "b" in
          let vrnt_eq = f_eq vrnt (f_local vrnt_local EcTypes.tint) in
          let vrnt_lt = f_int_lt vrnt (f_local vrnt_local EcTypes.tint) in
          let bnd_eq = f_eq bnd (f_local bnd_local EcTypes.tint) in
          let pre2 = f_and (f_and inv e) (f_and vrnt_eq bnd_eq) in
          let post2 = f_and vrnt_lt bnd_eq in
          let j2 = f_hoare mem pre2 c post2 in
          let juc,n2 = new_goal juc (hyps,j2) in

          (* invariant preservation *)
          (* TODO: if prob=1 then the next goal can be merged with previous one,
             otw one cannot *)
          let pre3, post3 = f_and inv e, inv in
          let j3 = f_hoare mem pre3 c post3 in
          let juc,n3 = new_goal juc (hyps,j3) in
          
          let rule = { pr_name = RN_while(inv,vrnt,bnd); pr_hyps=[n1;n2;n3]} in
          upd_rule (juc,n) rule
        | _ -> cannot_apply "while_tac" ""
*)


let add_locals_env env locals =
  let f (s,ty) = (s, `Variable (EcTypes.PVloc, ty)) in
  let locals = List.map f locals in
  EcEnv.bindall locals env


let process_phl _process_form _tac _loc (_juc,_n as _g) = assert false
(*
  let _hyps,concl = get_goal g in
  let env,_pre,_s,_post = destr_hl concl in
  (* let env = add_locals_env env body.EcModules.f_locals in (\* FIXME: after I have memenv *\) *)
  match tac with 
    | Papp (i,pf) -> 
      let f = process_form g pf EcTypes.tbool in
      app_tac (i,f) loc env g
    | Pwp i -> 
      wp_tac i loc env g
    | Pskip -> 
      skip_tac g
    | Pwhile (inv,varnt,bnd) ->
      let inv = process_form g inv EcTypes.tbool in
      let varnt = process_form g varnt EcTypes.tint in
      let bnd = process_form g bnd EcTypes.tint in
      while_tac inv varnt bnd g



*)
