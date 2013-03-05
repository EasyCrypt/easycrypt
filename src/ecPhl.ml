
open EcUtils

open EcFol
open EcBaseLogic
open EcLogic
open EcParsetree

type destr_error =
  | Destr_hl 

exception DestrError of destr_error

let destr_error e = raise (DestrError e)

let destr_hl f = 
  match f.f_node with
    | Fhoare (mem,pre,s,post) -> mem, pre, s, post
    | _ -> destr_error Destr_hl

let split_stmt n s = List.take_n n s





(* WP *)

exception No_wp

let wp_assgn lv e post = 
  match lv with
  | EcModules.LvVar (v,_t) ->  (* of (EcTypes.prog_var * EcTypes.ty) *)
    EcFol.Subst.subst_form (EcFol.Subst.single_subst (Lvar.mk_pvar v EcFol.mstd) 
                        (form_of_exp EcFol.mstd e)) post
  | _ -> raise No_wp
  (* | LvTuple of (EcTypes.prog_var * EcTypes.ty) list *)
  (* | LvMap   of (EcPath.path * EcTypes.ty list) *  *)
  (*              EcTypes.prog_var * EcTypes.tyexpr * EcTypes.ty *)

let rec wp_stmt (stmt: EcModules.instr list) post = 
  match stmt with
    | [] -> stmt, post
    | i :: stmt' -> 
      try 
        let post = wp_instr i post in
        wp_stmt stmt' post
      with No_wp -> stmt, post
and wp_instr i post =
  match i.EcModules.i_node with
    | EcModules.Sasgn (lv,e) ->
      wp_assgn lv e post
    | EcModules.Sif (e,s1,s2) -> 
      let s1,post1 = wp_stmt s1.EcModules.s_node post in
      let s2,post2 = wp_stmt s2.EcModules.s_node post in
      if s1=[] && s2=[] then
        let b = form_of_exp EcFol.mstd e in
        f_and (f_imp b post1) (f_imp (f_not b) post2)
      else raise No_wp
    | _ -> raise No_wp

let wp stmt post = 
  let stmt,post = wp_stmt (List.rev stmt) post in
  List.rev stmt, post

(* ENDOF WP *)


exception NotSkipStmt

let process_skip (juc,n as g) =
  let hyps,concl = get_goal g in
  let mem,pre,body,post = destr_hl concl in
  let s = body.EcModules.f_body in
  match s.EcModules.s_node with
    | _ :: _ -> 
      raise NotSkipStmt
    | [] -> 
      let conc = f_imp pre post in
      let pvars = body.EcModules.f_locals in
      let f (subst,bds) (sym,ty) = 
        let local = EcIdent.create sym in
        let pvar = {EcTypes.pv_name=EcPath.mident local; pv_kind=EcTypes.PVglob} in
        let subst = EcFol.Subst.add_subst (Lvar.mk_pvar pvar EcFol.mstd) (f_local local ty) subst in
        let bds = (local,GTty ty) :: bds in
        subst,bds
      in
      let subst,bds = List.fold_left f (EcFol.Subst.empty_subst,[]) pvars in
      (* let free_pvars = LVset.pvars (EcFol.Subst.fpvar_form conc) in *)
      let conc = EcFol.Subst.subst_form subst conc in
      let conc = f_forall bds conc in

      let juc,n1 = new_goal juc (hyps,conc) in
      let rule = {pr_name = RN_skip; pr_hyps=[n1]} in
      upd_rule (juc,n) rule
      


let process_wp i _loc _env (juc,n as g) =
  let hyps,concl = get_goal g in
  let mem,pre,body,post = destr_hl concl in
  let s = body.EcModules.f_body.EcModules.s_node in
  let s_fix,s_wp = split_stmt i s  in
  let s_wp,post = wp s_wp post in
  let s = EcModules.stmt (s_fix @ s_wp) in
  let a = f_hoare mem pre {body with EcModules.f_body = s} post  in
  let juc,n' = new_goal juc (hyps,a) in
  let rule = { pr_name = RN_wp i; pr_hyps = [n']} in
  upd_rule (juc,n) rule


let process_app (i,phi) _loc _env (juc,n as g) =
  let hyps,concl = get_goal g in
  let mem,pre,body,post = destr_hl concl in
  let s = body.EcModules.f_body.EcModules.s_node in
  let s1,s2 = split_stmt i s  in
  let a = f_hoare mem pre {body with EcModules.f_body = EcModules.stmt s1} phi  in
  let b = f_hoare mem phi {body with EcModules.f_body = EcModules.stmt s2} post in
  let juc,n1 = new_goal juc (hyps,a) in
  let juc,n2 = new_goal juc (hyps,b) in
  let rule = { pr_name = RN_app (i,phi); pr_hyps = [n1;n2]} in
  upd_rule (juc,n) rule
      

(* let process_tac _ _ (juc,n) = *)
(*   (juc,[n]) *)

let add_locals_env env locals =
  let f (s,ty) = (s, `Variable (EcTypes.PVloc, ty)) in
  let locals = List.map f locals in
  EcEnv.bindall locals env

let process_phl process_formula tac loc env (_juc,_n as g) = 
  let _hyps,concl = get_goal g in
  let mem,_pre,body,_post = destr_hl concl in
  match tac with 
    | Papp (i,pf) -> 
      let env = add_locals_env env body.EcModules.f_locals in
      (* first, add locals to env *)
      (* let env = ... in *)
      let f = process_formula env g pf in
      process_app (i,f) loc env g
      (* process_tac loc env g *)
    | Pwp i -> 
      process_wp i loc env g
    | Pskip -> 
      process_skip g




