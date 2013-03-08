
open EcUtils

open EcFol
open EcBaseLogic
open EcLogic
open EcParsetree

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





(* WP *)

exception No_wp

let wp_assgn lv e post = 
  match lv with
  | EcModules.LvVar (v,_t) ->  (* of (EcTypes.prog_var * EcTypes.ty) *)
    EcFol.Subst.subst_form (EcFol.Subst.single_subst (Lvar.mk_pvar v EcFol.mstd)
                              (form_of_exp EcFol.mstd e)) post
  | EcModules.LvTuple vs ->
    EcFol.let_form (List.map (fun (v,t) ->(Lvar.mk_pvar v mstd),t ) vs) (form_of_exp EcFol.mstd e) post
  | _ -> raise No_wp


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


let quantify_pvars pvars phi =
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

let quantify_out_local_pvars phi =
  let free_pvars = EcFol.free_pvar phi in
  quantify_pvars free_pvars phi


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



let wp_tac i _loc _env (juc,n as g) =
  let hyps,concl = get_goal g in
  let mem,pre,s,post = destr_hl concl in
  let s_fix,s_wp = split_stmt i s.EcModules.s_node  in
  let s_wp,post = wp s_wp post in
  let s = EcModules.stmt (s_fix @ s_wp) in
  let a = f_hoare mem pre s post  in
  let juc,n' = new_goal juc (hyps,a) in
  let rule = { pr_name = RN_wp i; pr_hyps = [n']} in
  upd_rule (juc,n) rule


let app_tac (i,phi) _loc _env (juc,n as g) =
  let hyps,concl = get_goal g in
  let mem,pre,s,post = destr_hl concl in
  let s1,s2 = split_stmt i s.EcModules.s_node  in
  let a = f_hoare mem pre (EcModules.stmt s1) phi  in
  let b = f_hoare mem phi (EcModules.stmt s2) post in
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

let while_tac inv vrnt bnd (juc,n as g) =
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



let add_locals_env env locals =
  let f (s,ty) = (s, `Variable (EcTypes.PVloc, ty)) in
  let locals = List.map f locals in
  EcEnv.bindall locals env


let process_phl process_form tac loc (_juc,_n as g) = 
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



