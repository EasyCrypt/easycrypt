(** WP computation. *)

open Ast
open EcUtil

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

exception Wp_random
exception Wp_call
exception Wp_while
exception Wp_if
exception Wp_assert
exception Wp_no_calls
exception Wp_no_asgn
exception Wp_no_random
exception Wp_wrong_equiv of ((Ast.fct * Ast.fct) * (Ast.fct * Ast.fct))
exception Wp_nothing_done


(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* Approximative goals *)

let reduce_app app1 app2 = 
  let real_div t1 t2 = 
    if Fol.eq_term t2 Global.rone then t1
    else if Fol.eq_term t1 t2 then Global.rone
    else Ast.Eapp(Global.op_real_div,[t1;t2])
  in
  let real_sub t1 t2 =
    if Fol.eq_term t2 Global.rzero then t1
    else if Fol.eq_term t1 t2 then Global.rzero
    else Ast.Eapp(Global.op_real_sub,[t1;t2])
  in
  let some (t1,t2) = 
    if Fol.eq_term t1 Global.rone && Fol.eq_term t2 Global.rzero 
    then None else Some (t1,t2)
  in
  match app1, app2 with
  | None, None -> None
  | Some (alpha1,delta1), Some (alpha2,delta2) ->
    some (real_div alpha1 alpha2,real_sub delta1 delta2)
  | Some _, None -> app1
  | None, Some (alpha,delta) -> 
    some (real_div Global.rone alpha,real_sub Global.rzero delta)



(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** {2 About Assignments} *)

let wp_asgn_term side lasgn t p =
  let lv_of_v v = Fol.lvar_of_var v side in
  match lasgn with
  | Ltuple vars -> Fol.let_pred (List.map lv_of_v vars) t p
  | Lupd(v, e) ->
      let lv = lv_of_v v in
      let e = Fol.term_of_exp side e in
      Fol.let_pred [lv] 
        (Eapp(Global.op_upd_map v.v_type, [Ebase lv; e; t])) p

let wp_return side v e p =
  let lv = Fol.lvar_of_var v side in
  match e with
    | Some e -> Fol.let_pred ~fresh:true [lv] (Fol.term_of_exp side e) p
    | None -> Fol.let_pred_opt lv None p

let wp_asgn side lasgn e p =
  if not (EcTerm.is_var_exp e) then raise Wp_random;
  wp_asgn_term side lasgn (Fol.term_of_exp side e) p

let wp_asgn_fct s1 s2 p =
  let rec wp ok s1 s2 p =
    match s1, s2 with
      | Ast.Sasgn (var, exp) :: r1, _ when EcTerm.is_var_exp exp ->
        let p = wp_asgn Fol.FVleft var exp p in
        wp true r1 s2 p
      | _, Ast.Sasgn (var, exp) :: r2 when EcTerm.is_var_exp exp ->
        let p = wp_asgn Fol.FVright var exp p in
        wp true s1 r2 p
      | _, _ ->
        if ok then (s1, s2, p)
        else raise Wp_no_asgn
  in wp false s1 s2 p

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** {2 About Sequences} *)

let rec wp_instr side i p =
  match i with
    | Sif (c, s_then, s_else) ->
      let p_else = wp_stmt side s_else p in
      let p_then = wp_stmt side s_then p in
      let c = Fol.term_of_exp side c in
      let split_info =
        match side with Fol.FVleft -> false | Fol.FVright -> true
      in
      Fol.pif ~split_info c p_then p_else
    | Scall _ -> raise Wp_call
    | Sasgn (vars, exp) -> wp_asgn side vars exp p
    | Swhile _ -> raise Wp_while
    | Sassert _ -> raise Wp_assert

and wp_stmt side stmt p =
  match stmt with
    | [] -> p
    | inst :: tl -> let p = wp_stmt side tl p in wp_instr side inst p


let rec wp_instr_app side i p =
  match i with
    | Sasgn (vars, exp) -> wp_asgn side vars exp p
    | Sif _ -> raise Wp_if
    | Scall _ -> raise Wp_call
    | Swhile _ -> raise Wp_while
    | Sassert _ -> raise Wp_assert


let rec wp_rev wpi side sr p =
  match sr with
    | [] -> [], p
    | i::sr' ->
      try wp_rev wpi side sr' (wpi side i p)
      with
        | Wp_call | Wp_random
        | Wp_while | Wp_if | Wp_assert -> sr, p



let rec wp_simpl_fct s1 s2 p =
  let s1', p = wp_rev wp_instr Fol.FVleft s1 p in
  let s2', p = wp_rev wp_instr Fol.FVright s2 p in
  let s1', s2', p = match s1', s2' with
    | Sassert b1::s1'', Sassert b2::s2'' ->
      let b1 = Fol.term_of_exp Fol.FVleft b1 in
      let b2 = Fol.term_of_exp Fol.FVright b2 in
      let post = 
        Fol.pand (Fol.peq b1 b2) (Fol.pimplies (Fol.pred_of_term b1) p) in
      begin
        try
          wp_simpl_fct s1'' s2'' post
        with Wp_nothing_done -> s1'',s2'',post
      end
    | _ -> s1',s2',p
  in
  if EcTerm.eq_stmt s1 s1' && EcTerm.eq_stmt s2 s2' then
    raise Wp_nothing_done;
  s1', s2', p



let rec wp_simpl_fct_app s1 s2 p =
  let s1', p = wp_rev wp_instr_app Fol.FVleft s1 p in
  let s2', p = wp_rev wp_instr_app Fol.FVright s2 p in
  let s1', s2', p = match s1', s2' with
    | Sif (b1,s_then1,s_else1)::s1'', Sif (b2,s_then2,s_else2)::s2'' ->
      let s_then1,s_then2, p_then = 
        try wp_simpl_fct_app (List.rev s_then1) (List.rev s_then2) p 
        with Wp_nothing_done -> s_then1, s_then2, p
      in
      let s_else1, s_else2, p_else = 
        try wp_simpl_fct_app (List.rev s_else1) (List.rev s_else2) p
        with Wp_nothing_done -> s_else1, s_else2, p
      in
      if (s_then1=[] && s_then2=[] && s_else1=[] && s_else2=[]) then
        let b1 = Fol.term_of_exp Fol.FVleft b1 in
        let b2 = Fol.term_of_exp Fol.FVright b2 in
        let post = Fol.pand (Fol.peq b1 b2) (Fol.pif b1 p_then p_else) in
        try wp_simpl_fct_app s1'' s2'' post
        with Wp_nothing_done -> s1'', s2'', post
      else
        s1',s2',p
    | Sassert b1::s1'', Sassert b2::s2'' ->
      let b1 = Fol.term_of_exp Fol.FVleft b1 in
      let b2 = Fol.term_of_exp Fol.FVright b2 in
      let post = 
        Fol.pand (Fol.peq b1 b2) (Fol.pimplies (Fol.pred_of_term b1) p) in
      wp_simpl_fct_app s1'' s2'' post
    (* TODO: consider the sync case as special case *)
    | _ -> s1',s2',p
  in
  if EcTerm.eq_stmt s1 s1' && EcTerm.eq_stmt s2 s2' then
    raise Wp_nothing_done;
  s1', s2', p


  



(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** {2 About Calls} *)

let wp_call1 x1 f1 args1 pre post p =
  let let_exp_pred side v e p =
    let lv = Fol.lvar_of_var v side in
    let t = Fol.term_of_exp side e in
    Fol.let_pred ~fresh:true [lv] t p
  in
  let pre = List.fold_right2 (let_exp_pred Fol.FVleft)  f1.f_param args1 pre in
  let p = wp_asgn Fol.FVleft x1 (Ebase f1.f_res) p in
  let p = Fol.pimplies post p in
  let qq side v (lv, p) =
    let (v',p) = Fol.forall_pred_with_var ~fresh:true (Fol.lvar_of_var v side) p
    in (v' :: lv, p)
  in
  let (lv,p) = List.fold_right (qq Fol.FVleft)  (f1.f_res::f1.f_modify) ([],p)
  in (lv, Fol.pand pre p)


let wp_call x1 f1 args1 x2 f2 args2 pre post p app f_app =
  let let_exp_pred side v e p =
    let lv = Fol.lvar_of_var v side in
    let t = Fol.term_of_exp side e in
    Fol.let_pred ~fresh:true [lv] t p
  in
  let pre = List.fold_right2 (let_exp_pred Fol.FVleft)  f1.f_param args1 pre in
  let pre = List.fold_right2 (let_exp_pred Fol.FVright) f2.f_param args2 pre in
  let p = wp_asgn Fol.FVright x2 (Ebase f2.f_res) p in
  let p = wp_asgn Fol.FVleft  x1 (Ebase f1.f_res) p in
  let p = Fol.pimplies post p in
  (* we quantify over all modified global variables *)
  let qq side v (lv, p) =
    let (v',p) = Fol.forall_pred_with_var ~fresh:true (Fol.lvar_of_var v side) p
    in (v' :: lv, p)
  in
  let (lv1,p) = List.fold_right (qq Fol.FVleft)  (f1.f_res::f1.f_modify) ([],p) 
  in
  let (lv2,p) = List.fold_right (qq Fol.FVright) (f2.f_res::f2.f_modify) ([],p) 
  in
  let p = Fol.simplify_equality p in 
  let app = match app with
    | Some (f_alpha,f_delta) -> 
      let let_exp_exp side v e p =
        let lv = Fol.lvar_of_var v side in
        let t = Fol.term_of_exp side e in
        Fol.change_vars_in_var_exp (fun x -> if Fol.eq_lvar x lv then Some t else None) p
      in
      let f_alpha = List.fold_right2 (let_exp_exp Fol.FVleft) f1.f_param args1 f_alpha in
      let f_alpha = List.fold_right2 (let_exp_exp Fol.FVright) f2.f_param args2 f_alpha in
      let f_delta = List.fold_right2 (let_exp_exp Fol.FVleft) f1.f_param args1 f_delta in
      let f_delta = List.fold_right2 (let_exp_exp Fol.FVright) f2.f_param args2 f_delta in
      Some (f_alpha,f_delta)
    | _ -> None
  in 
  ((lv1, lv2), Fol.pand pre p, reduce_app app f_app)


let wp_call_equiv_fct equiv s1 s2 p app =
  let check_equiv equiv f1 f2 =
    match equiv with
      | (f1', f2', pre, post, f_app) ->
        if EcTerm.eq_fct f1 f1' && EcTerm.eq_fct f2 f2' then (pre, post, f_app)
        else raise (Wp_wrong_equiv ((f1', f2'), (f1, f2)))
  in
  match s1, s2 with
    | Ast.Scall (x1, f1, args1)::r1, Ast.Scall (x2, f2, args2)::r2 ->
      let f_pre, f_post, f_app = check_equiv equiv f1 f2 in
      let (lv,p,app) = wp_call x1 f1 args1 x2 f2 args2 f_pre f_post p app f_app in
      lv, r1, r2, p,app
    | _, _ -> cannot_apply "wp_call" "no calls"

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** {2 About Random} *)

let rec wp_eq_random r1 r2 =
  match r1, r2 with
    | Rinter(e11,e12), Rinter(e21,e22) ->
      Fol.pand (Fol.peq_exp e11 e21) (Fol.peq_exp e12 e22)
    | Rbool, Rbool -> Fol.Ptrue
    | Rbitstr e1, Rbitstr e2 -> Fol.peq_exp e1 e2
    | Rexcepted(r1',e1), Rexcepted(r2',e2) ->
      Fol.pand (wp_eq_random r1' r2') (Fol.peq_exp e1 e2)
    | Rapp (op1,args1) , Rapp (op2,args2) when EcTerm.eq_op op1 op2 ->
      let f b e1 e2 = Fol.pand b (Fol.peq_exp e1 e2) in
      (List.fold_left2 f Fol.Ptrue args1 args2)
    | _, _ -> Fol.Pfalse


let cond_bij x y r1 r2 info =
  let x = Ebase x in
  let y = Ebase y in
  match info, r1, r2 with
    | AstLogic.RIidempotant _, Rapp (op,_), _
    | AstLogic.RIidempotant _, _, Rapp (op,_) 
    | AstLogic.RIbij _, Rapp (op,_), _
    | AstLogic.RIbij _, _, Rapp (op,_) -> 
        user_error "cannot compute wp: %a may not be uniform" PpAst.pp_op op;
    | AstLogic.RIid, _, _ -> wp_eq_random r1 r2, Fol.Ptrue, Fol.Ptrue, x
    | AstLogic.RIidempotant (lv,f), _, _ ->
      let t = Fol.lv_type lv in
        Unification.raise_unify_type t (Fol.lv_type lv) dummy_pos "wp random rule";
        if not (Fol.FVset.mem lv (Fol.free_term_vars f)) then
          user_error "wp random rule: expression %a is not a function of %a"
            (Fol.pp_term 0) f Fol.pp_lvar lv;
      let fx  = Fol.subst_var_in_term lv x  f in
      let ffx = Fol.subst_var_in_term lv fx f in
      let fy  = Fol.subst_var_in_term lv y  f in
      let ffy = Fol.subst_var_in_term lv fy f in
      let bound1 = FunLogic.bound_random Fol.FVright fx r2 in
      let bound2 = FunLogic.bound_random Fol.FVleft  fy r1 in
        Fol.Ptrue, Fol.pand bound1 (Fol.peq ffx x), Fol.pand bound2 (Fol.peq ffy y), fx
    | AstLogic.RIbij ((lv1,f), (lv2,finv)), _, _ ->
      let t1, t2 = Fol.lv_type lv1, Fol.lv_type lv2 in
      Unification.raise_unify_type t1 (Fol.lv_type lv1) dummy_pos "wp random rule";
      Unification.raise_unify_type t2 (Fol.lv_type lv2) dummy_pos "wp random rule";
      if not (Fol.FVset.mem lv1 (Fol.free_term_vars f)) then
        user_error "wp random rule: expression %a is not a function of %a"
          (Fol.pp_term 0) f Fol.pp_lvar lv1;
      if not (Fol.FVset.mem lv2 (Fol.free_term_vars finv)) then
        user_error "wp random rule: expression %a is not a function of %a"
          (Fol.pp_term 0) finv Fol.pp_lvar lv2;
      let fx     = Fol.subst_var_in_term lv1 x     f in
      let finvfx = Fol.subst_var_in_term lv2 fx    finv in
      let finvy  = Fol.subst_var_in_term lv2 y     finv in
      let ffinvy = Fol.subst_var_in_term lv1 finvy f in
      let bound1 = FunLogic.bound_random Fol.FVright fx    r2 in
      let bound2 = FunLogic.bound_random Fol.FVleft  finvy r1 in
        Fol.Ptrue, Fol.pand bound1 (Fol.peq finvfx x), Fol.pand bound2 (Fol.peq ffinvy y), fx
   
let wp_rnd_fct info s1 s2 p app =
  match s1, s2 with
    | Ast.Sasgn (l1, Ast.Ernd r1)::c1, Ast.Sasgn (l2, Ast.Ernd r2)::c2 ->
      (try Unification.raise_unify_type 
	    (EcTerm.type_of_random r1) 
	    (EcTerm.type_of_random r2) dummy_pos "wp random rule"
      with _ -> cannot_apply "wp random rule" "type mismatch");
      let x = Fol.logic_lvar "x" (EcTerm.type_of_random r1) in
      let y = Fol.logic_lvar "y" (EcTerm.type_of_random r2) in
      let bound1 = FunLogic.bound_random Fol.FVright (Ebase x) r1 in
      let bound2 = FunLogic.bound_random Fol.FVleft  (Ebase y) r2 in
      let (cond, cond1, cond2, fx) = cond_bij x y r1 r2 info in
      let post = wp_asgn_term Fol.FVleft  l1 (Ast.Ebase x) p in
      let post = wp_asgn_term Fol.FVright l2 fx post in
      let fresh = false in
      let post =
        Fol.pand cond
        (Fol.pand 
          (Fol.forall_pred ~fresh x 
	    (Fol.pimplies bound1 (Fol.pand cond1 (Fol.pimplies cond1 post))))
          (Fol.forall_pred ~fresh y (Fol.pimplies bound2 cond2)))
      in x, c1, c2, post, app
    | _, _ -> raise Wp_no_random

let rec wp_rnd_disj_fct side s1 s2 p app =
  match side, s1, s2 with
    | ApiTypes.Left, Ast.Sasgn(l1, Ast.Ernd e1)::r1, _ ->
      let quantif =
        match l1 with
          | Ltuple [x] -> Fol.logic_lvar x.v_name x.v_type
          | _ -> bug "unexpected match"
      in
      let q = Ebase quantif in
      let bound = FunLogic.bound_random Fol.FVleft q e1 in
      let post = wp_asgn_term Fol.FVleft l1 q p in
      let fresh = false in
      let post = Fol.forall_pred ~fresh quantif (Fol.pimplies bound post) in
      quantif, r1, s2, post, app
    | ApiTypes.Left,_,_ -> raise Wp_no_random
    | ApiTypes.Right, _, Ast.Sasgn(l2, Ast.Ernd e2)::r2 ->
      let quantif =
        match l2 with
          | Ltuple [x] -> Fol.logic_lvar x.v_name x.v_type
          | _ -> bug "unexpected match"
      in
      let q = Ebase quantif in
      let bound = FunLogic.bound_random Fol.FVright q e2 in
      let post = wp_asgn_term Fol.FVright l2 q p in
      let fresh = false in
      let post = Fol.forall_pred ~fresh quantif (Fol.pimplies bound post) in
      quantif, s1, r2, post, app
    | ApiTypes.Right,_,_ -> raise Wp_no_random
    | ApiTypes.Both,_, _ -> assert false

(* wp_rnd_disj_fct wrapper *)
let wp_rnd_disj_fct side s1 s2 p app =
	match side, s1, s2 with
	 	| ApiTypes.Left, Ast.Sasgn (Ltuple vars, Ast.Ernd r)::c, _ 
      when 1 < List.length vars ->
	 	  let _, x = Global.fresh_var (Global.empty_venv()) "r" (EcTerm.type_of_random r) in
	 	  let c = Ast.Sasgn (Ltuple [x], Ast.Ernd r):: c in
	 	  let p = wp_asgn Fol.FVleft (Ltuple vars) (Ebase x) p in
	 	  wp_rnd_disj_fct side c s2 p app
	 	| ApiTypes.Right, _, Ast.Sasgn (Ltuple vars, Ast.Ernd r)::c 
      when 1 < List.length vars ->
	 	  let _, x = Global.fresh_var (Global.empty_venv()) "r" (EcTerm.type_of_random r) in
	 	  let c = Ast.Sasgn (Ltuple [x], Ast.Ernd r):: c in
	 	  let p = wp_asgn Fol.FVright (Ltuple vars) (Ebase x) p in
	 	  wp_rnd_disj_fct side s1 c p app
    | ApiTypes.Left, Ast.Sasgn (Lupd(v,e), Ast.Ernd r)::c, _ ->
	 	  let _, x = Global.fresh_var (Global.empty_venv()) "r" (EcTerm.type_of_random r) in
	 	  let c = Ast.Sasgn (Ltuple [x], Ast.Ernd r):: c in
	 	  let p = wp_asgn Fol.FVleft (Lupd(v,e)) (Ebase x) p in
	 	  wp_rnd_disj_fct side c s2 p app
    | ApiTypes.Right, _, Ast.Sasgn (Lupd(v,e), Ast.Ernd r)::c ->
	 	  let _, x = Global.fresh_var (Global.empty_venv()) "r" (EcTerm.type_of_random r) in
	 	  let c = Ast.Sasgn (Ltuple [x], Ast.Ernd r):: c in
	 	  let p = wp_asgn Fol.FVright (Lupd(v,e)) (Ebase x) p in
	 	  wp_rnd_disj_fct side s1 c p app
    | _ -> wp_rnd_disj_fct side s1 s2 p app


(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* ~~~~~~~ STRONGEST POSTCONDITION ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

exception Sp_nothing_done
exception Sp_random
exception Sp_call
exception Sp_while

(* Warning: bounded domains must be inhabited *)
let exists l p = 
  if Fol.nb_var_in_pred l p > 0 then
    Fol.exists_pred l p
  else p

let sp_single_asgn side l t pre = 
    let l = Fol.lvar_of_var l side in
    let l' = Fol.logic_lvar "l" (Fol.lv_type l) in
    let e' = Fol.subst_var_in_term l (Ebase l') t in
    let pre' = Fol.subst_in_pred l (Ebase l') pre in
    let eq_l_e' = Fol.peq e' (Ebase l) in
    exists l' (Fol.pand eq_l_e'  pre')

let sp_asgn_term side lasgn t p =
  let lv_of_v v = Fol.lvar_of_var v side in
  match lasgn with
    | Ltuple vars ->
      let lvars = List.map lv_of_v vars in
      let lvars' = List.map (fun lv -> Fol.logic_lvar (Fol.lv_name lv) 
        (Fol.lv_type lv)) lvars in
      let llvars = List.combine lvars lvars' in
      let p' = List.fold_left (fun p (l,l') -> Fol.subst_in_pred l (Ebase l') p) p llvars in
      let t' = List.fold_left (fun p (l,l') -> Fol.subst_var_in_term l (Ebase l') p) t llvars in
      let lvars'' = List.map (fun lv -> Fol.logic_lvar "l" (Fol.lv_type lv)) lvars in
      let p'' = List.fold_left (fun p (l,l'') -> Fol.pand (Fol.peq (Ebase l) (Ebase l'')) p) p' 
        (List.combine lvars lvars'') in
      let p''' = Fol.let_pred lvars'' t' p'' in
      List.fold_left (fun p lv' -> exists lv' p) p''' lvars'
    | Lupd(v, e) ->
      let lv = lv_of_v v in
      let te = Fol.term_of_exp side e in
      let t = Eapp(Global.op_upd_map v.v_type, [Ebase lv; te; t]) in
      sp_single_asgn side v t p

let sp_asgn side lasgn e p =
  if not (EcTerm.is_var_exp e) then raise Sp_random;
  sp_asgn_term side lasgn (Fol.term_of_exp side e) p




(***************)

let rec sp_instr side instr pre = match instr with
  | Sasgn (vars,e) -> sp_asgn side vars e pre
  | Sassert e -> Fol.pand pre (Fol.pred_of_exp side e)
  | Sif (e,s1,s2) ->
    let e = Fol.pred_of_exp side e in
    let p1 = Fol.pand pre e in
    let p2 = Fol.pand pre (Fol.pnot e) in
    let p1 = sp_stmt side s1 p1 in
    let p2 = sp_stmt side s2 p2 in
    Fol.por p1 p2
  | Scall _ -> raise Sp_call
  | Swhile _ -> raise Sp_while

and sp_stmt side stmt pre = List.fold_left (fun p i -> sp_instr side i p) pre stmt


(* not reversed anymore *)
let rec sp_rev spi side sr p =
  match sr with
    | [] -> [], p
    | i::sr' ->
      try sp_rev spi side sr' (spi side i p)
      with
        | Sp_call | Sp_random
        | Sp_while -> sr, p


let sp_simpl_fct s1 s2 p =
  let s1', p = sp_rev sp_instr Fol.FVleft s1 p in
  let s2', p = sp_rev sp_instr Fol.FVright s2 p in
  if EcTerm.eq_stmt s1 s1' && EcTerm.eq_stmt s2 s2' then
    raise Sp_nothing_done;
  s1', s2', p



(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** {2 Strongest Postcondition Random} *)

exception Sp_no_random

let sp_rnd_fct info s1 s2 p app =
  match s1, s2 with
    | Ast.Sasgn (l1, Ast.Ernd r1)::s1, Ast.Sasgn (l2, Ast.Ernd r2)::s2 ->
      Unification.raise_unify_type (EcTerm.type_of_random r1) 
        (EcTerm.type_of_random r2) dummy_pos "wp random rule";
      let x = Fol.logic_lvar "x" (EcTerm.type_of_random r1) in
      let y = Fol.logic_lvar "y" (EcTerm.type_of_random r2) in
      let bound1 = FunLogic.bound_random Fol.FVright (Ebase x) r1 in
      let bound2 = FunLogic.bound_random Fol.FVleft  (Ebase y) r2 in
      let (cond, cond1, cond2, fx) = cond_bij x y r1 r2 info in
      let l1, l2 = match l1, l2 with
        | Ltuple [l1], Ltuple [l2] -> l1, l2
        | _ -> bug "sp_rnd_fct: unexpected match"
      in
      (* old values of l1,l2 *)
      let l1' = Fol.logic_lvar l1.v_name l1.v_type in
      let l2' = Fol.logic_lvar l2.v_name l2.v_type in
      let l1 = Fol.lvar_of_var l1 Fol.FVleft in
      let l2 = Fol.lvar_of_var l2 Fol.FVright in
      let subst lv = 
        if Fol.eq_lvar lv l1 then Some (Ebase l1')
        else if Fol.eq_lvar lv l2 then Some (Ebase l2')
        else None
      in
      let p = Fol.subst_vars_in_pred subst p in
      let bound1 = Fol.subst_vars_in_pred subst bound1 in
      let bound2 = Fol.subst_vars_in_pred subst bound2 in
      let cond1 = Fol.subst_vars_in_pred subst cond1 in
      let cond2 = Fol.subst_vars_in_pred subst cond2 in
      let fx = Fol.subst_var_in_term l1 (Ebase l1') fx in
      let fx = Fol.subst_var_in_term l2 (Ebase l2') fx in
      let f_l1 = Fol.subst_var_in_term x (Ebase l1) fx in
      let (&&&) = Fol.pand in
      let (==>) = Fol.pimplies in
      let bound_l1 = Fol.subst_in_pred x (Ebase l1) bound1 in
      let bound_l2 = Fol.subst_in_pred y (Ebase l2) bound2 in
      let p =  
        exists l1' (exists l2' 
         (cond ==>
          ((Fol.forall_pred x (Fol.pimplies bound1 cond1)) ==> 
          ((Fol.forall_pred y (Fol.pimplies bound2 cond2)) ==> 
           (Fol.peq (Ebase l2) f_l1))) &&& 
         bound_l1 &&& bound_l2 &&& p)) in
      x, s1, s2, p, app
    | _, _ -> raise Sp_no_random

(* sp_rnd_fct wrapper *)
let sp_rnd_fct info s1 s2 p app =
  let lv_of_v side v = Fol.lvar_of_var v side in
  match s1, s2 with
    | Ast.Sasgn (Ltuple vars1, Ast.Ernd r1)::s1, Ast.Sasgn (Ltuple vars2, Ast.Ernd r2)::s2 
      when 1 < List.length vars1->
      let _, x1 = Global.fresh_var (Global.empty_venv()) "r1" (EcTerm.type_of_random r1) in
      let _, x2 = Global.fresh_var (Global.empty_venv()) "r2" (EcTerm.type_of_random r2) in
 	    let c1 = Ast.Sasgn (Ltuple [x1], Ast.Ernd r1) in
 	    let c2 = Ast.Sasgn (Ltuple [x2], Ast.Ernd r2) in
      let q,_,_,p,app = sp_rnd_fct info [c1] [c2] p app in
      (* sp here *)
      (* but... *)
      let lvars1 = List.map (lv_of_v Fol.FVleft) vars1 in
      let lvars2 = List.map (lv_of_v Fol.FVright) vars2 in
      let lvars1' = List.map 
        (fun lv -> Fol.logic_lvar (Fol.lv_name lv) (Fol.lv_type lv)) lvars1 
      in
      let lvars2' = List.map 
        (fun lv -> Fol.logic_lvar (Fol.lv_name lv) (Fol.lv_type lv)) lvars2 
      in
      let p = List.fold_left 
        (fun p (l,l') -> Fol.subst_in_pred l (Ebase l') p) p 
        (List.combine lvars1 lvars1')
      in
      let p = List.fold_left 
        (fun p (l,l') -> Fol.subst_in_pred l (Ebase l') p) p 
        (List.combine lvars2 lvars2')
      in
      let tuple1 = Epair (List.map (fun lv -> Ebase lv) lvars1) in
      let tuple2 = Epair (List.map (fun lv -> Ebase lv) lvars2) in
      let p = Fol.subst_in_pred (lv_of_v Fol.FVleft x1) tuple1 p in
      let p = Fol.subst_in_pred (lv_of_v Fol.FVright x2) tuple2 p in
      let p = List.fold_left (fun p lv' -> exists lv' p) p lvars1' in
      let p = List.fold_left (fun p lv' -> exists lv' p) p lvars2' in
      q,s1,s2,p,app
    | Ast.Sasgn (Lupd(v1,e1), Ast.Ernd r1)::s1, Ast.Sasgn (Lupd(v2,e2), Ast.Ernd r2)::s2 ->
      let _, x1 = Global.fresh_var (Global.empty_venv()) "r" (EcTerm.type_of_random r1) in
      let _, x2 = Global.fresh_var (Global.empty_venv()) "r" (EcTerm.type_of_random r2) in
 	    let c1 = Ast.Sasgn (Ltuple [x1], Ast.Ernd r1) in
 	    let c2 = Ast.Sasgn (Ltuple [x2], Ast.Ernd r2) in
      let q,_,_,p,app = sp_rnd_fct info [c1] [c2] p app in
      (* sp here *)
      let p = sp_asgn_term Fol.FVleft (Lupd(v1,e1)) (Ebase (Fol.lvar_of_var x1 Fol.FVleft)) p in
      let p = sp_asgn_term Fol.FVright (Lupd(v2,e2)) (Ebase (Fol.lvar_of_var x2 Fol.FVright)) p in
      let p = exists (lv_of_v Fol.FVleft x1) (exists (lv_of_v Fol.FVright x2) p) in
      q,s1,s2,p,app
    | Ast.Sasgn (_, Ast.Ernd _)::_, Ast.Sasgn (_, Ast.Ernd _)::_ ->
      sp_rnd_fct info s1 s2 p app
    | _ -> raise Sp_no_random

let sp_rnd_disj_fct side s1 s2 p app =
  let sp_rnd side l e = 
    let x =
      match l with
        | Ltuple [x] -> x
        | _ -> bug "unexpected match"
    in
    let x = Fol.lvar_of_var x side in
    let x' = Fol.logic_lvar (Fol.lv_name x) (Fol.lv_type x) in
    let q = Fol.logic_lvar "aux" (Fol.lv_type x) in
    let bound = FunLogic.bound_random side (Ebase q) e in
    let bound = Fol.subst_in_pred x (Ebase x') bound in
    let bound = Fol.subst_in_pred q (Ebase x) bound in
    let p = Fol.subst_in_pred x (Ebase x') p in
    x', exists x' (Fol.pand bound p)
  in
  match side, s1, s2 with
    | ApiTypes.Left, Ast.Sasgn(l1, Ast.Ernd e1)::r1, _ ->
      let x',p = sp_rnd Fol.FVleft l1 e1 in 
      x', r1, s2, p, app
    | ApiTypes.Right, _, Ast.Sasgn(l2, Ast.Ernd e2)::r2 ->
      let x',p = sp_rnd Fol.FVright l2 e2 in 
      x', s1, r2, p, app 
    | ApiTypes.Left,_,_ -> raise Sp_no_random
    | ApiTypes.Right,_,_ -> raise Sp_no_random
    | ApiTypes.Both,_, _ -> assert false


(* wrapper *)
let sp_rnd_disj_fct side s1 s2 p app =
  let lside = match side with 
    | ApiTypes.Left -> Fol.FVleft 
    | ApiTypes.Right -> Fol.FVright 
    | _ -> bug "unexpected match"
  in
  let lv_of_v v = Fol.lvar_of_var v lside in
  let sp_rnd_disj lside vars r = 
	 	  let _, x = Global.fresh_var (Global.empty_venv()) "r" (EcTerm.type_of_random r) in
 	    let s = Ast.Sasgn (Ltuple [x], Ast.Ernd r) in
	    let q,_,_,p,app = match lside with
        | Fol.FVleft -> 
          sp_rnd_disj_fct side [s] [] p app 
        | Fol.FVright -> 
          sp_rnd_disj_fct side [] [s] p app 
      in
      let lvars = List.map lv_of_v vars in
      let lvars' = List.map 
        (fun lv -> Fol.logic_lvar (Fol.lv_name lv) (Fol.lv_type lv)) lvars 
      in
      let (p:Fol.pred) = List.fold_left 
        (fun p (l,l') -> Fol.subst_in_pred l (Ebase l') p) p 
        (List.combine lvars lvars')
      in
      let tuple = Epair (List.map (fun lv -> Ebase lv) lvars) in
      let (p:Fol.pred) = Fol.subst_in_pred (lv_of_v x) tuple p in
      let p = List.fold_left (fun p lv' -> exists lv' p) p lvars' in
      q, p, app
  in
  match side, s1, s2 with
    | ApiTypes.Left, Ast.Sasgn(Ltuple vars, Ast.Ernd r)::s1, s2 when 1 < List.length vars ->
      let q,p, app = sp_rnd_disj lside vars r in
      q,s1,s2,p,app
    | ApiTypes.Right, s1, Ast.Sasgn(Ltuple vars, Ast.Ernd r)::s2 when 1 < List.length vars ->
      let q,p, app = sp_rnd_disj lside vars r in
      q,s1,s2,p,app
    | ApiTypes.Left, Ast.Sasgn(Lupd(v,e), Ast.Ernd r)::s1, s2 ->
      let _, x = Global.fresh_var (Global.empty_venv()) "r" (EcTerm.type_of_random r) in
      let x', _ ,_, p, app = sp_rnd_disj_fct side [Ast.Sasgn(Ltuple[x],Ast.Ernd r)] [] p app in
      let p = sp_asgn_term lside (Lupd(v,e)) (Ebase (Fol.lvar_of_var x lside)) p in
      x', s1, s2, exists (Fol.lvar_of_var x lside) p, app
    | ApiTypes.Right, s1, Ast.Sasgn(Lupd(v,e), Ast.Ernd r)::s2 ->
      let _, x = Global.fresh_var (Global.empty_venv()) "r" (EcTerm.type_of_random r) in
      let x', _ ,_, p, app = sp_rnd_disj_fct side [] [Ast.Sasgn(Ltuple[x],Ast.Ernd r)] p app in
      let p = sp_asgn_term lside (Lupd(v,e)) (Ebase (Fol.lvar_of_var x lside)) p in
      x', s1, s2, exists (Fol.lvar_of_var x lside) p, app
    | _ ->
      sp_rnd_disj_fct side s1 s2 p app
