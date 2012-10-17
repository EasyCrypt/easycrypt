(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-2011                                               *)
(*    François Bobot                                                      *)
(*    Jean-Christophe Filliâtre                                           *)
(*    Claude Marché                                                       *)
(*    Andrei Paskevich                                                    *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Library General Public           *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)

open Format
open Why3
open Util
open Ident
open Ty
open Term
open Decl
open Theory
open Eval_match
open Pretty
open Pgm_ttree
open Pgm_types
open Pgm_types.T
open Pgm_module

let debug = Debug.register_flag "program_wp"

(* mutable fields *)

let mutable_fields = Hts.create 17 (* ts -> field:int -> region:int *)

let declare_mutable_field ts i j =
  let h =
    try
      Hts.find mutable_fields ts
    with Not_found ->
      let h = Hashtbl.create 17 in Hts.add mutable_fields ts h; h
  in
  Hashtbl.add h i j

let get_mutable_field ts i =
  Hashtbl.find (Hts.find mutable_fields ts) i

(* phase 4: weakest preconditions *******************************************)

(* smart constructors for building WPs
   TODO: tag with label "WP" *)

let wp_label e f =
  let loc = if f.t_loc = None then Some e.expr_loc else f.t_loc in
  let lab = e.expr_lab @ f.t_label in
  t_label ?loc lab f

let wp_and ?(sym=false) f1 f2 =
  if sym then t_and_simp f1 f2 else t_and_asym_simp f1 f2

let wp_ands ?(sym=false) fl =
  if sym then t_and_simp_l fl else t_and_asym_simp_l fl

let wp_implies f1 f2 = match f2.t_node with
  | Tfalse -> t_implies f1 f2
  | _ -> t_implies_simp f1 f2

let find_ts ~pure uc s =
  ns_find_ts (get_namespace (if pure then pure_uc uc else impure_uc uc)) [s]
let find_ls ~pure uc s =
  ns_find_ls (get_namespace (if pure then pure_uc uc else impure_uc uc)) [s]

let is_arrow_ty ty = match ty.ty_node with
  | Tyapp (ts, _) -> ts_equal ts ts_arrow
  | _ -> false

let wp_forall v f =
  if is_arrow_ty v.vs_ty then f else
  (* if t_occurs_single v f then t_forall_close_simp [v] [] f else f *)
  match f.t_node with
    | Tbinop (Timplies, {t_node = Tapp (s,[{t_node = Tvar u};r])},h)
      when ls_equal s ps_equ && vs_equal u v && not (Mvs.mem v r.t_vars) ->
        t_let_close_simp v r h
    | Tbinop (Timplies, {t_node = Tbinop (Tand, g,
                        {t_node = Tapp (s,[{t_node = Tvar u};r])})},h)
      when ls_equal s ps_equ && vs_equal u v && not (Mvs.mem v r.t_vars) ->
        t_let_close_simp v r (t_implies_simp g h)
    | _ when Mvs.mem v f.t_vars ->
        t_forall_close_simp [v] [] f
    | _ ->
        f

(* utility functions for building WPs *)

let fresh_mark () =
  create_vsymbol (id_fresh "mark") ty_mark

let wp_binder x f = match x.pv_tv with
  | Tpure _ -> wp_forall x.pv_pure f
  | Tarrow _ -> f

let wp_binders = List.fold_right wp_binder

let add_binder x rm =
  let add r rm =
    let spv =
      try Spv.add x (Mreg.find r rm) with Not_found -> Spv.singleton x
    in
    Mreg.add r spv rm
  in
  Sreg.fold add x.pv_regions rm

let add_binders = List.fold_right add_binder

(* replace [at(t,'old)] with [at(t,lab)] everywhere in formula [f] *)
let old_mark lab t = t_subst_single vs_old (t_var lab) t

(* replace [at(t,lab)] with [at(t,'now)] everywhere in formula [f] *)
let erase_mark lab t = t_subst_single lab (t_var vs_now) t

let rec unref s t = match t.t_node with
  | Tvar vs ->
      begin try t_var (Mvs.find vs s) with Not_found -> t end
  | Tapp (ls, _) when ls_equal ls fs_old ->
      assert false
  | Tapp (ls, [e;{t_node = Tvar lab}]) when ls_equal ls fs_at ->
      if vs_equal lab vs_old then assert false else
      if vs_equal lab vs_now then unref s e else
      (* do not recurse in at(...) *)
      t
  | Tlet _ | Tcase _ | Teps _ | Tquant _ ->
      (* do not open unless necessary *)
      let s = Mvs.set_inter s t.t_vars in
      if Mvs.is_empty s then t else
      t_map (unref s) t
  | _ ->
      t_map (unref s) t

let find_constructor env ts =
  let km = get_known (pure_uc env) in
  match find_constructors km ts with
  | [ls] -> ls
  | _ -> assert false

let get_ty_subst ty = match ty.ty_node with
  | Tyapp (ts, tyl) ->
      let add s tv ty = Mtv.add tv ty s in
      List.fold_left2 add Mtv.empty ts.ts_args tyl
  | Tyvar _ ->
      assert false

(* x is pure, ty is effect *)
let rec update env mreg x ty =
  if Mtv.is_empty mreg then
    t_var x
  else match ty.ty_node with
  | Tyapp (ts, tyl) ->
      let cl = find_constructors (get_known (effect_uc env)) ts in
      if cl = [] then failwith "WP: cannot update a value of this type";
      (* TODO: print the type *)
      let s = get_ty_subst ty in
      let branch cs =
        let cs_pure = (get_psymbol cs).ps_pure in
        let mk_var ty =
          let ty = ty_inst s ty in
          let ty_pure = purify ty in
          create_vsymbol (id_fresh "y") ty_pure, ty
        in
        let vars = List.map mk_var cs.ls_args in
        let pat_vars = List.map (fun (y, _) -> pat_var y) vars in
        let pat = pat_app cs_pure pat_vars x.vs_ty in
        let mk_arg i (y, ty) =
          let y =
            try
              let j = get_mutable_field ts i in
              begin match (List.nth tyl j).ty_node with
                | Tyvar tv -> Mtv.find tv mreg
                | Tyapp _ -> assert false
              end
            with Not_found ->
              y
          in
          let keep tv _ = Stv.mem tv (ty_freevars Stv.empty ty) in
          let mreg = Mtv.filter keep mreg in
          update env mreg y ty
        in
        let t = fs_app cs_pure (list_mapi mk_arg vars) x.vs_ty in
        t_close_branch pat t
      in
      t_case (t_var x) (List.map branch cl)
  | Tyvar _ ->
      assert false

(* quantify over all references in ef
   ef : effect
   rm : region -> pvsymbol set
   f  : formula

   let ef = { rho1, ..., rhon }
   we collect in vars all variables involving these regions
   let vars = { v1, ..., vm }

     forall r1:ty(rho1). ... forall rn:ty(rhon).
     let v'1 = update v1 r1...rn in
     ...
     let v'm = update vm r1...rn in
     f[vi <- v'i]
*)
let quantify env rm sreg f =
  (* all program variables involving these regions *)
  let vars =
    let add r s =
      try Spv.union (Mreg.find r rm) s with Not_found -> assert false
    in
    Sreg.fold add sreg Spv.empty
  in
  (* mreg: rho -> rho' *)
  let mreg =
    let add r m =
      let vars = Mreg.find r rm in
      let test x acc = match x.pv_effect.vs_ty.ty_node with
        | Tyapp (ts,{ ty_node = Tyvar tv }::_) when tv_equal tv r.R.r_tv ->
            let mt = get_mtsymbol ts in
            if mt.mt_regions = 1 then
              Some x.pv_effect.vs_name
            else acc
        | Tyapp _ -> acc
        | Tyvar _ -> assert false
      in
      let id = Spv.fold test vars None in
      let id = id_clone (default_option r.R.r_tv.tv_name id) in
      let r' = create_vsymbol id (purify r.R.r_ty) in
      Mtv.add r.R.r_tv r' m
    in
    Sreg.fold add sreg Mtv.empty
  in
  let vv' =
    let add pv s =
      let v = pv.pv_pure in
      let v' = create_vsymbol (id_clone v.vs_name) v.vs_ty in
      Mvs.add v v' s
    in
    Spv.fold add vars Mvs.empty
  in
  let f = unref vv' f in
  let f =
    let add_update x f =
      let v' = Mvs.find x.pv_pure vv' in
      let updatev = update env mreg x.pv_pure x.pv_effect.vs_ty in
      t_let_close_simp v' updatev f
    in
    Spv.fold add_update vars f
  in
  let quantify_r _ r' f = wp_forall r' f in
  Mtv.fold quantify_r mreg f

let wp_close_state env rm ef f =
  let sreg = Sreg.union ef.E.reads ef.E.writes in
  quantify env rm sreg f

let wp_close rm ef f =
  let sreg = ef.E.writes in
  let sreg = Sreg.union ef.E.reads sreg in
  (* all program variables involving these regions *)
  let vars =
    let add r s =
      try Spv.union (Mreg.find r rm) s with Not_found -> assert false
    in
    Sreg.fold add sreg Spv.empty
  in
  let quantify_v v f = wp_forall v.pv_pure f in
  Spv.fold quantify_v vars f

(* let quantify ?(all=false) env rm ef f = *)
(*   let r = quantify ~all env rm ef f in *)
(*   eprintf "@[<hov 2>quantify: all=%b ef=%a f=@[%a@] ==>@\n%a@]@." *)
(*     all E.print ef Pretty.print_term f Pretty.print_term r; *)
(*   r *)

let abstract_wp env rm ef (q',ql') (q,ql) =
  assert (List.length ql' = List.length ql);
  let quantify_res f' f res =
    let f = wp_implies f' f in
    let f = match res with
      (* | Some v when is_mutable_ty v.vs_ty -> *)
      (*          let v' = create_vsymbol (id_clone v.vs_name) (unref_ty env v.vs_ty) in *)
      (*          wp_forall v' (unref env (R.Rlocal v) v' f) *)
      | Some v ->
          wp_forall v f
      | None ->
          f
    in
    quantify env rm ef f
  in
  let quantify_h (e',(x',f')) (e,(x,f)) =
    assert (ls_equal e' e);
    let res, f' = match x', x with
      | Some v', Some v -> Some v, t_subst_single v' (t_var v) f'
      | None, None -> None, f'
      | _ -> assert false
    in
    quantify_res f' f res
  in
  let f =
    let res, f = q and res', f' = q' in
    let f' =
      if is_arrow_ty res'.vs_ty then f'
      else t_subst_single res' (t_var res) f'
    in
    quantify_res f' f (Some res)
  in
  wp_ands (f :: List.map2 quantify_h ql' ql)

let opaque_wp env rm ef q' q =
  let lab = fresh_mark () in
  let q' = post_map (old_mark lab) q' in
  let f = abstract_wp env rm ef q' q in
  erase_mark lab f

(*s [filter_post k q] removes exc. postconditions from [q] which do not
    appear in effect [ef] *)

let filter_post ef (q, ql) =
  let keep (ls, _) = Sexn.mem ls ef.E.raises in
  q, List.filter keep ql

let rec ls_assoc ls = function
  | [] -> raise Not_found
  | (ls', x) :: _ when ls_equal ls ls' -> x
  | _ :: r -> ls_assoc ls r

let default_exn_post ls = ls, (exn_v_result ls, t_true)

let default_post ty ef =
  (v_result ty, t_true),
  List.map default_exn_post (Sexn.elements ef.E.raises)

let rec assoc_handler x = function
  | [] -> raise Not_found
  | (y, h) :: _ when ls_equal x y -> h
  | _ :: hl -> assoc_handler x hl

(*s [saturate_post ef f q] makes a postcondition for a program of effect [ef]
    out of a normal postcondition [f] and the exc. postconditions from [q] *)

let saturate_post ef q (_, ql) =
  let set_post x = try x, ls_assoc x ql with Not_found -> default_exn_post x in
  let xs = Sexn.elements ef.E.raises in
  (q, List.map set_post xs)

(* maximum *)

let is_default_post = t_equal t_true

let sup ((q, ql) : post) (_, ql') =
  assert (List.length ql = List.length ql');
  let supx (x, (_,fa) as a) (x', _ as a') =
    assert (ls_equal x x');
    if is_default_post fa then a' else a
  in
  q, List.map2 supx ql ql'

(* post-condition for a loop body *)

let default_exns_post ef =
  let xs = Sexn.elements ef.E.raises in
  List.map default_exn_post xs

let term_at lab t =
  t_app fs_at [t; t_var lab] t.t_ty

let wp_expl l f =
  t_label ?loc:f.t_loc (("expl:"^l)::Split_goal.stop_split::f.t_label) f

(* 0 <= phi0 and phi < phi0 *)
let default_variant le lt phi phi0 =
  t_and
    (ps_app le [t_int_const "0"; phi0])
    (ps_app lt  [phi; phi0])

let while_post_block inv var lab e =
  let decphi = match var with
    | None ->
        t_true
    | Some (phi, Vint (le, lt)) ->
        let old_phi = term_at lab phi in
        default_variant le lt phi old_phi
    | Some (phi, Vuser r) ->
        ps_app r [phi; term_at lab phi]
  in
  let decphi = wp_expl "loop variant decreases" decphi in
  let ql = default_exns_post e.expr_effect in
  let res = v_result e.expr_type in
  match inv with
    | None ->
        (res, decphi), ql
    | Some i ->
        (res, wp_and (wp_expl "loop invariant preservation" i) decphi), ql

let well_founded_rel = function
  | None -> t_true
  | Some _ -> t_true (* TODO: Papp (well_founded, [Tvar r], []) *)

(* Recursive computation of the weakest precondition *)

let ty_bool env = ty_app (find_ts ~pure:true env "bool")  []
let t_True  env = fs_app (find_ls ~pure:true env "True")  [] (ty_bool env)
let t_False env = fs_app (find_ls ~pure:true env "False") [] (ty_bool env)
let mk_t_if env f = t_if f (t_True env) (t_False env)

let ls_absurd = create_lsymbol (id_fresh "absurd") [] None
let t_absurd  = ps_app ls_absurd []

(*
  env : module_uc
  rm  : Spv.t Mreg.t (maps regions to pvsymbol sets)
*)

let rec wp_expr env rm e q =
  let lab = fresh_mark () in
  let q = post_map (old_mark lab) q in
  let f = wp_desc env rm e q in
  let f = erase_mark lab f in
  if Debug.test_flag debug then begin
    eprintf "@[--------@\n@[<hov 2>e = %a@]@\n" Pgm_pretty.print_expr e;
    eprintf "@[<hov 2>q = %a@]@\n" Pretty.print_term (snd (fst q));
    eprintf "@[<hov 2>f = %a@]@\n----@]@." Pretty.print_term f;
  end;
  f

and wp_desc env rm e q = match e.expr_desc with
  | Elogic t ->
      let (v, q), _ = q in
      let t = wp_label e t in
      let t = if t.t_ty = None then mk_t_if env t else t in
      t_subst_single v t q
  | Elocal pv ->
      let (v, q), _ = q in
      t_subst_single v (wp_label e (t_var pv.pv_pure)) q
  | Eglobal { ps_kind = PSvar pv } ->
      let (v, q), _ = q in
      t_subst_single v (wp_label e (t_var pv.pv_pure)) q
  | Eglobal { ps_kind = PSfun _ } ->
      let (_, q), _ = q in wp_label e q
  | Eglobal { ps_kind = PSlogic } ->
      assert false
  | Efun (bl, t) ->
      let (_, q), _ = q in
      let f = wp_triple env rm bl t in
      wp_and ~sym:true (wp_label e f) q
  | Elet (x, e1, e2) ->
      let w2 =
        let rm = add_binder x rm in
        wp_expr env rm e2 (filter_post e2.expr_effect q)
      in
      let v1 = v_result x.pv_pure.vs_ty in
      let t1 = t_label ~loc:e1.expr_loc ["let"] (t_var v1) in
      let q1 = v1, t_subst_single x.pv_pure t1 w2 in
      let q1 = saturate_post e1.expr_effect q1 q in
      wp_label e (wp_expr env rm e1 q1)
  | Eletrec (dl, e1) ->
      let w1 = wp_expr env rm e1 q in
      let wl = List.map (wp_recfun env rm) dl in
      wp_label e (wp_ands ~sym:true (w1 :: wl)) (* FIXME? *)
  | Eif (e1, e2, e3) ->
      let res = v_result e1.expr_type in
      let test = t_equ (t_var res) (t_True env) in
      (* if both branches are pure, do not split *)
      let q1 =
        try
          let r2 = match e2.expr_desc with
            | Elogic t -> t
            | Elocal pv -> t_var pv.pv_pure
            | Eglobal { ps_kind = PSvar pv } -> t_var pv.pv_pure
            | _ -> raise Exit in
          let r3 = match e3.expr_desc with
            | Elogic t -> t
            | Elocal pv -> t_var pv.pv_pure
            | Eglobal { ps_kind = PSvar pv } -> t_var pv.pv_pure
            | _ -> raise Exit in
          let (v, q), _ = q in
          t_subst_single v (t_if_simp test r2 r3) q
        with Exit ->
          let w2 = wp_expr env rm e2 (filter_post e2.expr_effect q) in
          let w3 = wp_expr env rm e3 (filter_post e3.expr_effect q) in
          t_if_simp test w2 w3
      in
      let q1 = saturate_post e1.expr_effect (res, q1) q in
      wp_label e (wp_expr env rm e1 q1) (* FIXME? *)
  | Eloop ({ loop_invariant = inv; loop_variant = var }, e1) ->
      let wfr = well_founded_rel var in
      let lab = fresh_mark () in
      let q1 = while_post_block inv var lab e1 in
      let q1 = sup q1 q in (* exc. posts taken from [q] *)
      let we = wp_expr env rm e1 q1 in
      let we = erase_mark lab we in
      let sreg = e.expr_effect.E.writes in
      let w = match inv with
        | None ->
            wp_and wfr (quantify env rm sreg we)
        | Some i ->
            wp_and wfr
              (wp_and ~sym:true
                 (wp_expl "loop invariant init" i)
                 (quantify env rm sreg (wp_implies i we)))
      in
      wp_label e w (* FIXME? *)
  (* optimization for the particular case let _ = y in e *)
  | Ematch (_, [{ppat_pat = {pat_node = Term.Pwild}}, e]) ->
      wp_label e (wp_expr env rm e (filter_post e.expr_effect q))
  | Ematch (x, bl) ->
      let branch (p, e) =
        t_close_branch p.ppat_pat
          (wp_expr env rm e (filter_post e.expr_effect q))
      in
      let t = t_var x.pv_pure in
      wp_label e (t_case t (List.map branch bl))
  | Eabsurd ->
      wp_label e t_absurd
  | Eraise (x, None) ->
      (* $wp(raise E, _, R) = R$ *)
      let _, ql = q in
      let _, f = assoc_handler x ql in
      wp_label e f
  | Eraise (x, Some e1) ->
      (* $wp(raise (E e1), _, R) = wp(e1, R, R)$ *)
      let _, ql = q in
      let q1 = match assoc_handler x ql with
        | Some v, r -> (v, r), ql
        | None, _ -> assert false
      in
      let q1 = filter_post e1.expr_effect q1 in
      wp_label e (wp_expr env rm e1 q1)
  | Etry (e1, hl) ->
      (* $wp(try e1 with E -> e2, Q, R) = wp(e1, Q, wp(e2, Q, R))$ *)
      let hwl =
        List.map
          (fun (x, v, h) ->
             let w = wp_expr env rm h (filter_post h.expr_effect q) in
             let v = option_map (fun v -> v.pv_pure) v in
             x, (v, w))
          hl
      in
      let make_post (q, ql) =
        let hpost (x, r) =
          x, try assoc_handler x hwl with Not_found -> r
        in
        q, List.map hpost ql
      in
      let q1 = saturate_post e1.expr_effect (fst q) q in
      let q1 = filter_post e1.expr_effect (make_post q1) in
      wp_label e (wp_expr env rm e1 q1)
  | Efor (x, v1, d, v2, inv, e1) ->
      (* wp(for x = v1 to v2 do inv { I(x) } e1, Q, R) =
             v1 > v2  -> Q
         and v1 <= v2 ->     I(v1)
                         and forall S. forall i. v1 <= i <= v2 ->
                                                 I(i) -> wp(e1, I(i+1), R)
                                       and I(v2+1) -> Q                    *)
      let (res, q1), _ = q in
      let gt, le, incr = match d with
        | Ptree.To     ->
            find_ls ~pure:true env "infix >",
            find_ls ~pure:true env "infix <=", t_int_const  "1"
        | Ptree.Downto ->
            find_ls ~pure:true env "infix <",
            find_ls ~pure:true env "infix >=", t_int_const "-1"
      in
      let v1_gt_v2 = ps_app gt [t_var v1.pv_pure; t_var v2.pv_pure] in
      let v1_le_v2 = ps_app le [t_var v1.pv_pure; t_var v2.pv_pure] in
      let inv = match inv with Some inv -> inv | None -> t_true in
      let add = find_ls~pure:true env "infix +" in
      let wp1 =
        let xp1 = fs_app add [t_var x.pv_pure; incr] ty_int in
        let post = t_subst_single x.pv_pure xp1 inv in
        let q1 = saturate_post e1.expr_effect (res, post) q in
        wp_expr env rm e1 q1
      in
      let f = wp_and ~sym:true
        (wp_expl "for loop initialization"
           (t_subst_single x.pv_pure (t_var v1.pv_pure) inv))
        (quantify env rm e.expr_effect.E.writes
           (wp_and ~sym:true
              (wp_expl "for loop preservation"
                (wp_forall x.pv_pure
                 (wp_implies
                    (wp_and (ps_app le [t_var v1.pv_pure; t_var x.pv_pure])
                            (ps_app le [t_var x.pv_pure;  t_var v2.pv_pure]))
                 (wp_implies inv wp1))))
              (let sv2 = fs_app add [t_var v2.pv_pure; incr] ty_int in
               wp_implies (t_subst_single x.pv_pure sv2 inv) q1)))
      in
      let f =
        wp_and ~sym:true (wp_implies v1_gt_v2 q1) (wp_implies v1_le_v2 f) in
      wp_label e f (* FIXME? *)
  | Eassert (Ptree.Aassert, f) ->
      let (_, q), _ = q in
      let f = wp_expl "assertion" f in
      wp_and (wp_label e f) q   (* FIXME? *)
  | Eassert (Ptree.Acheck, f) ->
      let (_, q), _ = q in
      let f = wp_expl "check" f in
      wp_and ~sym:true (wp_label e f) q  (* FIXME? *)
  | Eassert (Ptree.Aassume, f) ->
      let (_, q), _ = q in
      wp_implies (wp_label e f) q  (* FIXME? *)
  | Emark (lab, e1) ->
      let w1 = wp_expr env rm e1 q in
      wp_label e (erase_mark lab w1) (* FIXME? *)
  | Eany c ->
      (* TODO: propagate call labels into c.c_post *)
      let w = opaque_wp env rm c.c_effect.E.writes c.c_post q in
      let p = wp_expl "precondition" c.c_pre in
      let p = t_label ~loc:e.expr_loc (p.t_label @ e.expr_lab) p in
      wp_and p w

and wp_triple env rm bl (p, e, q) =
  let rm = add_binders bl rm in
  let q =
    let (v, q), l = q in
    (v, wp_expl "normal postcondition" q),
    List.map (fun (e, (v, q)) ->
                e, (v, wp_expl "exceptional postcondition" q)) l
  in
  let f = wp_expr env rm e q in
  let f = wp_implies p f in
  let f = wp_close_state env rm e.expr_effect f in
  wp_binders bl f

and wp_recfun env rm (_, bl, t, _) =
  wp_triple env rm bl t

let global_regions = ref Mreg.empty

let declare_global_regions pv = global_regions := add_binder pv !global_regions

(* WP functions with quantification over global variables *)

let wp env e =
  let rm = !global_regions in
  let f = wp_expr env rm e (default_post e.expr_type e.expr_effect) in
  wp_close rm e.expr_effect f

let wp_rec env (_,_,_,ef as def) =
  let rm = !global_regions in
  let f = wp_recfun env rm def in
  wp_close rm ef f

let bool_to_prop env f =
  let ts_bool  = find_ts ~pure:true env "bool" in
  let ls_andb  = find_ls ~pure:true env "andb" in
  let ls_orb   = find_ls ~pure:true env "orb" in
  let ls_notb  = find_ls ~pure:true env "notb" in
  let ls_True  = find_ls ~pure:true env "True" in
  let ls_False = find_ls ~pure:true env "False" in
  let t_True   = fs_app ls_True [] (ty_app ts_bool []) in
  let rec t_btop t = t_label ?loc:t.t_loc t.t_label (* t_label_copy? *)
    (match t.t_node with
    | Tif (f,t1,t2) ->
        t_if_simp (f_btop f) (t_btop t1) (t_btop t2)
    | Tapp (ls, [t1;t2]) when ls_equal ls ls_andb ->
        t_and_simp (t_btop t1) (t_btop t2)
    | Tapp (ls, [t1;t2]) when ls_equal ls ls_orb ->
        t_or_simp (t_btop t1) (t_btop t2)
    | Tapp (ls, [t1]) when ls_equal ls ls_notb ->
        t_not_simp (t_btop t1)
    | Tapp (ls, []) when ls_equal ls ls_True ->
        t_true
    | Tapp (ls, []) when ls_equal ls ls_False ->
        t_false
    | _ ->
        t_equ_simp (f_btop t) t_True)
  and f_btop f = match f.t_node with
    | Tapp (ls, [{t_ty = Some {ty_node = Tyapp (ts, [])}} as l; r])
    when ls_equal ls ps_equ && ts_equal ts ts_bool ->
        t_label ?loc:f.t_loc f.t_label
          (t_iff_simp (t_btop l) (t_btop r))
    | _ -> t_map_simp f_btop f
  in
  f_btop f

(* replace every occurrence of [at(t,'now)] with [t] *)
let rec remove_at f = match f.t_node with
  | Tapp (ls, [t;{t_node = Tvar lab}])
    when ls_equal ls fs_at && vs_equal lab vs_now ->
      remove_at t
  | _ ->
      t_map remove_at f

(* replace t_absurd with t_false *)
let rec unabsurd f = match f.t_node with
  | Tapp (ls, []) when ls_equal ls ls_absurd ->
      t_label_copy f t_false
  | _ ->
      t_map unabsurd f

let add_wp_decl ps f uc =
  (* prepare a proposition symbol *)
  let name = ps.ps_pure.ls_name in
  let s = "WP_" ^ name.id_string in
  let label = ("expl:" ^ name.id_string) :: name.id_label in
  let id = id_fresh ~label ?loc:name.id_loc s in
  let pr = create_prsymbol id in
  (* prepare the VC formula *)
  let km = get_known (pure_uc uc) in
  let f = remove_at f in
  let f = bool_to_prop uc f in
  let f = eval_match ~inline:inline_nonrec_linear km f in
  let f = unabsurd f in
  (* printf "wp: f=%a@." print_term f; *)
  let d = create_prop_decl Pgoal pr f in
  add_pure_decl d uc

let decl uc = function
  | Pgm_ttree.Dlet (ps, e) ->
      Debug.dprintf debug "@[--effect %s-----@\n  %a@]@\n----------------@."
          ps.ps_pure.ls_name.id_string print_type_v e.expr_type_v;
      let f = wp uc e in
      Debug.dprintf debug "wp = %a@\n----------------@." Pretty.print_term f;
      add_wp_decl ps f uc
  | Pgm_ttree.Dletrec dl ->
      let add_one uc (ps, def) =
        let f = wp_rec uc def in
        Debug.dprintf debug "wp %s = %a@\n----------------@."
           ps.ps_pure.ls_name.id_string Pretty.print_term f;
        add_wp_decl ps f uc
      in
      List.fold_left add_one uc dl
  | Pgm_ttree.Dparam _ ->
      uc

(*
Local Variables:
compile-command: "unset LANG; make -C ../.. testl"
End:
*)
