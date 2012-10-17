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

open Util
open Ident
open Ty
open Term
open Decl
open Theory
open Task

(* a type constructor tagged "enumeration" generates a finite type
   if and only if all of its non-phantom arguments are finite types *)

let meta_enum = Theory.register_meta "enumeration_type" [Theory.MTtysymbol]

let meta_phantom =
  Theory.register_meta "phantom_type_arg" [Theory.MTtysymbol;Theory.MTint]

let rec enum_ts kn sts ts =
  assert (ts.ts_def = None);
  if Sts.mem ts sts then raise Exit else
  match find_type_definition kn ts with
    | Tabstract -> raise Exit
    | Talgebraic csl ->
        let sts = Sts.add ts sts in
        let rec finite_ty stv ty = match ty.ty_node with
          | Tyvar tv -> Stv.add tv stv
          | Tyapp (ts,tl) ->
              let check acc ph ty = if ph then acc else finite_ty acc ty in
              List.fold_left2 check stv (enum_ts kn sts ts) tl
        in
        let check_cs acc ls = List.fold_left finite_ty acc ls.ls_args in
        let stv = List.fold_left check_cs Stv.empty csl in
        List.map (fun v -> not (Stv.mem v stv)) ts.ts_args

let enum_ts kn ts = try Some (enum_ts kn Sts.empty ts) with Exit -> None

let is_finite_ty enum phlist =
  let add_ph phmap = function
    | [MAts ts; MAint i] ->
        let phmap, pha = try phmap, Mts.find ts phmap with
          | Not_found ->
              let pha = Array.make (List.length ts.ts_args) false in
              Mts.add ts pha phmap, pha
        in
        Array.set pha i true;
        phmap
    | _ -> assert false
  in
  let phmap = List.fold_left add_ph Mts.empty phlist in
  let phmap = Mts.map Array.to_list phmap in
  let rec finite_ty ty = match ty.ty_node with
    | Tyapp (ts,tl) when Mts.mem ts enum ->
        let phl = try Mts.find ts phmap with Not_found ->
          List.map Util.ffalse ts.ts_args in
        List.for_all2 (fun ph ty -> ph || finite_ty ty) phl tl
    | _ -> false
  in
  finite_ty

(** Compile match patterns *)

let rec rewriteT kn t = match t.t_node with
  | Tcase (t,bl) ->
      let t = rewriteT kn t in
      let mk_b (p,t) = ([p], rewriteT kn t) in
      let bl = List.map (fun b -> mk_b (t_open_branch b)) bl in
      Pattern.CompileTerm.compile (find_constructors kn) [t] bl
  | _ -> t_map (rewriteT kn) t

let comp t task =
  let fn = rewriteT t.task_known in
  match t.task_decl.td_node with
  | Decl d -> add_decl task (decl_map fn d)
  | _ -> add_tdecl task t.task_decl

let compile_match = Trans.fold comp None

(** Eliminate algebraic types and match statements *)

type state = {
  mt_map : lsymbol Mts.t;       (* from type symbols to selector functions *)
  pj_map : lsymbol list Mls.t;  (* from constructors to projections *)
  tp_map : (tysymbol * lsymbol list) Mid.t; (* skipped tuple symbols *)
  in_smt : bool;                (* generate indexing funcitons *)
}

let empty_state smt = {
  mt_map = Mts.empty;
  pj_map = Mls.empty;
  tp_map = Mid.empty;
  in_smt = smt;
}

let uncompiled = "eliminate_algebraic: compile_match required"

let rec rewriteT kn state t = match t.t_node with
  | Tcase (t1,bl) ->
      let t1 = rewriteT kn state t1 in
      let mk_br (w,m) br =
        let (p,e) = t_open_branch br in
        let e = rewriteT kn state e in
        match p with
        | { pat_node = Papp (cs,pl) } ->
            let add_var e p pj = match p.pat_node with
              | Pvar v -> t_let_close_simp v (fs_app pj [t1] v.vs_ty) e
              | _ -> Printer.unsupportedTerm t uncompiled
            in
            let pjl = Mls.find cs state.pj_map in
            let e = List.fold_left2 add_var e pl pjl in
            w, Mls.add cs e m
        | { pat_node = Pwild } ->
            Some e, m
        | _ -> Printer.unsupportedTerm t uncompiled
      in
      let w,m = List.fold_left mk_br (None,Mls.empty) bl in
      let find cs = try Mls.find cs m with Not_found -> of_option w in
      let ts = match t1.t_ty with
        | Some { ty_node = Tyapp (ts,_) } -> ts
        | _ -> Printer.unsupportedTerm t uncompiled
      in
      begin match List.map find (find_constructors kn ts) with
        | [t] -> t
        | tl  -> t_app (Mts.find ts state.mt_map) (t1::tl) t.t_ty
      end
  | _ ->
      TermTF.t_map (rewriteT kn state) (rewriteF kn state Svs.empty true) t

and rewriteF kn state av sign f = match f.t_node with
  | Tcase (t1,bl) ->
      let t1 = rewriteT kn state t1 in
      let av' = Mvs.set_diff av t1.t_vars in
      let mk_br (w,m) br =
        let (p,e) = t_open_branch br in
        let e = rewriteF kn state av' sign e in
        match p with
        | { pat_node = Papp (cs,pl) } ->
            let get_var p = match p.pat_node with
              | Pvar v -> v
              | _ -> Printer.unsupportedTerm f uncompiled
            in
            w, Mls.add cs (List.map get_var pl, e) m
        | { pat_node = Pwild } ->
            Some e, m
        | _ -> Printer.unsupportedTerm f uncompiled
      in
      let w,m = List.fold_left mk_br (None,Mls.empty) bl in
      let find cs =
        let vl,e = try Mls.find cs m with Not_found ->
          let var = create_vsymbol (id_fresh "w") in
          let get_var pj = var (t_type (t_app_infer pj [t1])) in
          List.map get_var (Mls.find cs state.pj_map), of_option w
        in
        let hd = t_app cs (List.map t_var vl) t1.t_ty in
        match t1.t_node with
        | Tvar v when Svs.mem v av ->
            let hd = t_let_close_simp v hd e in if sign
            then t_forall_close_simp vl [] hd
            else t_exists_close_simp vl [] hd
        | _ ->
            let hd = t_equ t1 hd in if sign
            then t_forall_close_simp vl [] (t_implies_simp hd e)
            else t_exists_close_simp vl [] (t_and_simp     hd e)
      in
      let ts = match t1.t_ty with
        | Some { ty_node = Tyapp (ts,_) } -> ts
        | _ -> Printer.unsupportedTerm f uncompiled
      in
      let op = if sign then t_and_simp else t_or_simp in
      map_join_left find op (find_constructors kn ts)
  | Tquant (q, bf) when (q = Tforall && sign) || (q = Texists && not sign) ->
      let vl, tr, f1, close = t_open_quant_cb bf in
      let tr = TermTF.tr_map (rewriteT kn state)
                      (rewriteF kn state Svs.empty sign) tr in
      let av = List.fold_left (fun s v -> Svs.add v s) av vl in
      let f1 = rewriteF kn state av sign f1 in
      t_quant_simp q (close vl tr f1)
  | Tbinop (o, _, _) when (o = Tand && sign) || (o = Tor && not sign) ->
      TermTF.t_map_sign (const (rewriteT kn state))
        (rewriteF kn state av) sign f
  | Tlet (t1, _) ->
      let av = Mvs.set_diff av t1.t_vars in
      TermTF.t_map_sign (const (rewriteT kn state))
        (rewriteF kn state av) sign f
  | _ ->
      TermTF.t_map_sign (const (rewriteT kn state))
        (rewriteF kn state Svs.empty) sign f

let add_selector (state,task) ts ty csl =
  (* declare the selector function *)
  let mt_id = id_derive ("match_" ^ ts.ts_name.id_string) ts.ts_name in
  let mt_ty = ty_var (create_tvsymbol (id_fresh "a")) in
  let mt_al = ty :: List.rev_map (fun _ -> mt_ty) csl in
  let mt_ls = create_fsymbol mt_id mt_al mt_ty in
  let mtmap = Mts.add ts mt_ls state.mt_map in
  let task  = add_decl task (create_logic_decl [mt_ls, None]) in
  (* define the selector function *)
  let mt_vs _ = create_vsymbol (id_fresh "z") mt_ty in
  let mt_vl = List.rev_map mt_vs csl in
  let mt_tl = List.rev_map t_var mt_vl in
  let mt_add tsk cs t =
    let id = mt_ls.ls_name.id_string ^ "_" ^ cs.ls_name.id_string in
    let pr = create_prsymbol (id_derive id cs.ls_name) in
    let vl = List.rev_map (create_vsymbol (id_fresh "u")) cs.ls_args in
    let hd = fs_app cs (List.rev_map t_var vl) (of_option cs.ls_value) in
    let hd = fs_app mt_ls (hd::mt_tl) mt_ty in
    let vl = List.rev_append mt_vl (List.rev vl) in
    let ax = t_forall_close vl [] (t_equ hd t) in
    add_decl tsk (create_prop_decl Paxiom pr ax)
  in
  let task = List.fold_left2 mt_add task csl mt_tl in
  { state with mt_map = mtmap }, task

let add_selector (state,task) ts ty = function
  | [_] -> state, task
  | csl -> add_selector (state,task) ts ty csl

let add_indexer (state,task) ts ty csl =
  (* declare the indexer function *)
  let mt_id = id_derive ("index_" ^ ts.ts_name.id_string) ts.ts_name in
  let mt_ls = create_fsymbol mt_id [ty] ty_int in
  let task  = add_decl task (create_logic_decl [mt_ls, None]) in
  (* define the indexer function *)
  let index = ref (-1) in
  let mt_add tsk cs =
    incr index;
    let id = mt_ls.ls_name.id_string ^ "_" ^ cs.ls_name.id_string in
    let pr = create_prsymbol (id_derive id cs.ls_name) in
    let vl = List.rev_map (create_vsymbol (id_fresh "u")) cs.ls_args in
    let hd = fs_app cs (List.rev_map t_var vl) (of_option cs.ls_value) in
    let ix = t_const (ConstInt (IConstDecimal(string_of_int !index))) in
    let ax = t_equ (fs_app mt_ls [hd] ty_int) ix in
    let ax = t_forall_close (List.rev vl) [[hd]] ax in
    add_decl tsk (create_prop_decl Paxiom pr ax)
  in
  let task = List.fold_left mt_add task csl in
  state, task

let add_discriminator (state,task) ts ty csl =
  let d_add c1 task c2 =
    let id = c1.ls_name.id_string ^ "_" ^ c2.ls_name.id_string in
    let pr = create_prsymbol (id_derive id ts.ts_name) in
    let ul = List.rev_map (create_vsymbol (id_fresh "u")) c1.ls_args in
    let vl = List.rev_map (create_vsymbol (id_fresh "v")) c2.ls_args in
    let t1 = fs_app c1 (List.rev_map t_var ul) ty in
    let t2 = fs_app c2 (List.rev_map t_var vl) ty in
    let ax = t_neq t1 t2 in
    let ax = t_forall_close (List.rev vl) [[t2]] ax in
    let ax = t_forall_close (List.rev ul) [[t1]] ax in
    add_decl task (create_prop_decl Paxiom pr ax)
  in
  let rec dl_add task = function
    | c :: cl -> List.fold_left (d_add c) task cl
    | _ -> task
  in
  state, dl_add task csl

let add_indexer (state,task) ts ty = function
  | [_] -> state, task
  | csl when state.in_smt -> add_indexer (state,task) ts ty csl
  | csl when List.length csl <= 16 -> add_discriminator (state,task) ts ty csl
  | _ -> state, task

let add_projections (state,task) _ts _ty csl =
  (* declare and define the projection functions *)
  let pj_add (m,tsk) cs =
    let id = cs.ls_name.id_string ^ "_proj_" in
    let vl = List.rev_map (create_vsymbol (id_fresh "u")) cs.ls_args in
    let tl = List.rev_map t_var vl in
    let hd = fs_app cs tl (of_option cs.ls_value) in
    let c = ref 0 in
    let add (pjl,tsk) t =
      let id = id_derive (id ^ (incr c; string_of_int !c)) cs.ls_name in
      let ls = create_lsymbol id [of_option cs.ls_value] t.t_ty in
      let tsk = add_decl tsk (create_logic_decl [ls, None]) in
      let id = id_derive (ls.ls_name.id_string ^ "_def") ls.ls_name in
      let pr = create_prsymbol id in
      let hh = t_app ls [hd] t.t_ty in
      let ax = t_forall_close (List.rev vl) [] (t_equ hh t) in
      ls::pjl, add_decl tsk (create_prop_decl Paxiom pr ax)
    in
    let pjl,tsk = List.fold_left add ([],tsk) tl in
    Mls.add cs (List.rev pjl) m, tsk
  in
  let pjmap, task = List.fold_left pj_add (state.pj_map, task) csl in
  { state with pj_map = pjmap }, task

let add_inversion (state,task) ts ty csl =
  (* add the inversion axiom *)
  let ax_id = ts.ts_name.id_string ^ "_inversion" in
  let ax_pr = create_prsymbol (id_derive ax_id ts.ts_name) in
  let ax_vs = create_vsymbol (id_fresh "u") ty in
  let ax_hd = t_var ax_vs in
  let mk_cs cs =
    let pjl = Mls.find cs state.pj_map in
    let app pj = t_app_infer pj [ax_hd] in
    t_equ ax_hd (fs_app cs (List.map app pjl) ty)
  in
  let ax_f = map_join_left mk_cs t_or csl in
  let ax_f = t_forall_close [ax_vs] [] ax_f in
  let task = add_decl task (create_prop_decl Paxiom ax_pr ax_f) in
  state, task

let add_type kn (state,task) ts csl =
  (* declare constructors as abstract functions *)
  let cs_add tsk cs = add_decl tsk (create_logic_decl [cs, None]) in
  let task = List.fold_left cs_add task csl in
  (* add selector, projections, and inversion axiom *)
  let ty = ty_app ts (List.map ty_var ts.ts_args) in
  let state,task = add_selector (state,task) ts ty csl in
  let state,task = add_indexer (state,task) ts ty csl in
  let state,task = add_projections (state,task) ts ty csl in
  let state,task = add_inversion (state,task) ts ty csl in
  (* add the tags for enumeration if the type is one *)
  let task = match enum_ts kn ts with
    | None -> task
    | Some phs ->
        let task = add_meta task meta_enum [MAts ts] in
        let cpt = ref (-1) in
        let add task ph =
          incr cpt;
          if ph then
            add_meta task meta_phantom [MAts ts; MAint !cpt]
          else task in
        List.fold_left add task phs
  in
  (* return the updated state and task *)
  state, task

let comp t (state,task) = match t.task_decl.td_node with
  | Decl { d_node = Dtype dl } ->
      (* add abstract type declarations *)
      let tydl = List.map (fun (ts,_) -> [ts,Tabstract]) dl in
      let task = List.fold_left add_ty_decl task tydl in
      (* add needed functions and axioms *)
      let add acc (ts,df) = match df with
        | Tabstract      -> acc
        | Talgebraic csl -> add_type t.task_known acc ts csl
      in
      List.fold_left add (state,task) dl
  | Decl d ->
      let fnT = rewriteT t.task_known state in
      let fnF = rewriteF t.task_known state Svs.empty true in
      state, add_decl task (DeclTF.decl_map fnT fnF d)
  | _ ->
      state, add_tdecl task t.task_decl

let comp t (state,task) = match t.task_decl.td_node with
  | Decl { d_node = Dtype [ts, Talgebraic csl] } when is_ts_tuple ts ->
      let tp_map = Mid.add ts.ts_name (ts,csl) state.tp_map in
      { state with tp_map = tp_map }, task
  | Decl d ->
      let rstate,rtask = ref state, ref task in
      let add _ (ts,csl) () =
        let task = add_ty_decl !rtask [ts,Tabstract] in
        let state,task = add_type t.task_known (!rstate,task) ts csl in
        rstate := state ; rtask := task ; None
      in
      let tp_map = Mid.diff add state.tp_map d.d_syms in
      comp t ({ !rstate with tp_map = tp_map }, !rtask)
  | _ ->
      comp t (state,task)

let eliminate_algebraic_smt = Trans.compose compile_match
  (Trans.fold_map comp (empty_state true) None)

let eliminate_algebraic = Trans.compose compile_match
  (Trans.fold_map comp (empty_state false) None)

let () =
  Trans.register_transform "eliminate_algebraic_smt" eliminate_algebraic_smt

let () =
  Trans.register_transform "eliminate_algebraic" eliminate_algebraic

