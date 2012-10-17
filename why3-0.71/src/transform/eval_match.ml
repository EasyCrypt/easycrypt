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
open Ident
open Ty
open Term
open Decl
open Pretty

type inline = known_map -> lsymbol -> ty list -> ty option -> bool

let unfold def tl ty =
  let vl, e = open_ls_defn def in
  let add (mt,mv) x y = ty_match mt x.vs_ty (t_type y), Mvs.add x y mv in
  let (mt,mv) = List.fold_left2 add (Mtv.empty, Mvs.empty) vl tl in
  let mt = oty_match mt e.t_ty ty in
  t_ty_subst mt mv e

let is_constructor kn ls = match Mid.find ls.ls_name kn with
  | { d_node = Dtype _ } -> true
  | _ -> false

let rec dive env t = match t.t_node with
  | Tvar x ->
      (try dive env (Mvs.find x env) with Not_found -> t)
  | Tlet (t1, tb) ->
      let x, t2 = t_open_bound tb in
      dive (Mvs.add x t1 env) t2
  | _ -> t_map (dive env) t

let make_flat_case kn t bl =
  let mk_b b = let p,t = t_open_branch b in [p],t in
  Pattern.CompileTerm.compile (find_constructors kn) [t] (List.map mk_b bl)

let rec add_quant kn (vl,tl,f) v =
  let ty = v.vs_ty in
  let cl = match ty.ty_node with
    | Tyapp (ts, _) -> find_constructors kn ts
    | _ -> []
  in
  match cl with
    | [ls] ->
        let s = ty_match Mtv.empty (Util.of_option ls.ls_value) ty in
        let mk_v ty = create_vsymbol (id_clone v.vs_name) (ty_inst s ty) in
        let nvl = List.map mk_v ls.ls_args in
        let t = fs_app ls (List.map t_var nvl) ty in
        let f = t_let_close_simp v t f in
        let tl = tr_map (t_subst_single v t) tl in
        List.fold_left (add_quant kn) (vl,tl,f) nvl
    | _ ->
        (v::vl, tl, f)

let t_label_merge { t_label = l; t_loc = p } t =
  let p = if t.t_loc = None then p else t.t_loc in
  t_label ?loc:p (l @ t.t_label) t

let eval_match ~inline kn t =
  let rec eval env t = match t.t_node with
    | Tapp (ls, tl) when inline kn ls (List.map t_type tl) t.t_ty ->
        begin match find_logic_definition kn ls with
          | None ->
              t_map (eval env) t
          | Some def ->
              t_label_merge t (eval env (unfold def tl t.t_ty))
        end
    | Tlet (t1, tb2) ->
        let t1 = eval env t1 in
        let x, t2, close = t_open_bound_cb tb2 in
        let t2 = eval (Mvs.add x t1 env) t2 in
        t_label_merge t (t_let_simp t1 (close x t2))
    | Tcase (t1, bl1) ->
        let t1 = eval env t1 in
        let t1flat = dive env t1 in
        let r = try match t1flat.t_node with
          | Tapp (ls,_) when is_constructor kn ls ->
              eval env (make_flat_case kn t1flat bl1)
          | Tcase (t2, bl2) ->
              let mk_b b =
                let p,t = t_open_branch b in
                match t.t_node with
                  | Tapp (ls,_) when is_constructor kn ls ->
                      t_close_branch p (eval env (make_flat_case kn t bl1))
                  | _ -> raise Exit
              in
              t_case t2 (List.map mk_b bl2)
          | _ -> raise Exit
        with
          | Exit ->
              let mk_b b =
                let p,t,close = t_open_branch_cb b in
                close p (eval env t)
              in
              t_case t1 (List.map mk_b bl1)
        in
        t_label_merge t r
    | Tquant (q, qf) ->
        let vl,tl,f,close = t_open_quant_cb qf in
        let vl,tl,f = List.fold_left (add_quant kn) ([],tl,f) vl in
        t_label_merge t (t_quant_simp q (close (List.rev vl) tl (eval env f)))
    | _ ->
        t_map_simp (eval env) t
  in
  eval Mvs.empty t

let rec linear vars t = match t.t_node with
  | Tvar x when Svs.mem x vars ->
      raise Exit
  | Tvar x ->
      Svs.add x vars
  | _ ->
      t_fold linear vars t

let linear t =
  try ignore (linear Svs.empty t); true with Exit -> false

let is_algebraic_type kn ty = match ty.ty_node with
  | Tyapp (ts, _) -> find_constructors kn ts <> []
  | Tyvar _ -> false

(* The following memoization by function definition is unsafe,
   since the same definition can be used in different contexts.
   If we could produce the record updates {| x with field = v |}
   that were linear (by eliminating occurrences of x.field in v),
   inline_nonrec_linear might not call eval_match at all and so
   be independent of the context. FIXME/TODO *)

let inline_cache = Wdecl.create 17

let rec inline_nonrec_linear kn ls tyl ty =
  (* at least one actual parameter (or the result) has an algebraic type *)
  List.exists (is_algebraic_type kn) (oty_cons tyl ty) &&
  (* and ls is not recursively defined and is linear *)
  let d = Mid.find ls.ls_name kn in
  if Mid.mem ls.ls_name d.d_syms then false else
  match d.d_node with
    | Dlogic [_, Some def] ->
        begin try Wdecl.find inline_cache d with Not_found ->
          let _, t = open_ls_defn def in
          let t = eval_match ~inline:inline_nonrec_linear kn t in
          let res = linear t in
          Wdecl.set inline_cache d res;
          res
        end
    | _ -> false
