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
open Pp
open Util
open Ident
open Ptree
open Ty
open Term
open Theory

exception AnyMessage of string

let error ?loc e = match loc with
  | None -> raise e
  | Some loc -> raise (Loc.Located (loc,e))

let () = Exn_printer.register (fun fmt e -> match e with
  | AnyMessage s -> fprintf fmt "%s" s
  | _ -> raise e)

(** types with destructive type variables *)

type dty_view =
  | Tyvar of type_var
  | Tyapp of tysymbol * dty_view list

and type_var = {
  tag : int;
  user : bool;
  tvsymbol : tvsymbol;
  mutable type_val : dty_view option;
  type_var_loc : loc option;
}

let tyvar v = Tyvar v

let rec type_inst s ty = match ty.ty_node with
  | Ty.Tyvar n -> Mtv.find n s
  | Ty.Tyapp (ts, tyl) -> Tyapp (ts, List.map (type_inst s) tyl)

let tyapp ts tyl = match ts.ts_def with
  | None ->
      Tyapp (ts, tyl)
  | Some ty ->
      let add m v t = Mtv.add v t m in
      let s = List.fold_left2 add Mtv.empty ts.ts_args tyl in
      type_inst s ty

type dty = dty_view

let tvsymbol_of_type_var tv = tv.tvsymbol

let rec print_dty fmt = function
  | Tyvar { type_val = Some t } ->
      print_dty fmt t
  | Tyvar { type_val = None; tvsymbol = v } ->
      Pretty.print_tv fmt v
  | Tyapp (s, []) ->
      fprintf fmt "%s" s.ts_name.id_string
  | Tyapp (s, [t]) ->
      fprintf fmt "%s %a" s.ts_name.id_string print_dty t
  | Tyapp (s, l) ->
      fprintf fmt "%s %a" s.ts_name.id_string (print_list space print_dty) l

let rec view_dty = function
  | Tyvar { type_val = Some dty } -> view_dty dty
  | dty -> dty

let create_ty_decl_var =
  let t = ref 0 in
  fun ?loc ~user tv ->
    incr t;
    { tag = !t; user = user; tvsymbol = tv; type_val = None;
      type_var_loc = loc }

let rec occurs v = function
  | Tyvar { type_val = Some t } -> occurs v t
  | Tyvar { tag = t; type_val = None } -> v.tag = t
  | Tyapp (_, l) -> List.exists (occurs v) l

(* destructive type unification *)
let rec unify t1 t2 = match t1, t2 with
  | Tyvar { type_val = Some t1 }, _ ->
      unify t1 t2
  | _, Tyvar { type_val = Some t2 } ->
      unify t1 t2
  | Tyvar v1, Tyvar v2 when v1.tag = v2.tag ->
      true
        (* instantiable variables *)
  | Tyvar ({user=false} as v), t
  | t, Tyvar ({user=false} as v) ->
      not (occurs v t) && (v.type_val <- Some t; true)
        (* recursive types *)
  | Tyapp (s1, l1), Tyapp (s2, l2) ->
      ts_equal s1 s2 && List.length l1 = List.length l2 &&
          List.for_all2 unify l1 l2
  | Tyapp _, _ | _, Tyapp _ ->
      false
        (* other cases *)
  | Tyvar {user=true; tag=t1}, Tyvar {user=true; tag=t2} ->
      t1 = t2

(* intermediate types -> types *)
let rec ty_of_dty = function
  | Tyvar { type_val = Some t } ->
      ty_of_dty t
  | Tyvar { type_val = None; user = false; type_var_loc = loc } ->
      error ?loc (AnyMessage "undefined type variable")
  | Tyvar { tvsymbol = tv } ->
      ty_var tv
  | Tyapp (s, tl) ->
      ty_app s (List.map ty_of_dty tl)

type ident = Ptree.ident

type dpattern = { dp_node : dpattern_node; dp_ty : dty }

and dpattern_node =
  | Pwild
  | Pvar of ident
  | Papp of lsymbol * dpattern list
  | Por of dpattern * dpattern
  | Pas of dpattern * ident

let create_user_id { id = x ; id_lab = ll ; id_loc = loc } =
  let get_labels (ll,p) = function
    | Lstr l -> l::ll, p
    | Lpos p -> ll, Some p
  in
  let label,p = List.fold_left get_labels ([],None) ll in
  id_user ~label x (default_option loc p)

let create_user_vs id ty = create_vsymbol (create_user_id id) ty

let rec pattern_env env p = match p.dp_node with
  | Pwild -> env
  | Papp (_, pl) -> List.fold_left pattern_env env pl
  | Por (p, _) -> pattern_env env p
  | Pvar id ->
      let vs = create_user_vs id (ty_of_dty p.dp_ty) in
      Mstr.add id.id vs env
  | Pas (p, id) ->
      let vs = create_user_vs id (ty_of_dty p.dp_ty) in
      pattern_env (Mstr.add id.id vs env) p

let get_pat_var env p x = try Mstr.find x env with Not_found ->
  raise (Term.UncoveredVar (create_vsymbol (id_fresh x) (ty_of_dty p.dp_ty)))

let rec pattern_pat env p = match p.dp_node with
  | Pwild -> pat_wild (ty_of_dty p.dp_ty)
  | Pvar x -> pat_var (get_pat_var env p x.id)
  | Pas (p, x) -> pat_as (pattern_pat env p) (get_pat_var env p x.id)
  | Por (p, q) -> pat_or (pattern_pat env p) (pattern_pat env q)
  | Papp (s, pl) ->
      pat_app s (List.map (pattern_pat env) pl) (ty_of_dty p.dp_ty)

let pattern env p = let env = pattern_env env p in env, pattern_pat env p

type dterm = { dt_node : dterm_node; dt_ty : dty }

and dterm_node =
  | Tvar of string
  | Tconst of constant
  | Tapp of lsymbol * dterm list
  | Tif of dfmla * dterm * dterm
  | Tlet of dterm * ident * dterm
  | Tmatch of dterm * (dpattern * dterm) list
  | Tnamed of label * dterm
  | Teps of ident * dty * dfmla

and dfmla =
  | Fapp of lsymbol * dterm list
  | Fquant of quant * (ident * dty) list * dtrigger list list * dfmla
  | Fbinop of binop * dfmla * dfmla
  | Fnot of dfmla
  | Ftrue
  | Ffalse
  | Fif of dfmla * dfmla * dfmla
  | Flet of dterm * ident * dfmla
  | Fmatch of dterm * (dpattern * dfmla) list
  | Fnamed of label * dfmla
  | Fvar of term

and dtrigger =
  | TRterm of dterm
  | TRfmla of dfmla

let rec term env t = match t.dt_node with
  | Tvar x ->
      assert (Mstr.mem x env);
      t_var (Mstr.find x env)
  | Tconst c ->
      t_const c
  | Tapp (s, tl) ->
      fs_app s (List.map (term env) tl) (ty_of_dty t.dt_ty)
  | Tif (f, t1, t2) ->
      t_if (fmla env f) (term env t1) (term env t2)
  | Tlet (e1, id, e2) ->
      let e1 = term env e1 in
      let v = create_user_vs id (t_type e1) in
      let env = Mstr.add id.id v env in
      let e2 = term env e2 in
      t_let_close v e1 e2
  | Tmatch (t1, bl) ->
      let branch (p,e) =
        let env, p = pattern env p in t_close_branch p (term env e)
      in
      t_case (term env t1) (List.map branch bl)
  | Tnamed _ ->
      let rec collect p ll e = match e.dt_node with
        | Tnamed (Lstr l, e) -> collect p (l::ll) e
        | Tnamed (Lpos p, e) -> collect (Some p) ll e
        | _ -> t_label ?loc:p (List.rev ll) (term env e)
      in
      collect None [] t
  | Teps (id, ty, e1) ->
      let v = create_user_vs id (ty_of_dty ty) in
      let env = Mstr.add id.id v env in
      let e1 = fmla env e1 in
      t_eps_close v e1

and fmla env = function
  | Ftrue ->
      t_true
  | Ffalse ->
      t_false
  | Fnot f ->
      t_not (fmla env f)
  | Fbinop (op, f1, f2) ->
      t_binary op (fmla env f1) (fmla env f2)
  | Fif (f1, f2, f3) ->
      t_if (fmla env f1) (fmla env f2) (fmla env f3)
  | Fquant (q, uqu, trl, f1) ->
      let uquant env (id,ty) =
        let v = create_user_vs id (ty_of_dty ty) in
        Mstr.add id.id v env, v
      in
      let env, vl = map_fold_left uquant env uqu in
      let trigger = function
        | TRterm t -> term env t
        | TRfmla f -> fmla env f
      in
      let trl = List.map (List.map trigger) trl in
      t_quant_close q vl trl (fmla env f1)
  | Fapp (s, tl) ->
      ps_app s (List.map (term env) tl)
  | Flet (e1, id, f2) ->
      let e1 = term env e1 in
      let v = create_user_vs id (t_type e1) in
      let env = Mstr.add id.id v env in
      let f2 = fmla env f2 in
      t_let_close v e1 f2
  | Fmatch (t, bl) ->
      let branch (p,e) =
        let env, p = pattern env p in t_close_branch p (fmla env e)
      in
      t_case (term env t) (List.map branch bl)
  | (Fnamed _) as f ->
      let rec collect p ll = function
        | Fnamed (Lstr l, e) -> collect p (l::ll) e
        | Fnamed (Lpos p, e) -> collect (Some p) ll e
        | e -> t_label ?loc:p (List.rev ll) (fmla env e)
      in
      collect None [] f
  | Fvar f ->
      f

(* Specialize *)

let find_type_var ~loc env tv =
  try
    Htv.find env tv
  with Not_found ->
    let v = create_ty_decl_var ~loc ~user:false tv in
    Htv.add env tv v;
    v

let rec specialize_ty ~loc env t = match t.ty_node with
  | Ty.Tyvar tv ->
      Tyvar (find_type_var ~loc env tv)
  | Ty.Tyapp (s, tl) ->
      Tyapp (s, List.map (specialize_ty ~loc env) tl)

let specialize_lsymbol ~loc s =
  let tl = s.ls_args in
  let t = s.ls_value in
  let env = Htv.create 17 in
  List.map (specialize_ty ~loc env) tl, option_map (specialize_ty ~loc env) t

