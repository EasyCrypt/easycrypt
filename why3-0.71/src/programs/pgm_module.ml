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

open Why3
open Util
open Ident
open Ty
open Decl
open Theory
open Term

open Pgm_types
open Pgm_types.T
open Pgm_ttree

type namespace = {
  ns_ex : esymbol   Mstr.t;  (* exceptions*)
  ns_ns : namespace Mstr.t;  (* inner namespaces *)
}

let empty_ns = {
  ns_ex = Mstr.empty;
  ns_ns = Mstr.empty;
}

exception ClashSymbol of string

let ns_replace eq chk x vo vn =
  if not chk then vn else
  if eq vo vn then vo else
  raise (ClashSymbol x)

let ns_union eq chk =
  Mstr.union (fun x vn vo -> Some (ns_replace eq chk x vo vn))

let rec merge_ns chk ns1 ns2 =
  let fusion _ ns1 ns2 = Some (merge_ns chk ns1 ns2) in
  { ns_ex = ns_union ls_equal chk ns1.ns_ex ns2.ns_ex;
    ns_ns = Mstr.union fusion      ns1.ns_ns ns2.ns_ns; }

let nm_add chk x ns m = Mstr.change x (function
  | None -> Some ns
  | Some os -> Some (merge_ns chk ns os)) m

let ns_add eq chk x v m = Mstr.change x (function
  | None -> Some v
  | Some vo -> Some (ns_replace eq chk x vo v)) m

let ex_add = ns_add ls_equal
let mt_add = ns_add mt_equal

let add_ex chk x ls ns = { ns with ns_ex = ex_add chk x ls ns.ns_ex }
let add_ns chk x nn ns = { ns with ns_ns = nm_add chk x nn ns.ns_ns }

let rec ns_find get_map ns = function
  | []   -> assert false
  | [a]  -> Mstr.find a (get_map ns)
  | a::l -> ns_find get_map (Mstr.find a ns.ns_ns) l

let ns_find_ex = ns_find (fun ns -> ns.ns_ex)
let ns_find_ns = ns_find (fun ns -> ns.ns_ns)

(* modules under construction *)

type uc = {
  uc_name   : Ident.ident;
  uc_impure : theory_uc; (* the theory used for program types *)
  uc_effect : theory_uc; (* the theory used for typing effects *)
  uc_pure   : theory_uc; (* the logic theory used to type annotations *)
  uc_decls  : decl list; (* the program declarations *)
  uc_import : namespace list;
  uc_export : namespace list;
}

let namespace uc = List.hd uc.uc_import
let impure_uc uc = uc.uc_impure
let effect_uc uc = uc.uc_effect
let pure_uc   uc = uc.uc_pure

let add_pervasives uc =
  (* type unit = () *)
  let ts =
    Ty.create_tysymbol
      (id_fresh "unit") [] (Some (Ty.ty_app (Ty.ts_tuple 0) []))
  in
  add_ty_decl uc [ts, Decl.Tabstract]

let open_namespace uc = match uc.uc_import with
  | ns :: _ -> { uc with
      uc_impure = Theory.open_namespace uc.uc_impure;
      uc_effect = Theory.open_namespace uc.uc_effect;
      uc_pure   = Theory.open_namespace uc.uc_pure;
      uc_import =       ns :: uc.uc_import;
      uc_export = empty_ns :: uc.uc_export; }
  | [] -> assert false

exception NoOpenedNamespace

let close_namespace uc import s =
  match uc.uc_import, uc.uc_export with
  | _ :: i1 :: sti, e0 :: e1 :: ste ->
      let i1 = if import then merge_ns false e0 i1 else i1 in
      let _  = if import then merge_ns true  e0 e1 else e1 in
      let i1 = match s with Some s -> add_ns false s e0 i1 | _ -> i1 in
      let e1 = match s with Some s -> add_ns true  s e0 e1 | _ -> e1 in
      let ith = Theory.close_namespace uc.uc_impure import s in
      let eth = Theory.close_namespace uc.uc_effect import s in
      let pth = Theory.close_namespace uc.uc_pure   import s in
      { uc with uc_impure = ith; uc_effect = eth; uc_pure = pth;
                uc_import = i1 :: sti; uc_export = e1 :: ste; }
  | [_], [_] -> raise NoOpenedNamespace
  | _ -> assert false

(** Insertion of new declarations *)

let add_symbol add id v uc =
  match uc.uc_import, uc.uc_export with
  | i0 :: sti, e0 :: ste -> { uc with
      uc_import = add false id.id_string v i0 :: sti;
      uc_export = add true  id.id_string v e0 :: ste }
  | _ -> assert false

let add_esymbol ls uc =
  add_symbol add_ex ls.ls_name ls uc

let add_decl d uc =
  { uc with uc_decls = d :: uc.uc_decls }

let add_impure_decl d uc =
  let th = Theory.add_decl_with_tuples uc.uc_impure d in
  { uc with uc_impure = th }

let add_effect_decl d uc =
  let th = Theory.add_decl_with_tuples uc.uc_effect d in
  { uc with uc_effect = th }

let add_pure_decl d uc =
  let th = Theory.add_decl_with_tuples uc.uc_pure d in
  { uc with uc_pure = th }

(**
let add_psymbol ps uc =
  let uc = add_impure_decl (Decl.create_logic_decl [ps.ps_impure, None]) uc in
  let uc = add_effect_decl (Decl.create_logic_decl [ps.ps_effect, None]) uc in
  let uc = add_pure_decl   (Decl.create_logic_decl [ps.ps_pure,   None]) uc in
  uc
**)

let ls_Exit = create_lsymbol (id_fresh "%Exit") [] (Some ty_exn)

(* type unit = () *)
let ty_unit = ty_tuple []
let ts_unit = create_tysymbol (id_fresh "unit") [] (Some ty_unit)

(* logic ignore 'a : () *)

let ts_mark = create_tysymbol (id_fresh "'mark") [] None
let ty_mark = ty_app ts_mark []

let fs_at =
  let ty = ty_var (create_tvsymbol (id_fresh "a")) in
  create_lsymbol (id_fresh "at") [ty; ty_mark] (Some ty)

let fs_old =
  let ty = ty_var (create_tvsymbol (id_fresh "a")) in
  create_lsymbol (id_fresh "old") [ty] (Some ty)

let vs_old = create_vsymbol (id_fresh "'old") ty_mark
let vs_now = create_vsymbol (id_fresh "'now") ty_mark

let th_prelude =
  let uc = create_theory (id_fresh "Prelude") in
  let uc = use_export uc (tuple_theory 0) in
  let uc = add_ty_decl uc [ts_unit, Tabstract] in
  let uc = add_ty_decl uc [ts_mark, Tabstract] in
  let uc = add_logic_decl uc [fs_at, None] in
  let uc = add_logic_decl uc [fs_old, None] in
  close_theory uc

let empty_module path n =
  let m = {
    uc_name   = id_register n;
    uc_impure = Theory.create_theory ~path n;
    uc_effect = Theory.create_theory ~path n;
    uc_pure   = Theory.create_theory ~path n;
    uc_decls  = [];
    uc_import = [empty_ns];
    uc_export = [empty_ns]; }
  in
  (* pervasives *)
  let m = add_esymbol  ls_Exit    m in
  (***
  let m = add_mtsymbol mt_ghost   m in
  let m = add_psymbol  ps_ghost   m in
  let m = add_psymbol  ps_unghost m in
  ***)
  m

(** Modules *)

type t = {
  m_name   : Ident.ident;
  m_impure : theory;
  m_effect : theory;
  m_pure   : theory;
  m_decls  : decl list;
  m_export : namespace;
}

exception CloseModule

let close_module uc = match uc.uc_export with
  | [e] ->
      { m_name = uc.uc_name;
        m_decls = List.rev uc.uc_decls;
        m_export = e;
        m_impure = close_theory uc.uc_impure;
        m_effect = close_theory uc.uc_effect;
        m_pure = close_theory uc.uc_pure;
      }
  | _ ->
      raise CloseModule

(** Use *)

let use_export uc m =
  match uc.uc_import, uc.uc_export with
  | i0 :: sti, e0 :: ste -> { uc with
      uc_import = merge_ns false m.m_export i0 :: sti;
      uc_export = merge_ns true  m.m_export e0 :: ste;
      uc_impure = Theory.use_export uc.uc_impure m.m_impure;
      uc_effect = Theory.use_export uc.uc_effect m.m_effect;
      uc_pure   = Theory.use_export uc.uc_pure   m.m_pure; }
  | _ -> assert false

let use_export_theory uc th =
  let uc =
    { uc with
        uc_impure = Theory.use_export uc.uc_impure th;
        uc_effect = Theory.use_export uc.uc_effect th;
        uc_pure   = Theory.use_export uc.uc_pure   th; }
  in
  (* all type symbols from th are added as (pure) mtsymbols *)
  let add_ts _ ts =
    ignore
      (create_mtsymbol ~impure:ts ~effect:ts ~pure:ts ~singleton:false)
  in
  let rec add_ns ns uc =
    Mstr.iter add_ts ns.Theory.ns_ts;
    Mstr.fold (fun _ -> add_ns) ns.Theory.ns_ns uc
  in
  add_ns th.th_export uc

let create_module ?(path=[]) id =
  let uc = empty_module path id in
  use_export_theory uc th_prelude

let add_impure_pdecl env ltm d uc =
  { uc with uc_impure = Typing.add_decl env ltm uc.uc_impure d }

let add_effect_pdecl env ltm d uc =
  { uc with uc_effect = Typing.add_decl env ltm uc.uc_effect d; }

let add_pure_pdecl env ltm d uc =
  { uc with uc_pure = Typing.add_decl env ltm uc.uc_pure d; }

let add_pdecl env ltm d uc =
  { uc with
      uc_impure = Typing.add_decl env ltm uc.uc_impure d;
      uc_effect = Typing.add_decl env ltm uc.uc_effect d;
      uc_pure   = Typing.add_decl env ltm uc.uc_pure   d; }


(*
Local Variables:
compile-command: "unset LANG; make -C ../.. testl"
End:
*)
