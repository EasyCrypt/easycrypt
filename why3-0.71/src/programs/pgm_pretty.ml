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
open Pp
open Ident
open Term
open Pretty
open Pgm_types.T
open Pgm_ttree

let debug_print_labels = Debug.register_flag "print_labels"
let debug_print_locs = Debug.register_flag "print_locs"

(* pretty-printing (for debugging) *)

let rec print_expr fmt e = match e.expr_desc with
  | Elogic t ->
      fprintf fmt "@[<hov 2><term %a : %a>@]" Pretty.print_term t
        Pretty.print_ty (t_type t)
  | Elocal v ->
      fprintf fmt "%a" print_pv v
  | Eglobal { ps_kind = PSvar v } ->
      fprintf fmt "<global var %a>" print_pv v
  | Eglobal { ps_kind = PSfun tv } ->
      fprintf fmt "<global %a>" print_type_v tv
  | Eglobal { ps_kind = PSlogic } ->
      assert false
  | Efun (bl, t) ->
      fprintf fmt "@[<hov 2>fun %a ->@ %a@]"
        (print_list space print_pv) bl print_triple t
  | Elet (v, e1, e2) ->
      fprintf fmt "@[<hv 0>@[<hov 2>let %a/%a =@ %a in@]@ %a@]"
        print_vs v.pv_effect print_vs v.pv_pure
        print_lexpr e1 print_lexpr e2

  | Eif (e1, e2, e3) ->
      fprintf fmt "@[if %a@ then@ %a else@ %a@]"
        print_lexpr e1 print_lexpr e2 print_lexpr e3

  | Eany c ->
      fprintf fmt "@[[any %a]@]" print_type_c c

  | Emark (_, _)  ->
      fprintf fmt "<todo: Emark>"
  | Eassert (_, f) ->
      fprintf fmt "@[assert {%a}@]" print_term f
  | Efor (_, _, _, _, _, e) ->
      fprintf fmt "@[<hov 2>for ... do@ %a@ done@]" print_lexpr e
  | Etry (_, _) ->
      fprintf fmt "<todo: Etry>"
  | Eraise (_, _)  ->
      fprintf fmt "<todo: Eraise>"
  | Ematch (v, cl) ->
      fprintf fmt "@[<hov 2>match %a with@ %a@]" print_pv v
        (print_list newline print_branch) cl
  | Eloop (_, _) ->
      fprintf fmt "<todo: Eloop>"
  | Eletrec (_, _)  ->
      fprintf fmt "<todo: Eletrec>"
  | Eabsurd ->
      fprintf fmt "absurd"

and print_lexpr fmt e =
  let print_elab fmt e =
    if Debug.test_flag debug_print_labels && e.expr_lab <> []
    then fprintf fmt "@[<hov 0>%a@ %a@]"
      (print_list space print_label) e.expr_lab print_expr e
    else print_expr fmt e in
  let print_eloc fmt e =
    if Debug.test_flag debug_print_locs
    then fprintf fmt "@[<hov 0>%a@ %a@]"
      print_loc e.expr_loc print_elab e
    else print_elab fmt e in
  print_eloc fmt e

and print_pv fmt v =
  fprintf fmt "<@[%a@]>" print_vsty v.pv_effect

and print_triple fmt (p, e, q) =
  fprintf fmt "@[<hv 0>%a@ %a@ %a@]" print_pre p print_expr e print_post q

and print_recfun fmt (v, bl, t, _) =
  fprintf fmt "@[<hov 2>rec %a@ %a =@ %a@]"
    print_pv v (print_list space print_pv) bl print_triple t

and print_branch fmt (p, e) =
  fprintf fmt "@[<hov 4>| %a ->@ %a@]" print_pattern p print_expr e

and print_pattern fmt p =
  Pretty.print_pat fmt p.ppat_pat

