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
open Ident
open Denv
open Ty
open Pgm_types
open Pgm_types.T

type loc = Loc.position

type ident = Ptree.ident

type constant = Term.constant

type assertion_kind = Ptree.assertion_kind

type lazy_op = Ptree.lazy_op

type for_direction = Ptree.for_direction

(*****************************************************************************)
(* phase 1: introduction of destructive types *)

(* user type_v *)

type dpre = Ptree.pre
type dpost_fmla = Ptree.lexpr
type dexn_post_fmla = Ptree.lexpr
type dpost = dpost_fmla * (Term.lsymbol * dexn_post_fmla) list

type dueffect = {
  du_reads  : Ptree.lexpr list;
  du_writes : Ptree.lexpr list;
  du_raises : esymbol list;
}

type dutype_v =
  | DUTpure  of Denv.dty
  | DUTarrow of dubinder list * dutype_c

and dutype_c =
  { duc_result_type : dutype_v;
    duc_effect      : dueffect;
    duc_pre         : Ptree.lexpr;
    duc_post        : Ptree.lexpr * (Term.lsymbol * Ptree.lexpr) list; }

and dubinder = ident * Denv.dty * dutype_v

type dvariant = Ptree.lexpr * Term.lsymbol option

type dloop_annotation = {
  dloop_invariant : Ptree.lexpr option;
  dloop_variant   : dvariant option;
}

type dexpr = {
  dexpr_desc : dexpr_desc;
  dexpr_type : Denv.dty;
  dexpr_lab  : Ident.label list;
  dexpr_loc  : loc;
}

and dexpr_desc =
  | DEconstant of constant
  | DElocal of string * Denv.dty
  | DEglobal of psymbol * type_v * type_var Htv.t
  | DElogic of Term.lsymbol
  | DEapply of dexpr * dexpr
  | DEfun of dubinder list * dtriple
  | DElet of ident * dexpr * dexpr
  | DEletrec of drecfun list * dexpr
  | DEassign of dexpr * Term.lsymbol * int * dexpr

  | DEsequence of dexpr * dexpr
  | DEif of dexpr * dexpr * dexpr
  | DEloop of dloop_annotation * dexpr
  | DElazy of lazy_op * dexpr * dexpr
  | DEnot of dexpr
  | DEmatch of dexpr * (Denv.dpattern * dexpr) list
  | DEabsurd
  | DEraise of esymbol * dexpr option
  | DEtry of dexpr * (esymbol * string option * dexpr) list
  | DEfor of ident * dexpr * for_direction * dexpr * Ptree.lexpr option * dexpr

  | DEassert of assertion_kind * Ptree.lexpr
  | DEmark of string * dexpr
  | DEany of dutype_c

and drecfun = (ident * Denv.dty) * dubinder list * dvariant option * dtriple

and dtriple = dpre * dexpr * dpost

(*****************************************************************************)
(* phase 2: removal of destructive types *)

type variant_rel =
  | Vuser of Term.lsymbol
  | Vint  of Term.lsymbol (* <= *) * Term.lsymbol (* < *)

type variant = Term.term * variant_rel

type loop_annotation = {
  loop_invariant : Term.term option;
  loop_variant   : variant option;
}

type ipre = T.pre

type ipost = T.post

(* each program variable is materialized by two logic variables (vsymbol):
   one for typing programs and another for typing annotations *)
type ivsymbol = {
  i_impure : Term.vsymbol; (* in programs *)
  i_effect : Term.vsymbol; (* in effect *)
  i_pure   : Term.vsymbol; (* in annotations *)
}

type iregion = R.t

type ieffect = {
  ie_reads  : iregion list;
  ie_writes : iregion list;
  ie_raises : esymbol list;
}

type itype_v =
  | ITpure  of ty
  | ITarrow of ibinder list * itype_c

and itype_c =
  { ic_result_type : itype_v;
    ic_effect      : ieffect;
    ic_pre         : T.pre;
    ic_post        : T.post; }

and ibinder = ivsymbol * itype_v

type mark = Term.vsymbol

type irec_variant = ivsymbol * Term.term * variant_rel

(* FIXME: get rid of ipattern *)
type ipattern = {
  ipat_pat  : Term.pattern; (* program variables *)
  ipat_node : ipat_node;
}

and ipat_node =
  | IPwild
  | IPvar  of ivsymbol
  | IPapp  of Term.lsymbol * ipattern list
  | IPor   of ipattern * ipattern
  | IPas   of ipattern * ivsymbol

type iexpr = {
  iexpr_desc : iexpr_desc;
  iexpr_type : ty;
  iexpr_lab  : Ident.label list;
  iexpr_loc  : loc;
}

and iexpr_desc =
  | IElogic of Term.term (* pure *)
      * Term.Svs.t (* local impure variables *) * Spv.t (* globals *)
  | IElocal of ivsymbol
  | IEglobal of psymbol * type_v
  | IEapply of iexpr * ivsymbol
  | IEapply_var of iexpr * ivsymbol
  | IEapply_glob of iexpr * pvsymbol
  | IEfun of ibinder list * itriple
  | IElet of ivsymbol * iexpr * iexpr
  | IEletrec of irecfun list * iexpr

  | IEif of iexpr * iexpr * iexpr
  | IEloop of loop_annotation * iexpr
  | IElazy of lazy_op * iexpr * iexpr
  | IEnot of iexpr
  | IEmatch of ivsymbol * (ipattern * iexpr) list
  | IEabsurd
  | IEraise of esymbol * iexpr option
  | IEtry of iexpr * (esymbol * ivsymbol option * iexpr) list
  | IEfor of ivsymbol * ivsymbol * for_direction * ivsymbol *
             Term.term option * iexpr

  | IEassert of assertion_kind * Term.term
  | IEmark of mark * iexpr
  | IEany of itype_c

and irecfun = ivsymbol * ibinder list * irec_variant option * itriple

and itriple = ipre * iexpr * ipost


(*****************************************************************************)
(* phase 3: effect inference *)

type reference = R.t

type pre = T.pre

type post = T.post

type pattern = {
  ppat_pat  : Term.pattern; (* logic variables *)
  ppat_node : ppat_node;
}

and ppat_node =
  | Pwild
  | Pvar  of pvsymbol
  | Papp  of Term.lsymbol * pattern list
  | Por   of pattern * pattern
  | Pas   of pattern * pvsymbol

type expr = {
  expr_desc  : expr_desc;
  expr_type  : ty;
  expr_type_v: type_v;
  expr_effect: E.t;
  expr_lab   : Ident.label list;
  expr_loc   : loc;
}

and expr_desc =
  | Elogic of Term.term
  | Elocal of pvsymbol
  | Eglobal of psymbol
  | Efun of pvsymbol list * triple
  | Elet of pvsymbol * expr * expr
  | Eletrec of recfun list * expr

  | Eif of expr * expr * expr
  | Eloop of loop_annotation * expr
  | Ematch of pvsymbol * (pattern * expr) list
  | Eabsurd
  | Eraise of esymbol * expr option
  | Etry of expr * (esymbol * pvsymbol option * expr) list
  | Efor of pvsymbol * pvsymbol * for_direction * pvsymbol *
            Term.term option * expr

  | Eassert of assertion_kind * Term.term
  | Emark of mark * expr
  | Eany of type_c

and recfun = pvsymbol * pvsymbol list * triple * E.t

and triple = pre * expr * post

type decl =
  | Dlet    of T.psymbol * expr
  | Dletrec of (T.psymbol * recfun) list
  | Dparam  of T.psymbol

type file = decl list


(*
Local Variables:
compile-command: "unset LANG; make -C ../.. testl"
End:
*)
