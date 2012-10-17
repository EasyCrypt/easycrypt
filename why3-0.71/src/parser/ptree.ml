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

(*s Parse trees. *)

type loc = Loc.position

(*s Logical expressions (for both terms and predicates) *)

type integer_constant = Term.integer_constant
type real_constant = Term.real_constant
type constant = Term.constant

type label =
  | Lstr of Ident.label
  | Lpos of Loc.position

type pp_quant =
  | PPforall | PPexists | PPlambda | PPfunc | PPpred

type pp_binop =
  | PPand | PPor | PPimplies | PPiff

type pp_unop =
  | PPnot

type ident = { id : string; id_lab : label list; id_loc : loc }

type qualid =
  | Qident of ident
  | Qdot of qualid * ident

type pty =
  | PPTtyvar of ident
  | PPTtyapp of pty list * qualid
  | PPTtuple of pty list

type param = ident option * pty

type pattern =
  { pat_loc : loc; pat_desc : pat_desc }

and pat_desc =
  | PPpwild
  | PPpvar of ident
  | PPpapp of qualid * pattern list
  | PPprec of (qualid * pattern) list
  | PPptuple of pattern list
  | PPpor of pattern * pattern
  | PPpas of pattern * ident

type lexpr =
  { pp_loc : loc; pp_desc : pp_desc }

and pp_desc =
  | PPvar of qualid
  | PPapp of qualid * lexpr list
  | PPtrue
  | PPfalse
  | PPconst of constant
  | PPinfix of lexpr * ident * lexpr
  | PPbinop of lexpr * pp_binop * lexpr
  | PPunop of pp_unop * lexpr
  | PPif of lexpr * lexpr * lexpr
  | PPquant of pp_quant * param list * lexpr list list * lexpr
  | PPnamed of label * lexpr
  | PPlet of ident * lexpr * lexpr
  | PPeps of ident * pty * lexpr
  | PPmatch of lexpr * (pattern * lexpr) list
  | PPcast of lexpr * pty
  | PPtuple of lexpr list
  | PPrecord of (qualid * lexpr) list
  | PPupdate of lexpr * (qualid * lexpr) list

(*s Declarations. *)

type plogic_type =
  | PPredicate of pty list
  | PFunction  of pty list * pty

type imp_exp =
  | Import | Export | Nothing

type use = {
  use_theory  : qualid;
  use_as      : ident option option;
  use_imp_exp : imp_exp;
}

type clone_subst =
  | CSns    of qualid option * qualid option
  | CStsym  of qualid * qualid
  | CSfsym  of qualid * qualid
  | CSpsym  of qualid * qualid
  | CSlemma of qualid
  | CSgoal  of qualid

type is_mutable = bool

type type_def =
  | TDabstract
  | TDalias     of pty
  | TDalgebraic of (loc * ident * param list) list
  | TDrecord    of (loc * is_mutable * ident * pty) list

type type_decl = {
  td_loc    : loc;
  td_ident  : ident;
  td_params : ident list;
  td_model  : bool;
  td_def    : type_def;
}

type logic_decl = {
  ld_loc    : loc;
  ld_ident  : ident;
  ld_params : param list;
  ld_type   : pty option;
  ld_def    : lexpr option;
}

type ind_decl = {
  in_loc    : loc;
  in_ident  : ident;
  in_params : param list;
  in_def    : (loc * ident * lexpr) list;
}

type prop_kind =
  | Kaxiom | Klemma | Kgoal

type metarg =
  | PMAts  of qualid
  | PMAfs  of qualid
  | PMAps  of qualid
  | PMApr  of qualid
  | PMAstr of string
  | PMAint of int

type decl =
  | TypeDecl of type_decl list
  | LogicDecl of logic_decl list
  | IndDecl of ind_decl list
  | PropDecl of loc * prop_kind * ident * lexpr
  | UseClone of loc * use * clone_subst list option
  | Meta of loc * ident * metarg list


(* program files *)

type assertion_kind = Aassert | Aassume | Acheck

type lazy_op = LazyAnd | LazyOr

type variant = lexpr * qualid option

type loop_annotation = {
  loop_invariant : lexpr option;
  loop_variant   : variant option;
}

type for_direction = To | Downto

type effect = {
  pe_reads  : lexpr list;
  pe_writes : lexpr list;
  pe_raises : qualid list;
}

type pre = lexpr

type post = lexpr * (qualid * lexpr) list

type type_v =
  | Tpure of pty
  | Tarrow of binder list * type_c

and type_c =
  { pc_result_type : type_v;
    pc_effect      : effect;
    pc_pre         : pre;
    pc_post        : post; }

and binder = ident * type_v option

type expr = {
  expr_desc : expr_desc;
  expr_loc  : loc;
}

and expr_desc =
  (* lambda-calculus *)
  | Econstant of constant
  | Eident of qualid
  | Eapply of expr * expr
  | Efun of binder list * triple
  | Elet of ident * expr * expr
  | Eletrec of (ident * binder list * variant option * triple) list * expr
  | Etuple of expr list
  | Erecord of (qualid * expr) list
  | Eupdate of expr * (qualid * expr) list
  | Eassign of expr * qualid * expr
  (* control *)
  | Esequence of expr * expr
  | Eif of expr * expr * expr
  | Eloop of loop_annotation * expr
  | Elazy of lazy_op * expr * expr
  | Enot of expr
  | Ematch of expr * (pattern * expr) list
  | Eabsurd
  | Eraise of qualid * expr option
  | Etry of expr * (qualid * ident option * expr) list
  | Efor of ident * expr * for_direction * expr * lexpr option * expr
  (* annotations *)
  | Eassert of assertion_kind * lexpr
  | Emark of ident * expr
  | Ecast of expr * pty
  | Eany of type_c
  | Enamed of label * expr

  (* TODO: ghost *)

and triple = pre * expr * post

type program_decl =
  | Dlet    of ident * expr
  | Dletrec of (ident * binder list * variant option * triple) list
  | Dlogic  of decl
  | Dparam  of ident * type_v
  | Dexn    of ident * pty option
  (* modules *)
  | Duse    of qualid * imp_exp * (*as:*) ident option
  | Dnamespace of loc * ident option * (* import: *) bool * program_decl list

type theory = {
  pth_name   : ident;
  pth_decl   : program_decl list;
}

type module_ = {
  mod_name   : ident;
  mod_decl   : program_decl list;
}

type theory_module =
  | Ptheory of theory
  | Pmodule of module_

type program_file = theory_module list

