(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2016 - Inria
 * 
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcSymbols
open EcIdent
open EcPath
open EcFol
open EcDecl
open EcModules

type locals

(* -------------------------------------------------------------------- *)
val env_of_locals   : locals -> EcEnv.env
val items_of_locals : locals -> EcTheory.ctheory_item list

val is_local : [`Lemma | `Module] -> path -> locals -> bool
val is_mp_local : mpath -> locals -> bool

val form_use_local : form  -> locals -> bool

val form_use_local_or_abs   : form        -> locals -> bool
val module_use_local_or_abs : module_expr -> locals -> bool
val opdecl_use_local_or_abs : operator    -> locals -> bool
val tydecl_use_local_or_abs : tydecl      -> locals -> bool

val abstracts : locals -> (EcIdent.t * (module_type * mod_restr)) list * Sid.t

val generalize : EcEnv.env -> locals -> form -> form

(* -------------------------------------------------------------------- *)
type t

exception NoSectionOpened

val initial : t

val in_section : t -> bool

val enter : EcEnv.env -> symbol option -> t -> t
val exit  : t -> locals * t

val path  : t -> symbol option * path
val opath : t -> (symbol option * path) option

val topenv  : t -> EcEnv.env

val locals  : t -> locals
val olocals : t -> locals option

type lvl = [`Local | `Global] * [`Axiom | `Lemma]

val add_local_mod : path -> t -> t
val add_lemma     : path -> lvl -> t -> t
val add_item      : EcTheory.ctheory_item -> t -> t
val add_abstract  : EcIdent.t -> (module_type * mod_restr) -> t -> t
