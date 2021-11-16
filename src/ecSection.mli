(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcModules
open EcEnv
open EcTheory

(* -------------------------------------------------------------------- *)
exception SectionError of string

(* -------------------------------------------------------------------- *)
type sc_item =
  | SC_th_item  of theory_item
  | SC_decl_mod of EcIdent.t * module_type * mod_restr

(* -------------------------------------------------------------------- *)
type scenv

val env : scenv -> env

val initial : env -> scenv

val add_item     : theory_item -> scenv -> scenv
val add_decl_mod : EcIdent.t -> module_type -> mod_restr -> scenv -> scenv

val enter_section : EcSymbols.symbol option -> scenv -> scenv
val exit_section  : EcSymbols.symbol option -> scenv -> scenv

type checked_ctheory = private ctheory

val enter_theory : EcSymbols.symbol -> EcTypes.is_local -> thmode -> scenv -> scenv
val exit_theory  :
  ?clears:EcPath.path list ->
  ?pempty:[ `ClearOnly | `Full | `No ] ->
  scenv -> EcSymbols.symbol * checked_ctheory option * scenv

val import : EcPath.path -> scenv -> scenv

val import_vars : EcPath.mpath -> scenv -> scenv

val add_th  : import:import -> EcSymbols.symbol -> checked_ctheory -> scenv -> scenv
val require : EcSymbols.symbol -> checked_ctheory -> scenv -> scenv

val astop : scenv -> scenv
