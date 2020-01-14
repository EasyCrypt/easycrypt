(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcSymbols
open EcPath
open EcTypes
open EcCoreFol

(* -------------------------------------------------------------------- *)
include module type of struct include EcCoreModules end

(* -------------------------------------------------------------------- *)
(* Instantiation of EcCoreModules.PreOI on EcCoreFol.form. *)
module OI : sig
  type t = EcCoreFol.form PreOI.t

  val hash : t -> int
  val equal : t -> t -> bool

  val empty : t

  val is_in : t -> bool

  val cost : t -> xpath -> EcCoreFol.form option
  val cost_self : t -> EcCoreFol.form option

  val allowed : t -> xpath list
  val allowed_s : t -> Sx.t

  val mk :
    xpath list ->
    bool ->
    EcCoreFol.form Mx.t ->
    EcCoreFol.form option ->
    t

  val filter : (xpath -> bool) -> t -> t
end

(* -------------------------------------------------------------------- *)
type mod_restr         = form pre_mod_restr
type module_type       = form pre_module_type
type module_sig        = form pre_module_sig
type module_smpl_sig   = form pre_module_smpl_sig
type function_body     = form pre_function_body
type function_         = form pre_function_
type module_expr       = form pre_module_expr
type module_body       = form pre_module_body
type module_structure  = form pre_module_structure
type module_item       = form pre_module_item
type module_comps      = form pre_module_comps
type module_comps_item = form pre_module_comps_item

(* Careful, the avalaible oracle are empty in both [mr_empty] and [mr_full]. *)
val mr_empty : mod_restr
val mr_full  : mod_restr

val mr_hash  : mod_restr -> int
val mr_equal : mod_restr -> mod_restr -> bool

val mr_add_restr :
  mod_restr -> EcPath.Sx.t use_restr -> EcPath.Sm.t use_restr -> mod_restr

val add_oinfo : mod_restr -> string -> OI.t -> mod_restr
val change_oicalls : mod_restr -> string -> xpath list -> mod_restr
val oicalls_filter :
  mod_restr ->
  EcSymbols.Msym.key ->
  (EcPath.xpath -> bool) ->
  mod_restr

(* -------------------------------------------------------------------- *)
val sig_smpl_sig_coincide : module_sig -> module_smpl_sig -> bool

(* -------------------------------------------------------------------- *)
val mty_equal : module_type -> module_type -> bool
val mty_hash  : module_type -> int
