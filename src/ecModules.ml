(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcUtils
open EcSymbols
open EcTypes
open EcPath
open EcCoreFol

module Sid = EcIdent.Sid
module Mid = EcIdent.Mid

(* -------------------------------------------------------------------- *)
include EcCoreModules

(* -------------------------------------------------------------------- *)
(* Instantiation of EcCoreModules.PreOI on EcCoreFol.form. *)
module OI : sig
  type t = form PreOI.t

  val hash : t -> int
  val equal : t -> t -> bool

  val empty : t

  val is_in : t -> bool

  val cost : t -> xpath -> form option
  val cost_self : t -> form option
  val costs : t -> form Mx.t

  val allowed : t -> xpath list
  val allowed_s : t -> Sx.t

  val mk : xpath list -> bool -> form Mx.t -> form option -> t
  val change_calls : t -> xpath list -> t
  val filter : (xpath -> bool) -> t -> t
end = struct
  type t = EcCoreFol.form PreOI.t

  let empty        = PreOI.empty
  let is_in        = PreOI.is_in
  let allowed      = PreOI.allowed
  let allowed_s    = PreOI.allowed_s
  let cost         = PreOI.cost
  let costs        = PreOI.costs
  let cost_self    = PreOI.cost_self
  let mk           = PreOI.mk
  let change_calls = PreOI.change_calls
  let filter       = PreOI.filter
  let equal        = PreOI.equal EcCoreFol.f_equal
  let hash         = PreOI.hash EcCoreFol.f_hash
end

(* -------------------------------------------------------------------- *)
type module_type       = EcCoreFol.module_type
type mod_restr         = EcCoreFol.mod_restr
type module_sig        = form p_module_sig
type module_smpl_sig   = form p_module_smpl_sig
type function_body     = form p_function_body
type function_         = form p_function_
type module_expr       = form p_module_expr
type module_body       = form p_module_body
type module_structure  = form p_module_structure
type module_item       = form p_module_item
type module_comps      = form p_module_comps
type module_comps_item = form p_module_comps_item

let mr_empty = {
  mr_xpaths = ur_empty EcPath.Sx.empty;
  mr_mpaths = ur_empty EcPath.Sm.empty;
  mr_oinfos = Msym.empty;
}

let mr_full = {
  mr_xpaths = ur_full EcPath.Sx.empty;
  mr_mpaths = ur_full EcPath.Sm.empty;
  mr_oinfos = Msym.empty;
}


let mr_add_restr mr (rx : Sx.t use_restr) (rm : Sm.t use_restr) =
  { mr_xpaths = ur_union Sx.union Sx.inter mr.mr_xpaths rx;
    mr_mpaths = ur_union Sm.union Sm.inter mr.mr_mpaths rm;
    mr_oinfos = mr.mr_oinfos; }

let change_oinfo restr f oi =
  { restr with mr_oinfos = Msym.add f oi restr.mr_oinfos }

let add_oinfo restr f oi = change_oinfo restr f oi

let change_oicalls restr f ocalls =
  let oi = match Msym.find f restr.mr_oinfos with
    | oi -> OI.change_calls oi ocalls
    | exception Not_found -> OI.mk ocalls true Mx.empty None in
  add_oinfo restr f oi

let oicalls_filter restr f filter =
  match Msym.find f restr.mr_oinfos with
  | oi -> change_oinfo restr f (OI.filter filter oi)
  | exception Not_found -> restr

(* -------------------------------------------------------------------- *)
let mty_hash  = EcCoreFol.mty_hash
let mty_equal = EcCoreFol.mty_equal

let mr_equal  = EcCoreFol.mr_equal
let mr_hash   = EcCoreFol.mr_hash
