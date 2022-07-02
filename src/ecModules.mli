(* -------------------------------------------------------------------- *)
open EcPath
open EcCoreFol

(* -------------------------------------------------------------------- *)
include module type of struct include EcCoreModules end

(* -------------------------------------------------------------------- *)
(* Instantiation of EcCoreModules.PreOI on EcCoreFol.form. *)
module OI : sig
  type t = form PreOI.t

  val hash : t -> int
  val equal : t -> t -> bool

  val cost_self : t -> [`Bounded of form | `Unbounded]
  val cost : t -> xpath -> [`Bounded of form | `Zero | `Unbounded]
  val cost_calls : t -> [`Bounded of form Mx.t | `Unbounded]
  val costs : t -> [`Bounded of form * form Mx.t | `Unbounded]

  val allowed : t -> xpath list
  val allowed_s : t -> Sx.t

  val mk : xpath list -> [`Bounded of form * form Mx.t | `Unbounded] -> t
  (* val change_calls : t -> xpath list -> t *)
  val filter : (xpath -> bool) -> t -> t
end

(* -------------------------------------------------------------------- *)
type mod_restr         = form p_mod_restr
type module_type       = form p_module_type
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
type top_module_sig    = form p_top_module_sig
type top_module_expr   = form p_top_module_expr

(* Careful, the available oracles are empty in both [mr_empty] and [mr_full]. *)
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
val mty_equal : module_type -> module_type -> bool
val mty_hash  : module_type -> int
