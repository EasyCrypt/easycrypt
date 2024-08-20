(* -------------------------------------------------------------------- *)
open EcAst
open EcPath

(* -------------------------------------------------------------------- *)
include module type of struct include EcCoreModules end

(* -------------------------------------------------------------------- *)
(* Instantiation of EcCoreModules.PreOI on EcCoreFol.form. *)
module OI : sig
  type t = PreOI.t

  val hash : t -> int

  val equal : t -> t -> bool

  val allowed : t -> xpath list

  val allowed_s : t -> Sx.t

  val mk : xpath list -> t

  val filter : (xpath -> bool) -> t -> t
end

(* -------------------------------------------------------------------- *)
(* Careful, the available oracles are empty in both                     *)
(* [mr_empty] and [mr_full].                                            *)

val mr_empty : mod_restr

val mr_full  : mod_restr

val mr_add_restr :
  mod_restr -> mod_restr -> mod_restr

val change_oicalls : oracle_infos -> string -> xpath list -> oracle_infos

val oicalls_filter : oracle_infos -> string -> (xpath -> bool) -> oracle_infos
