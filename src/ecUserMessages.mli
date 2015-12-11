(* -------------------------------------------------------------------- *)
open EcUtils
open EcTypes
open EcEnv

(* -------------------------------------------------------------------- *)
module TypingError : sig
  open EcTyping

  val pp_tyerror         : env -> Format.formatter -> tyerror -> unit
  val pp_cnv_failure     : env -> Format.formatter -> tymod_cnv_failure -> unit
  val pp_mismatch_funsig : env -> Format.formatter -> mismatch_funsig -> unit
  val pp_modappl_error   : env -> Format.formatter -> modapp_error -> unit
  val pp_restr_error     : env -> Format.formatter -> restriction_error -> unit
end

(* -------------------------------------------------------------------- *)
module InductiveError : sig
  open EcHiInductive

  val pp_rcerror : env -> Format.formatter -> rcerror -> unit
  val pp_dterror : env -> Format.formatter -> dterror -> unit
  val pp_fxerror : env -> Format.formatter -> fxerror -> unit
end

(* -------------------------------------------------------------------- *)
module PredError : sig
  open EcHiPredicates

  val pp_tperror : env -> Format.formatter -> tperror -> unit
end

(* -------------------------------------------------------------------- *)
module CloneError : sig
  open EcThCloning

  val string_of_ovkind : ovkind -> string
  val pp_clone_error : env -> Format.formatter -> clone_error -> unit
end

(* -------------------------------------------------------------------- *)
module PTermError : sig
  open EcProofTerm

  val string_of_argkind : argkind -> string
  val pp_pterm_apperror : Format.formatter -> pterror -> unit
end

(* -------------------------------------------------------------------- *)
module RedError : sig
  open EcFol

  val pp_incompatible_form : Format.formatter -> env -> form pair -> unit
  val pp_incompatible_type : Format.formatter -> env -> ty pair -> unit
end

(* -------------------------------------------------------------------- *)
val pp_parse_error : Format.formatter -> string option -> unit
val pp_alias_clash : env -> Format.formatter -> EcPV.alias_clash -> unit
val pp_tc_error    : Format.formatter -> EcCoreGoal.tcerror -> unit

(* -------------------------------------------------------------------- *)
val register : unit -> unit
