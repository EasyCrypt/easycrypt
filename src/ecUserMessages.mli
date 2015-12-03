(* -------------------------------------------------------------------- *)
open EcEnv

(* -------------------------------------------------------------------- *)
module TypingError : sig
  open EcTyping

  val pp_tyerror         : env -> Format.formatter -> tyerror -> unit
  val pp_cnv_failure     : env -> Format.formatter -> tymod_cnv_failure -> unit
  val pp_mismatch_funsig : env -> Format.formatter -> mismatch_funsig -> unit
  val pp_modappl_error   : env -> Format.formatter -> modapp_error -> unit
end

(* -------------------------------------------------------------------- *)
val register : unit -> unit
