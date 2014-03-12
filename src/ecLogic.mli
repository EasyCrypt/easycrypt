(* -------------------------------------------------------------------- *)
val cannot_apply : string -> string -> 'a
val tacerror     : ?catchable:bool -> EcBaseLogic.tac_error -> 'a
val tacuerror    : ?catchable:bool -> ('a, Format.formatter, unit, 'b) format4 -> 'a

val set_loc  : EcLocation.t -> ('a -> 'b) -> 'a -> 'b
val set_oloc : EcLocation.t option -> ('a -> 'b) -> 'a -> 'b

(* -------------------------------------------------------------------- *)
val destruct_product : EcEnv.LDecl.hyps -> EcFol.form ->
  [ `Forall of EcIdent.t * EcFol.gty * EcFol.form
  | `Imp of EcFol.form * EcFol.form
  ]  option
