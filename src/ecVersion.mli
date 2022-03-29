(* -------------------------------------------------------------------- *)
val copyright : string list
val url       : string
val hash      : string
val app       : string

module License : sig
  val engine : string
  val stdlib : string
end
