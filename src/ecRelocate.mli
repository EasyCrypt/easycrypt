(* -------------------------------------------------------------------- *)
val sourceroot : string option

(* -------------------------------------------------------------------- *)
module type Sites = sig
  val commands : string
  val theories : string list
  val doc      : string
  val config   : string
end

(* -------------------------------------------------------------------- *)
val sites : (module Sites)
