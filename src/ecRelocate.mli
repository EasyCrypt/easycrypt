(* -------------------------------------------------------------------- *)
val sourceroot : string option

(* -------------------------------------------------------------------- *)
module type Sites = sig
  val commands : string
  val theories : string list
  val doc      : string
end

(* -------------------------------------------------------------------- *)
val sites : (module Sites)
