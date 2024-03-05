(* -------------------------------------------------------------------- *)
val sourceroot : string option

(* -------------------------------------------------------------------- *)
module type Sites = sig
  val commands : string
  val theories : string list
end

(* -------------------------------------------------------------------- *)
val sites : (module Sites)
