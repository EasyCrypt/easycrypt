(* -------------------------------------------------------------------- *)
module type S = sig
  type t

  val nbits : int

  val zero : t
  val one  : t

  val neg  : t -> t
  val add  : t -> t -> t
  val sub  : t -> t -> t
  val mul  : t -> t -> t

  val lognot : t -> t
  val logand : t -> t -> t
  val logor  : t -> t -> t
  val logxor : t -> t -> t

  val shiftl : t -> int -> t
  val shiftr : t -> int -> t

  val abs : t -> t

  val of_int : int -> t
  val to_int : t -> int
end

(* -------------------------------------------------------------------- *)
val sword : size:int -> (module S)
val uword : size:int -> (module S)

(* -------------------------------------------------------------------- *)
val word : sign:[`U | `S] -> size:int -> (module S)
