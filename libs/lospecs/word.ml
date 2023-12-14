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
module type Size = sig
  val nbits : int
end

(* -------------------------------------------------------------------- *)
module SWord(I : Size) : S = struct
  type t = int

  let () = assert (I.nbits < Sys.int_size)

  let nbits = I.nbits

  let of_int (x : int) : t =
    x lsl (Sys.int_size - nbits)

  let to_int (x : t) : int =
    x asr (Sys.int_size - nbits)

  let mask : int =
    (1 lsl nbits) - 1

  let zero : t =
    of_int 0

  let one : t =
    of_int 1

  let add (x : t) (y : t) =
    x + y

  let sub (x : t) (y : t) =
    x - y

  let neg (x : t) : t =
    -x

  let mul (x : t) (y : t) : t =
    (to_int x) * y

  let logand (x : t) (y : t) : t =
    x land y

  let logor (x : t) (y : t) : t =
    x lor y

  let logxor (x : t) (y : t) : t =
    (x lxor y) land (of_int mask)

  let lognot (x : t) : t =
    logxor x (of_int (-1))

  let shiftl (x : t) (y : int) : t =
    x lsl y

  let shiftr (x : t) (y : t) : t =
    (x asr y) land (of_int mask)

  let abs (x : t) : t =
    abs x
end

(* -------------------------------------------------------------------- *)
module UWord(I : Size) : S = struct
  type t = int

  let () = assert (I.nbits < Sys.int_size)

  let nbits = I.nbits

  let mask : int =
    (1 lsl nbits) - 1

  let of_int (x : int) : t =
    x land mask

  let to_int (x : t) : int =
    x

  let zero : t =
    of_int 0

  let one : t =
    of_int 1

  let add (x : t) (y : t) =
    of_int (x + y)

  let sub (x : t) (y : t) =
    of_int (x - y)

  let mul (x : t) (y : t) =
    of_int (x * y)

  let neg (x : t) : t =
    of_int (-x)

  let logand (x : t) (y : t) : t =
    x land y

  let logor (x : t) (y : t) : t =
    x lor y

  let logxor (x : t) (y : t) =
    x lxor y

  let lognot (x : t) : t =
    x lxor mask

  let shiftl (x : t) (y : int) =
    of_int (x lsl y)

  let shiftr (x : t) (y : int) =
    x lsr y

  let abs (x : t) : t =
    x
end

(* -------------------------------------------------------------------- *)
let sword ~(size : int) : (module S) =
  (module SWord(struct let nbits = size end))

(* -------------------------------------------------------------------- *)
let uword ~(size : int) : (module S) =
  (module UWord(struct let nbits = size end))
