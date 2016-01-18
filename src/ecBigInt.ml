(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2016 - Inria
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
module B = Big_int

(* -------------------------------------------------------------------- *)
module ZImpl : EcBigIntCore.TheInterface = struct
  type zint = Z.t

  exception Overflow
  exception InvalidString

  let compare = (Z.compare : zint -> zint -> int)
  let equal   = (Z.equal : zint -> zint -> bool)
  let sign    = (Z.sign : zint -> int)
  let hash    = (Z.hash : zint -> int)

  let le = (Z.leq : zint -> zint -> bool)
  let lt = (Z.lt  : zint -> zint -> bool)
  let ge = (Z.geq : zint -> zint -> bool)
  let gt = (Z.gt  : zint -> zint -> bool)

  let zero : zint = Z.zero
  let one  : zint = Z.one

  let add  = (Z.add      : zint -> zint -> zint)
  let neg  = (Z.neg      : zint -> zint)
  let sub  = (Z.sub      : zint -> zint -> zint)
  let mul  = (Z.mul      : zint -> zint -> zint)
  let div  = (Z.div      : zint -> zint -> zint)
  let ediv = (Z.ediv_rem : zint -> zint -> zint * zint)
  let erem = (Z.erem     : zint -> zint -> zint)
  let gcd  = (Z.gcd      : zint -> zint -> zint)
  let abs  = (Z.abs      : zint -> zint)
  let pow  = (Z.pow      : zint -> int -> zint)

  let pred = (Z.pred : zint -> zint)
  let succ = (Z.succ : zint -> zint)

  let parity (z : zint) =
    if Z.sign (Z.extract z 0 1) = 0 then `Even else `Odd

  let lshift = (Z.shift_left  : zint -> int -> zint)
  let rshift = (Z.shift_right : zint -> int -> zint)

  let lgand = (Z.logand : zint -> zint -> zint)
  let lgor  = (Z.logor  : zint -> zint -> zint)
  let lgxor = (Z.logxor : zint -> zint -> zint)

  module Notations = struct
    let ( =^ ) = equal
    let ( +^ ) = add
    let ( ~^ ) = neg
    let ( -^ ) = sub
    let ( *^ ) = mul
    let ( /^ ) = div

    let ( <=^ ) = le
    let ( <^  ) = lt
    let ( >=^ ) = ge
    let ( >^  ) = gt
  end

  let of_int = (Z.of_int : int -> zint)

  let to_int (x : zint) =
    try Z.to_int x with Z.Overflow -> raise Overflow

  let to_string = (Z.to_string : zint -> string)

  let of_string (x : string) =
    try  Z.of_string x
    with Failure _ -> raise InvalidString

  let pp_print  = (Z.pp_print : Format.formatter -> zint -> unit)
end

(* -------------------------------------------------------------------- *)
module BigNumImpl : EcBigIntCore.TheInterface = struct
  type zint = Big_int.big_int

  exception Overflow
  exception InvalidString

  let compare = (B.compare_big_int : zint -> zint -> int)
  let equal   = (B.eq_big_int      : zint -> zint -> bool)
  let sign    = (B.sign_big_int    : zint -> int)
  let hash    = (Hashtbl.hash      : zint -> int) (* fixed in OCaml 3.12 *)

  let le = (B.le_big_int : zint -> zint -> bool)
  let lt = (B.lt_big_int : zint -> zint -> bool)
  let ge = (B.eq_big_int : zint -> zint -> bool)
  let gt = (B.gt_big_int  : zint -> zint -> bool)

  let zero : zint = B.zero_big_int
  let one  : zint = B.unit_big_int

  let add  = (B.add_big_int    : zint -> zint -> zint)
  let neg  = (B.minus_big_int  : zint -> zint)
  let sub  = (B.sub_big_int    : zint -> zint -> zint)
  let mul  = (B.mult_big_int   : zint -> zint -> zint)
  let div  = (B.div_big_int    : zint -> zint -> zint)
  let abs  = (B.abs_big_int    : zint -> zint)
  let gcd  = (B.gcd_big_int    : zint -> zint -> zint)
  let erem = (B.mod_big_int    : zint -> zint -> zint)
  let ediv = (B.quomod_big_int : zint -> zint -> zint * zint)
  let pow  = (B.power_big_int_positive_int : zint -> int -> zint)

  let pred = (B.pred_big_int : zint -> zint)
  let succ = (B.succ_big_int : zint -> zint)

  let parity (z : zint) =
    if B.sign_big_int (B.extract_big_int z 0 1) = 0 then `Even else `Odd

  let lshift = (B.shift_left_big_int  : zint -> int -> zint)
  let rshift = (B.shift_right_big_int : zint -> int -> zint)

  let lgand = (B.and_big_int : zint -> zint -> zint)
  let lgor  = (B.or_big_int  : zint -> zint -> zint)
  let lgxor = (B.xor_big_int : zint -> zint -> zint)

  module Notations = struct
    let ( =^ ) = equal
    let ( +^ ) = add
    let ( ~^ ) = neg
    let ( -^ ) = sub
    let ( *^ ) = mul
    let ( /^ ) = div

    let ( <=^ ) = le
    let ( <^  ) = lt
    let ( >=^ ) = ge
    let ( >^  ) = gt
  end

  let of_int = (B.big_int_of_int : int -> zint)

  let to_int (x : zint) =
    try B.int_of_big_int x with Failure _ -> raise Overflow

  let to_string = (B.string_of_big_int : zint -> string)

  let of_string (x : string) : zint =
    try  B.big_int_of_string x
    with Failure _ -> raise InvalidString

  let pp_print fmt x =
    Format.fprintf fmt "%s" (B.string_of_big_int x)
end

(* -------------------------------------------------------------------- *)
include ZImpl
