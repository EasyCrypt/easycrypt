(* --------------------------------------------------------------------
 * Copyright (c) - 2012-2015 - IMDEA Software Institute and INRIA
 * Distributed under the terms of the CeCILL-C license
 * -------------------------------------------------------------------- *)

type zint = Z.t

exception Overflow

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
let lgnot = (Z.lognot : zint -> zint)

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

let of_string = (Z.of_string : string -> zint)
let to_string = (Z.to_string : zint -> string)
let pp_print  = (Z.pp_print : Format.formatter -> zint -> unit)
