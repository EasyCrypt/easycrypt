(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2016 - Inria
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcBigInt
open EcMaps

(* -------------------------------------------------------------------- *)
type pexpr =
| PEc   of zint
| PEX   of int
| PEadd of pexpr * pexpr
| PEsub of pexpr * pexpr
| PEmul of pexpr * pexpr
| PEopp of pexpr
| PEpow of pexpr * zint

val pexpr_eq : pexpr -> pexpr -> bool

val pp_pe : Format.formatter -> pexpr -> unit
val fv_pe : pexpr -> Sint.t

(* -------------------------------------------------------------------- *)
type 'a cmp_sub = [`Eq | `Lt | `Gt of 'a]

(* -------------------------------------------------------------------- *)
exception Overflow

(* -------------------------------------------------------------------- *)
module type Coef = sig
  (* ------------------------------------------------------------------ *)
  type c

  val cofint : zint -> c
  val ctoint : c -> zint

  val c0   : c
  val c1   : c
  val cadd : c -> c -> c
  val csub : c -> c -> c
  val cmul : c -> c -> c
  val copp : c -> c
  val ceq  : c -> c -> bool
  val cdiv : c -> c -> c * c

  (* ------------------------------------------------------------------ *)
  type p

  val pofint : zint -> p
  val ptoint : p -> zint

  val padd : p -> p -> p
  val peq  : p -> p -> bool
  val pcmp : p -> p -> int

  val pcmp_sub : p -> p -> p cmp_sub
end

(* -------------------------------------------------------------------- *)
module Cint  : Coef
module Cbool : Coef

module type ModVal = sig
  val c : zint option
  val p : zint option
end

module Cmod(M : ModVal) : Coef

(* -------------------------------------------------------------------- *)
module type Rnorm = sig
  module C : Coef

  val norm_pe : pexpr -> (pexpr * pexpr) list -> pexpr

end

module Iring : Rnorm
module Bring : Rnorm

module Make(C : Coef) : Rnorm

(* -------------------------------------------------------------------- *)
type c = zint

val c0   : c
val c1   : c
val cadd : c -> c -> c
val csub : c -> c -> c
val cmul : c -> c -> c
val copp : c -> c
val ceq  : c -> c -> bool
val cdiv : c -> c -> c*c

