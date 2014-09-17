(* --------------------------------------------------------------------
 * Copyright (c) - 2012-2014 - IMDEA Software Institute and INRIA
 * Distributed under the terms of the CeCILL-C license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcMaps
open Big_int

(* -------------------------------------------------------------------- *)
type pexpr =
| PEc   of big_int 
| PEX   of int
| PEadd of pexpr * pexpr 
| PEsub of pexpr * pexpr
| PEmul of pexpr * pexpr
| PEopp of pexpr 
| PEpow of pexpr * int

val pexpr_eq : pexpr -> pexpr -> bool

val pp_pe : Format.formatter -> pexpr -> unit
val fv_pe : pexpr -> Sint.t 

(* -------------------------------------------------------------------- *)
type 'a cmp_sub = [`Eq | `Lt | `Gt of 'a]

(* -------------------------------------------------------------------- *)
module type Coef = sig
  (* ------------------------------------------------------------------ *)
  type c 

  val cofint : big_int -> c
  val ctoint : c -> big_int

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

  val pofint : int -> p
  val ptoint : p -> int 

  val padd : p -> p -> p
  val peq  : p -> p -> bool
  val pcmp : p -> p -> int 

  val pcmp_sub : p -> p -> p cmp_sub
end

(* -------------------------------------------------------------------- *)
module Cint  : Coef
module Cbool : Coef

module type ModVal = sig
  val c : int option
  val p : int option
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
type c = big_int

val c0   : c
val c1   : c
val cadd : c -> c -> c
val csub : c -> c -> c
val cmul : c -> c -> c
val copp : c -> c 
val ceq  : c -> c -> bool
val cdiv : c -> c -> c*c

