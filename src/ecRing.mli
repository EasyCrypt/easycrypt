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
val pp_pe  : Format.formatter -> pexpr -> unit

(* -------------------------------------------------------------------- *)

type 'a cmp_sub = 
  | Eq 
  | Lt of 'a
  | Gt of 'a

module type Coef = sig
  type c 
  val cofint : big_int -> c
  val ctoint : c -> big_int
  val c0 : c
  val c1 : c
  val cadd : c -> c -> c
  val csub : c -> c -> c
  val cmul : c -> c -> c
  val copp : c -> c 
  val ceq  : c -> c -> bool
  val cdiv : c -> c -> c*c

  type p 
  val pofint : int -> p
  val ptoint : p -> int 
  val padd : p -> p -> p
  val peq  : p -> p -> bool
  val pcmp : p -> p -> p cmp_sub

end

(* -------------------------------------------------------------------- *)
module type Rnorm = sig

  module C : Coef 
    
  type pol =
  | Pc of C.c 
  | Pinj of int * pol
  | PX of pol * C.p * pol

  val peq    : pol -> pol -> bool
  val norm   : pexpr -> (pexpr * pexpr) list -> pol
  val norm_pe: pexpr -> (pexpr * pexpr) list -> pexpr
  val pp_pol : Format.formatter -> pol -> unit

end

module Iring : Rnorm
module Bring : Rnorm

(* -------------------------------------------------------------------- *)

type c = big_int

val c0 : c
val c1 : c
val cadd : c -> c -> c
val csub : c -> c -> c
val cmul : c -> c -> c
val copp : c -> c 
val ceq  : c -> c -> bool
val cdiv : c -> c -> c*c

