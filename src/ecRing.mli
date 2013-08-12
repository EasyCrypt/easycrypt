(* -------------------------------------------------------------------- *)
type c = Big_int.big_int

val ceq : c -> c -> bool

val c0 : c
val c1 : c

val cadd : c -> c -> c
val csub : c -> c -> c
val cmul : c -> c -> c
val copp : c -> c
val cdiv : c -> c -> c * c

(* -------------------------------------------------------------------- *)
type pexpr =
| PEc   of c 
| PEX   of int
| PEadd of pexpr * pexpr 
| PEsub of pexpr * pexpr
| PEmul of pexpr * pexpr
| PEopp of pexpr 
| PEpow of pexpr * int

type pol =
| Pc of c 
| Pinj of int * pol
| PX of pol * int * pol

val pexpr_eq : pexpr -> pexpr -> bool
val peq : pol -> pol -> bool

(* -------------------------------------------------------------------- *)
val norm : pexpr -> (pexpr * pexpr) list -> pol
