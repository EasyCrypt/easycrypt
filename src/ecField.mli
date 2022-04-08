(* -------------------------------------------------------------------- *)
open EcRing
open EcBigInt

(* -------------------------------------------------------------------- *)
type fexpr =
| FEc   of c
| FEX   of int
| FEadd of fexpr * fexpr
| FEsub of fexpr * fexpr
| FEmul of fexpr * fexpr
| FEopp of fexpr
| FEinv of fexpr
| FEdiv of fexpr * fexpr
| FEpow of fexpr * zint

type linear = (pexpr * pexpr * (pexpr list))

(* -------------------------------------------------------------------- *)
val fnorm : fexpr -> linear
