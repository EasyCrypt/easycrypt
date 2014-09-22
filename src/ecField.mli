(* --------------------------------------------------------------------
 * Copyright (c) - 2012-2014 - IMDEA Software Institute and INRIA
 * Distributed under the terms of the CeCILL-C license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcRing

(* -------------------------------------------------------------------- *)
type fexpr =
| FEc   of Big_int.big_int
| FEX   of int
| FEadd of fexpr * fexpr
| FEsub of fexpr * fexpr
| FEmul of fexpr * fexpr
| FEopp of fexpr
| FEinv of fexpr
| FEdiv of fexpr * fexpr
| FEpow of fexpr * int

type linear = (pexpr * pexpr * (pexpr list))

(* -------------------------------------------------------------------- *)
val fnorm : fexpr -> linear
