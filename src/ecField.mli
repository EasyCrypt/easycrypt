(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2017 - Inria
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

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
