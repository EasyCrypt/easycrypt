(* -------------------------------------------------------------------- *)
require import Distr NewDistr Int Real StdBigop.

op lap : real -> int -> int distr.

axiom lap_ll e x : is_lossless (lap e x).

(* -------------------------------------------------------------------- *)
op sumr (n : int) (f : int -> real) =
  Bigreal.BRA.bigi predT f 0 n.
