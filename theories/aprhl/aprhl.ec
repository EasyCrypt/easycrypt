(* -------------------------------------------------------------------- *)
require export Distr NewDistr Int IntExtra Real RealExtra RealExp List.
require import StdBigop.
(*---*) export StdBigop.Bigreal.BRA.

(* -------------------------------------------------------------------- *)
op lap : real -> int -> int distr.

axiom lap_ll e x : is_lossless (lap e x).

(* -------------------------------------------------------------------- *)
op sumr (n : int) (f : int -> real) =
  Bigreal.BRA.bigi predT f 0 n.
