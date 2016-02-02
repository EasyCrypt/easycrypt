(* -------------------------------------------------------------------- *)
require import Distr NewDistr Int Real.

op lap : real -> int -> int distr.

axiom lap_ll e x : is_lossless (lap e x).
