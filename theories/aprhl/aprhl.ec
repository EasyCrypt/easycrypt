(* -------------------------------------------------------------------- *)
require import Distr NewDistr Int.

op lap : int -> int distr.

axiom lap_ll x : is_lossless (lap x).

