(* -------------------------------------------------------------------- *)
op from_int: int -> real.
op zero = from_int 0.
op one  = from_int 1.
op add  : real -> real -> real.
op opp  : real -> real.
op mul  : real -> real -> real.
op inv  : real -> real.

op lt : real -> real -> bool.
op le = fun x y => lt x y \/ x = y.

(* -------------------------------------------------------------------- *)

