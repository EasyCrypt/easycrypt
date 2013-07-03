
require import FSet.
require import Int.


(***** doesn't work yet *)
(* require Monoid. *)
(* clone Monoid as MInt with  *)
(*   type t = int, *)
(*   op (+) = Int.(+), *)
(*   op Z = 0. *)


(* temporary workaround *)
op intval : int -> int -> int set.

axiom intval_def : forall i i1 i2, 
  mem i (intval i1 i2)  <=> (i1<= i /\ i <= i2).

axiom intval_card_0 : 
  forall i1 (i2 : int), i1 <= i2 => 
  card (intval i1 i2) = i2 - i1 + 1.

axiom intval_card_1 : 
  forall i1 (i2:int), i2 < i1 => card (intval i1 i2) = 0.


op int_sum : (int -> 'a) -> int set -> 'a.

pred is_cnst (f : int -> 'a) = forall i1 i2, f i1 = f i2.

require import Real.

axiom int_sum_const :
  forall (f : int -> real) (s: int set),
    int_sum f s = (card s)%r * f 0.




