(* --------------------------------------------------------------------
 * Copyright (c) - 2012-2015 - IMDEA Software Institute and INRIA
 * Distributed under the terms of the CeCILL-B licence.
 * -------------------------------------------------------------------- *)

require Int.

import why3 "real" "Real"
  op "prefix -" as "[-]".

theory Abs.

  import why3 "real" "Abs"
    op "abs" as "`|_|".
  (* unset triangular_inequality *)

end Abs.
export Abs.

theory Triangle.

  lemma triangular_inequality (x y z:real):
     `| x-y | <= `| x-z |  + `| y-z |
  by smt full.

end Triangle.

theory FromInt.
  require import Int.
  import why3 "real" "FromInt".
  lemma from_intM (a b:int):
    (from_int a < from_int b) <=> (a < b)%Int
  by (split; smt full).

  lemma from_intMle : forall (a b : int), from_int a <= from_int b <=> a <= b
  by smt full.

end FromInt.
export FromInt.

theory PowerInt.
  import why3 "real" "PowerInt"
     op "power" as "^".

  axiom pow_inv_pos :
    forall (x : real) (n : int), Int.(<=) 0 n => x ^ (Int.([-]) n) = inv (x ^ n).

  axiom pow_div_den (a b:int):
    Int.(<=) a b =>
    from_int (Int.(^) 2 a) / from_int (Int.(^) 2 b)
    = from_int 1 / from_int (Int.(^) 2 (Int.(-) b a)).
end PowerInt.
export PowerInt.

theory Square.
  import why3 "real" "Square"
    op "sqrt" as "sqrt".
end Square.
export Square.

lemma nosmt inv_def (x:real):
  inv x = from_int 1 / x
by smt full.

lemma nosmt sign_inv (x:real):
  from_int 0 < x =>
  from_int 0 < inv x
by smt full.

lemma real_lt_trans (a b c:real):
 a < b => b <= c => a < c
by smt full.

lemma div_def (x y:real):
  y <> from_int 0 =>
  x / y = x * (from_int 1 / y)
by smt full.

lemma mul_div (x:real):
  x <> from_int 0 => x / x = from_int 1
by smt full.

lemma mulrMle (x y z:real):
  from_int 0 <= z =>
  x <= y =>
  x * z <= y * z
by smt full.

lemma mulrM (x y z:real):
  from_int 0 < z =>
  x < y =>
  x * z < y * z
by smt full.

lemma mul_compat_le (z x y:real):
  from_int 0 < z =>
  (x * z <= y * z <=> x <= y)
by smt full.

lemma nosmt addleM : forall (x1 x2 y1 y2:real),
   x1 <= x2 => y1 <= y2 => x1 + y1 <= x2 + y2 
by smt full.

lemma nosmt addgeM : forall (x1 x2 y1 y2:real),
   x1 >= x2 => y1 >= y2 => x1 + y1 >= x2 + y2 
by smt full.

lemma real_abs_sum : forall (a b c:real),
 a = b + c => `|a| <= `|b| + `|c|
by smt.

lemma real_le_trans: forall (a b c:real), 
 a <= b => b <= c => a <= c
by smt full.

lemma nosmt le_ge : forall (x y:real), (x <= y) <=> (y >= x)
by smt full.

lemma nosmt le_ge_sym : forall (x y:real), (x <= y) => (y >= x)
by (intros x y;rewrite le_ge).

lemma nosmt eq_le_ge : forall (x y:real), (x = y) <=> (x <= y /\ x >= y)
by smt full.

lemma nosmt eq_le: forall (x y:real), x = y => x <= y
by smt full.

lemma nosmt inv_le (x y:real): from_int 0 < x => from_int 0 < y => y <= x => inv x <= inv y.
proof.
  move=> _ _ _.
  rewrite -(mul_compat_le x); first trivial.
  rewrite -(mul_compat_le y); first trivial.
  cut H: ((x * inv x) * y <= (y * inv y) * x); last smt.
  rewrite (Inverse y _); first smt.
  by rewrite (Inverse x _); smt.
qed.

theory Exp.
  import why3 "real" "ExpLog"
    op "exp" as "exp".
  axiom exp_zero : exp (from_int 0) = from_int 1.
  axiom exp_monotonous : forall (x y:real) , x<=y => exp x <= exp y.

end Exp.
export Exp.

require import Ring.
require import AlgTactic.

instance ring with real
  op rzero = zero
  op rone  = one
  op add   = (+)
  op opp   = [-]
  op mul   = ( * )
  op expr  = PowerInt.( ^ )
  op sub   = (-)
  op ofint = FromInt.from_int

  proof oner_neq0 by smt full
  proof addr0     by smt full
  proof addrA     by smt full
  proof addrC     by smt full
  proof addrN     by smt full
  proof mulr1     by smt full
  proof mulrA     by smt full
  proof mulrC     by smt full
  proof mulrDl    by smt full
  proof expr0     by smt full
  proof exprS     by smt full
  proof subrE     by smt full
  proof ofint0    by smt full
  proof ofint1    by smt full
  proof ofintS    by smt full
  proof ofintN    by smt full.

instance field with real
  op rzero = zero
  op rone  = one
  op add   = (+)
  op opp   = [-]
  op mul   = ( * )
  op expr  = PowerInt.( ^ )
  op sub   = (-)
  op ofint = FromInt.from_int
  op inv   = inv
  op div   = (/)

  proof oner_neq0 by smt full
  proof addr0     by smt full
  proof addrA     by smt full
  proof addrC     by smt full
  proof addrN     by smt full
  proof mulr1     by smt full
  proof mulrA     by smt full
  proof mulrC     by smt full
  proof mulrDl    by smt full
  proof mulrV     by smt full
  proof expr0     by smt full
  proof exprS     by smt full
  proof exprN     by smt full
  proof subrE     by smt full
  proof divrE     by smt full
  proof ofint0    by smt full
  proof ofint1    by smt full
  proof ofintS    by smt full
  proof ofintN    by smt full.

(* WARNING Lemmas used by tactics : 
   eq_le addleM real_le_trans and the following lemmas *)
lemma nosmt upto2_abs (x1 x2 x3 x4 x5:real):
   FromInt.from_int 0 <= x1 => 
   FromInt.from_int 0 <= x3 => 
   x1 <= x5 => 
   x3 <= x5 => 
   x2 = x4 =>
   `|x1 + x2 - (x3 + x4)| <= x5 by smt full.

lemma nosmt upto2_notbad (ev1 ev2 bad1 bad2:bool) :
  ((bad1 <=> bad2) /\ (!bad2 => (ev1 <=> ev2))) =>
  ((ev1 /\ !bad1) <=> (ev2 /\ !bad2)) by smt full.

lemma nosmt upto2_imp_bad (ev1 ev2 bad1 bad2:bool) :
  ((bad1 <=> bad2) /\ (!bad2 => (ev1 <=> ev2))) =>
  (ev1 /\ bad1) => bad2 by smt full.

lemma nosmt upto_bad_false (ev bad2:bool) :
  !((ev /\ !bad2) /\ bad2) by smt full.

lemma nosmt upto_bad_or (ev1 ev2 bad2:bool) :
   (!bad2 => ev1 => ev2) => ev1 =>
    ev2 /\ !bad2 \/ bad2 by smt full.

lemma nosmt upto_bad_sub (ev bad:bool) :
  ev /\ ! bad => ev by [].
