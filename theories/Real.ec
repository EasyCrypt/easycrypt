(* --------------------------------------------------------------------
 * Copyright (c) - 2012-2015 - IMDEA Software Institute and INRIA
 * Distributed under the terms of the CeCILL-B licence.
 * -------------------------------------------------------------------- *)

require Int.

(*
  import why3 "real" "Real"
  op "prefix -" as "[-]".
*)
(** Begin Import **)
  op zero : real.
  
  op one : real.
  
  op (<) : real -> real -> bool.
  
  op (>) (x y:real) = y < x.
  
  op (<=) (x y:real) = x < y \/ x = y.
  
  op (+) : real -> real -> real.
  
  op [-] : real -> real.
  
  op ( * ) : real -> real -> real.
  
  theory CommutativeGroup.
    axiom Assoc: forall (x y z : real), x + y + z = x + (y + z).
    
    axiom Unit_def_l: forall (x : real), zero + x = x.
    
    axiom Unit_def_r: forall (x : real), x + zero = x.
    
    axiom Inv_def_l: forall (x : real), -x + x = zero.
    
    axiom Inv_def_r: forall (x : real), x + -x = zero.
    
    theory Comm.
      axiom Comm: forall (x y : real), x + y = y + x.
    end Comm.
  end CommutativeGroup.
  
  theory Assoc.
    axiom Assoc: forall (x y z : real), x * y * z = x * (y * z).
  end Assoc.
  
  axiom Mul_distr_l: forall (x y z : real), x * (y + z) = x * y + x * z.
  
  axiom Mul_distr_r: forall (x y z : real), (y + z) * x = y * x + z * x.
  
  op (-) (x y:real) = x + (-y).
  
  theory Comm.
    axiom Comm: forall (x y : real), x * y = y * x.
  end Comm.
  
  axiom Unitary: forall (x : real), one * x = x.
  
  axiom NonTrivialRing: zero <> one.
  
  op inv : real -> real.
  
  axiom Inverse: forall (x : real), x <> zero => x * inv x = one.
  
  op (/) : real -> real -> real.
  
  axiom add_div:
    forall (x y z : real), z <> zero => (x + y) / z = x / z + y / z.
  
  axiom sub_div:
    forall (x y z : real), z <> zero => (x - y) / z = x / z - y / z.
  
  axiom neg_div: forall (x y : real), y <> zero => -x / y = -(x / y).
  
  axiom assoc_mul_div:
    forall (x y z : real), z <> zero => x * y / z = x * (y / z).
  
  axiom assoc_div_mul:
    forall (x y z : real),
      y <> zero /\ z <> zero => x / y / z = x / (y * z).
  
  axiom assoc_div_div:
    forall (x y z : real),
      y <> zero /\ z <> zero => x / (y / z) = x * z / y.
  
  op (>=) : real -> real -> bool.
  
  axiom Refl: forall (x : real), x <= x.
  
  axiom Trans: forall (x y z : real), x <= y => y <= z => x <= z.
  
  axiom Antisymm: forall (x y : real), x <= y => y <= x => x = y.
  
  axiom Total: forall (x y : real), x <= y \/ y <= x.
  
  axiom ZeroLessOne: zero <= one.
  
  axiom CompatOrderAdd: forall (x y z : real), x <= y => x + z <= y + z.
  
  axiom CompatOrderMult:
    forall (x y z : real), x <= y => zero <= z => x * z <= y * z.
(** End Import **)

theory Abs.

(*
  import why3 "real" "Abs"
    op "abs" as "`|_|".
*)
  (* unset triangular_inequality *)
(** Begin Import **)
    op "`|_|" (x:real) = if x >= zero then x else -x.
    
    axiom Abs_le: forall (x y : real), `|x| <= y <=> -y <= x /\ x <= y.
    
    axiom Abs_pos: forall (x:real), `|x| >= zero.
    
    axiom Abs_sum: forall (x y : real), `|x + y| <= `|x| + `|y|.
    
    axiom Abs_prod: forall (x y : real), `|x * y| = `|x| * `|y|.
    
    axiom triangular_inequality:
      forall (x y z : real), `|x - z| <= `|x - y| + `|y - z|.
(** End Import **)

end Abs.
export Abs.

theory Triangle.

  lemma triangular_inequality (x y z:real):
     `| x-y | <= `| x-z |  + `| y-z |
  by smt full.

end Triangle.

theory FromInt.
  require import Int.

(*
  import why3 "real" "FromInt".
*)
(** Begin Import **)
  op from_int: int -> real.

  axiom Zero: from_int (Int.zero) = zero.
  axiom One: from_int (Int.one) = one.

  axiom Add:
    forall (x y:int), from_int (Int.(+) x y) = from_int x + from_int y.
  axiom Sub:
    forall (x y:int), from_int (Int.(-) x y) = from_int x - from_int y.
  axiom Mul:
    forall (x y:int), from_int (Int.( * ) x y) = from_int x * from_int y.
  axiom Neg:
    forall (x:int), from_int (Int.([-]) x) = - from_int x.
(** End Import **)
  lemma from_intM (a b:int):
    (from_int a < from_int b) <=> (a < b)%Int.
  proof. by split; smt full. qed.

  lemma from_intMle : forall (a b : int), from_int a <= from_int b <=> a <= b
  by smt full.

end FromInt.
export FromInt.

theory PowerInt.
(*
  import why3 "real" "PowerInt"
     op "power" as "^".
*)
(** Begin Import **)
    op (^) : real -> int -> real.
    
    axiom Power_0: forall (x:real), x ^ (Int.zero) = one.
    
    axiom Power_s: forall (x:real) (n:int), Int.(>=) n Int.zero => x ^ (Int.(+) n Int.one) = x * x ^ n.
    
    axiom Power_s_alt: forall (x:real) (n:int), Int.(>) n Int.zero => x ^ n = x * x ^ (Int.(-) n Int.one).
    
    axiom Power_1: forall (x:real), x ^ Int.one = x.
    
    axiom Power_sum: forall (x:real) (n m:int), Int.(<=) Int.zero n => Int.(<=) Int.zero m => x ^ (Int.(+) n m) = x^n * x^m.
    
    axiom Power_mult: forall (x:real) (n m:int), Int.(<=) Int.zero n => Int.(<=) Int.zero m => x ^ (Int.( * ) n m) = (x ^ n) ^ m.
    
    axiom Power_mult2: forall (x y:real) (n:int), Int.(<=) Int.zero n => (x * y) ^ n = x ^ n * y ^ n.
    
    axiom Pow_ge_one: forall (x:real) (n:int), Int.(<=) Int.zero n /\ one <= x => one <= x ^ n.
(** End Import **)

  axiom pow_inv_pos :
    forall (x : real) (n : int), Int.(<=) 0 n => x ^ (Int.([-]) n) = inv (x ^ n).

  axiom pow_div_den (a b:int):
    Int.(<=) a b =>
    from_int (Int.(^) 2 a) / from_int (Int.(^) 2 b)
    = from_int 1 / from_int (Int.(^) 2 (Int.(-) b a)).
end PowerInt.
export PowerInt.

theory Square.
(*
  import why3 "real" "Square"
    op "sqrt" as "sqrt".
*)
(** Begin Import **)
    op sqr : real -> real.
    
    op sqrt : real -> real.
    
    axiom Sqrt_positive: forall (x:real), x >= zero => sqrt x >= zero.
    
    axiom Sqrt_square: forall (x:real), x >= zero => sqr (sqrt x) = x.
    
    axiom Square_sqrt: forall (x:real), x >= zero => sqrt (x * x) = x.
    
    axiom Sqrt_mul: forall (x y:real), x >= zero /\ y >= zero => sqrt (x * y) = sqrt x * sqrt y.
    
    axiom Sqrt_le: forall (x y:real), zero <= x <= y => sqrt x <= sqrt y.
(** End Import **)
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
by smt.

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
by smt.

lemma nosmt addgeM : forall (x1 x2 y1 y2:real),
   x1 >= x2 => y1 >= y2 => x1 + y1 >= x2 + y2 
by smt full.

lemma real_abs_sum : forall (a b c:real),
 a = b + c => `|a| <= `|b| + `|c|
by smt.

lemma real_le_trans: forall (a b c:real), 
 a <= b => b <= c => a <= c
by smt.

lemma nosmt le_ge : forall (x y:real), (x <= y) <=> (y >= x)
by smt full.

lemma nosmt le_ge_sym : forall (x y:real), (x <= y) => (y >= x).
proof. by move=> x y; rewrite le_ge. qed.

lemma nosmt eq_le_ge : forall (x y:real), (x = y) <=> (x <= y /\ x >= y)
by smt full.

lemma nosmt eq_le: forall (x y:real), x = y => x <= y
by smt.

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
(*
  import why3 "real" "ExpLog"
    op "exp" as "exp".
*)
(** Begin Import **)
    op exp : real -> real.
    
    axiom Exp_zero: exp zero = one.
    
    axiom Exp_sum: forall (x y : real), exp (x + y) = exp x * exp y.
    
    op e : real.
    
    op log : real -> real.
    
    axiom Log_one: log one = zero.
    
    axiom Log_mul: forall (x y:real), x > zero /\ y > zero => log (x * y) = log x + log y.
    
    axiom Log_exp: forall (x : real), log (exp x) = x.
    
    axiom Exp_log: forall (x:real), x > zero => exp (log x) = x.
    
    op log2 : real -> real.
    
    op log10 : real -> real.
(** End Import **)
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

  proof oner_neq0 by smt
  proof addr0     by smt
  proof addrA     by smt
  proof addrC     by smt
  proof addrN     by smt
  proof mulr1     by smt
  proof mulrA     by smt
  proof mulrC     by smt
  proof mulrDl    by smt
  proof expr0     by smt full
  proof exprS     by smt full
  proof subrE     by smt full
  proof ofint0    by smt
  proof ofint1    by smt
  proof ofintS    by smt full
  proof ofintN    by smt.

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

  proof oner_neq0 by smt
  proof addr0     by smt
  proof addrA     by smt
  proof addrC     by smt
  proof addrN     by smt
  proof mulr1     by smt
  proof mulrA     by smt
  proof mulrC     by smt
  proof mulrDl    by smt
  proof mulrV     by smt
  proof expr0     by smt full
  proof exprS     by smt full
  proof exprN     by smt
  proof subrE     by smt full
  proof divrE     by smt full
  proof ofint0    by smt
  proof ofint1    by smt
  proof ofintS    by smt full
  proof ofintN    by smt.

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
  ((ev1 /\ !bad1) <=> (ev2 /\ !bad2)) by smt.

lemma nosmt upto2_imp_bad (ev1 ev2 bad1 bad2:bool) :
  ((bad1 <=> bad2) /\ (!bad2 => (ev1 <=> ev2))) =>
  (ev1 /\ bad1) => bad2 by smt.

lemma nosmt upto_bad_false (ev bad2:bool) :
  !((ev /\ !bad2) /\ bad2) by smt.

lemma nosmt upto_bad_or (ev1 ev2 bad2:bool) :
   (!bad2 => ev1 => ev2) => ev1 =>
    ev2 /\ !bad2 \/ bad2 by smt.

lemma nosmt upto_bad_sub (ev bad:bool) :
  ev /\ ! bad => ev by [].
