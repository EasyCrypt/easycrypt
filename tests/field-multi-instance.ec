(* Selecting a named `field` structure when a carrier has several instances.
   Mirrors ring-multi-instance.ec for the `field` tactic: two field structures
   are registered on `real', each named at declaration and picked with
   `field [<name>]'. *)
require import Real.

(* ------------------------------------------------------------------ *)
(* Structure A, registered under the name `A'. *)
op zeroA : real = 0%r.
op oneA  : real = 1%r.
op addA (x y : real) : real = x + y.
op oppA (x : real)   : real = -x.
op mulA (x y : real) : real = x * y.
op invA (x : real)   : real = inv x.
op exprA (x : real) (n : int) : real = RField.exp x n.
op ofintA (n : int) : real = n%r.

instance field [A] with real
  op rzero = zeroA op rone = oneA op add = addA op opp = oppA
  op mul = mulA op expr = exprA op ofint = ofintA op inv = invA

  proof oner_neq0 by smt() proof addr0 by smt() proof addrA by smt()
  proof addrC by smt() proof addrN by smt() proof mulr1 by smt()
  proof mulrA by smt() proof mulrC by smt() proof mulrDl by smt()
  proof mulrV by smt()
  proof expr0 by smt(RField.expr0 RField.exprS RField.exprN)
  proof exprS by smt(RField.expr0 RField.exprS RField.exprN)
  proof exprN by smt(RField.expr0 RField.exprS RField.exprN)
  proof ofint0 by smt() proof ofint1 by smt()
  proof ofintS by smt() proof ofintN by smt().

(* ------------------------------------------------------------------ *)
(* Structure B, registered under the name `B'. *)
op zeroB : real = 0%r.
op oneB  : real = 1%r.
op addB (x y : real) : real = x + y.
op oppB (x : real)   : real = -x.
op mulB (x y : real) : real = x * y.
op invB (x : real)   : real = inv x.
op exprB (x : real) (n : int) : real = RField.exp x n.
op ofintB (n : int) : real = n%r.

instance field [B] with real
  op rzero = zeroB op rone = oneB op add = addB op opp = oppB
  op mul = mulB op expr = exprB op ofint = ofintB op inv = invB

  proof oner_neq0 by smt() proof addr0 by smt() proof addrA by smt()
  proof addrC by smt() proof addrN by smt() proof mulr1 by smt()
  proof mulrA by smt() proof mulrC by smt() proof mulrDl by smt()
  proof mulrV by smt()
  proof expr0 by smt(RField.expr0 RField.exprS RField.exprN)
  proof exprS by smt(RField.expr0 RField.exprS RField.exprN)
  proof exprN by smt(RField.expr0 RField.exprS RField.exprN)
  proof ofint0 by smt() proof ofint1 by smt()
  proof ofintS by smt() proof ofintN by smt().

(* Each selector routes to its own structure. The trailing `smt()' discharges
   the `x <> 0' side condition that `field' emits for the inverse. *)
lemma fA (x : real) :
  x <> zeroA => mulA (addA x oneA) (invA x) = addA oneA (invA x).
proof. move=> h; field [A]; smt(). qed.

lemma fB (x : real) :
  x <> zeroB => mulB (addB x oneB) (invB x) = addB oneB (invB x).
proof. move=> h; field [B]; smt(). qed.
