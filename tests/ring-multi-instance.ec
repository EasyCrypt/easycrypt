(* Selecting a named `ring` structure when a carrier has several instances.
   Two ring structures are registered on `int`; each is given a name at
   declaration, and the `ring` tactic is directed at one of them with
   `ring [<name>]`. Bare `ring` keeps resolving the sole/first instance. *)
require import Int.
require (*--*) Ring.

(* ------------------------------------------------------------------ *)
(* Structure A, registered under the name `A'.                        *)
op zeroA : int = 0.
op oneA  : int = 1.
op addA (x y : int) : int = x + y.
op oppA (x : int)   : int = -x.
op mulA (x y : int) : int = x * y.
op exprA (x : int) (n : int) : int = Ring.IntID.exp x n.

instance ring [A] with int
  op rzero = zeroA op rone = oneA op add = addA
  op opp = oppA op mul = mulA op expr = exprA

  proof oner_neq0 by smt() proof addr0 by smt() proof addrA by smt()
  proof addrC by smt() proof addrN by smt() proof mulr1 by smt()
  proof mulrA by smt() proof mulrC by smt() proof mulrDl by smt()
  proof expr0 by smt(Ring.IntID.expr0) proof exprS by smt(Ring.IntID.exprS).

(* Only one instance exists here, so bare `ring` resolves it (this is the
   backwards-compatible, single-structure case). *)
lemma bare (x y : int) : addA x (mulA y oneA) = addA (mulA oneA y) x.
proof. ring. qed.

lemma useA1 (x y : int) : addA x (mulA y oneA) = addA (mulA oneA y) x.
proof. ring [A]. qed.

(* ------------------------------------------------------------------ *)
(* Structure B, registered under the name `B'. Same underlying maths, but
   distinct operator paths, so it is a genuinely separate instance on the
   same carrier `int'. *)
op zeroB : int = 0.
op oneB  : int = 1.
op addB (x y : int) : int = x + y.
op oppB (x : int)   : int = -x.
op mulB (x y : int) : int = x * y.
op exprB (x : int) (n : int) : int = Ring.IntID.exp x n.

instance ring [B] with int
  op rzero = zeroB op rone = oneB op add = addB
  op opp = oppB op mul = mulB op expr = exprB

  proof oner_neq0 by smt() proof addr0 by smt() proof addrA by smt()
  proof addrC by smt() proof addrN by smt() proof mulr1 by smt()
  proof mulrA by smt() proof mulrC by smt() proof mulrDl by smt()
  proof expr0 by smt(Ring.IntID.expr0) proof exprS by smt(Ring.IntID.exprS).

(* Two instances are now registered on `int'. Each selector routes to its own
   structure: the operators of the other structure are opaque to it, so a goal
   phrased with A's operators is a ring identity only for structure A (and dually
   for B). These lemmas being accepted is exactly what shows the selector picks
   the intended structure rather than the first-registered one. *)
lemma useA2 (x y : int) : addA x (mulA y oneA) = addA (mulA oneA y) x.
proof. ring [A]. qed.

lemma useB (x y : int) : addB x (mulB y oneB) = addB (mulB oneB y) x.
proof. ring [B]. qed.
