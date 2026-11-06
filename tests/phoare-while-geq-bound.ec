(* pHL `while I v k eps` with a lower bound or an equality (#1127): the
   rule is an induction on the iterations of the loop starting from the
   probability 1, so it must require `bd <= 1%r` in every memory
   satisfying the pre-condition. Requiring it only when the loop is not
   entered is not enough: a bound that doubles on every iteration that
   does not exit satisfies all the other goals. *)
require import AllCore Distr DBool.

module M = { proc f() : unit = { while (false) {} } }.

(* The loop is never entered: every goal but the exit one is vacuous. *)
lemma bad : phoare[M.f : true ==> true] >= 2%r.
proof.
proc.
while (true) 0 0 1%r.
+ done.
+ done.
+ done.
+ by move=> _; exfalso.
+ by exfalso.
+ split; first done.
  by move=> z; exfalso.
(* remaining goal: forall &hr, true => 2%r <= 1%r *)
move=> &hr _.
fail (by smt()).
abort.

(* A bound at most 1 needs no extra step. *)
lemma ok : phoare[M.f : true ==> true] >= 1%r.
proof.
proc.
while (true) 0 0 1%r.
+ done.
+ done.
+ done.
+ by move=> _; exfalso.
+ by exfalso.
+ split; first done.
  by move=> z; exfalso.
qed.

lemma ok' : phoare[M.f : true ==> true] = 1%r.
proof.
proc.
while (true) 0 0 1%r.
+ done.
+ done.
+ done.
+ by move=> _; exfalso.
+ by exfalso.
+ split; first done.
  by move=> z; exfalso.
qed.

(* Each iteration exits with probability 1/2; otherwise it increments
   `W.i`. The bound `2 ^ W.i + 1` is the expectation of the bound after
   one iteration (1 on exit), so the inductive goal holds, and the bound
   is 1 when the loop is not entered: without the new goal, `W.f` (which
   terminates with probability 1) would succeed with probability at
   least 2 when `W.b` holds. *)
module W = {
  var b : bool
  var i : int

  proc f() = {
    var c;
    while (W.b) {
      c <$ {0,1};
      if (c) { W.b <- false; } else { W.i <- W.i + 1; }
    }
  }
}.

lemma bad_ge : phoare[W.f : 0 <= W.i ==> true] >=
  (if W.b then (2 ^ W.i)%r + 1%r else 1%r).
proof.
proc.
while (0 <= W.i) (b2i W.b) 1 (1%r / 2%r).
+ by move=> &hr.
+ by move=> &hr.
+ by move=> &hr; smt().
+ move=> ih.
  seq 1 : c (1%r/2%r) 1%r (1%r/2%r) ((2 ^ (W.i + 1))%r + 1%r)
          (W.b /\ 0 <= W.i).
  + by auto.
  + by rnd (pred1 true); auto => />; smt(dbool1E).
  + rcondt 1; 1: by auto.
    by sp; conseq ih => /> /#.
  + by rnd (pred1 false); auto => />; smt(dbool1E).
  + rcondf 1; 1: by auto.
    exists* W.i; elim* => i0.
    conseq (: W.b /\ 0 <= W.i /\ W.i = i0 ==> true
            : >= ((2 ^ (i0 + 1))%r + 1%r)); 1,2: smt(StdOrder.IntOrder.expr_ge0).
    by sp; conseq ih; smt(StdOrder.IntOrder.expr_ge0).
  by move=> &hr [h0 ->] /=; rewrite exprS //; smt().
+ by auto=> /> &hr *; smt(dbool_ll).
+ split; first smt().
  by move=> z; wp; rnd (pred1 true); auto => /> &hr *; smt(dbool1E).
(* remaining goal: forall &hr, 0 <= W.i => bd <= 1%r *)
move=> &hr _.
fail (by smt()).
abort.

(* The same bound, with `=`. *)
lemma bad_eq : phoare[W.f : 0 <= W.i ==> true] =
  (if W.b then (2 ^ W.i)%r + 1%r else 1%r).
proof.
proc.
while (0 <= W.i) (b2i W.b) 1 (1%r / 2%r).
+ by move=> &hr.
+ by move=> &hr b i _ ->.
+ by move=> &hr; smt().
+ move=> ih.
  seq 1 : c (1%r/2%r) 1%r (1%r/2%r) ((2 ^ (W.i + 1))%r + 1%r)
          (W.b /\ 0 <= W.i).
  + by auto.
  + by rnd (pred1 true); auto => />; smt(dbool1E).
  + rcondt 1; 1: by auto.
    by sp; conseq ih => /> /#.
  + by rnd (pred1 false); auto => />; smt(dbool1E).
  + rcondf 1; 1: by auto.
    exists* W.i; elim* => i0.
    conseq (: W.b /\ 0 <= W.i /\ W.i = i0 ==> true
            : = ((2 ^ (i0 + 1))%r + 1%r)); 1,2: smt(StdOrder.IntOrder.expr_ge0).
    by sp; conseq ih; smt(StdOrder.IntOrder.expr_ge0).
  by move=> &hr [h0 ->] /=; rewrite exprS //; smt().
+ by auto=> /> &hr *; smt(dbool_ll).
+ split; first smt().
  by move=> z; wp; rnd (pred1 true); auto => /> &hr *; smt(dbool1E).
(* remaining goal: forall &hr, 0 <= W.i => bd <= 1%r *)
move=> &hr _.
fail (by smt()).
abort.
