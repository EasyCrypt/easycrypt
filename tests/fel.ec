require import AllCore List Distr DBool.

(* -------------------------------------------------------------------- *)
module type Oracle = {
  proc o() : unit
}.

module type Adv (O : Oracle) = {
  proc a() : unit
}.

module O = {
  var bad : bool
  var c   : int

  proc o() : unit = {
    var b;
    b <$ {0,1};
    c <- c + 1;
    if (b) bad <- true;
  }
}.

module G (A : Adv) = {
  proc main() : unit = {
    O.bad <- false;
    O.c   <- 0;
    A(O).a();
  }
}.

op q : { int | 0 <= q } as ge0_q.

(* -------------------------------------------------------------------- *)
(* [fel] needs the [FelTactic] theory.                                  *)
lemma fel_not_loaded (A <: Adv {-O}) &m :
  Pr[G(A).main() @ &m : O.bad /\ O.c <= q] <= q%r * (1%r / 2%r).
proof.
fail fel 2 O.c (fun _ => 1%r / 2%r) q O.bad [].
abort.

require import FelTactic StdBigop.
import Bigreal.

(* -------------------------------------------------------------------- *)
(* [fel] with an abstract adversary, no precondition, no invariant.     *)
lemma fel_basic (A <: Adv {-O}) &m :
  Pr[G(A).main() @ &m : O.bad /\ O.c <= q] <= q%r * (1%r / 2%r).
proof.
fel 2 O.c (fun _ => 1%r / 2%r) q O.bad [] => //.
+ by rewrite BRA.sumr_const RField.intmulr count_predT size_range; smt(ge0_q).
+ by auto.
+ proc; wp; rnd (pred1 true); auto=> />.
  + by move=> &hr *; rewrite dbool1E.
  by smt().
by move=> c; proc; auto; smt().
qed.

(* -------------------------------------------------------------------- *)
(* [fel] with oracle preconditions and an invariant, on a concrete      *)
(* program: [H.o] is reached through [H.w] (which writes nothing of     *)
(* the counter, event and invariant itself), [H.reset] writes the       *)
(* invariant. The initialization ends before [i <- 0].                  *)
module H = {
  var bad : bool
  var c   : int
  var k   : int

  proc o() : unit = {
    var b;
    if (c < q) {
      b <$ {0,1};
      c <- c + 1;
      if (b) bad <- true;
    }
  }

  proc reset() : unit = {
    k <- 0;
  }

  proc w() : unit = {
    o();
  }

  proc main() : unit = {
    var i;
    bad <- false;
    c   <- 0;
    k   <- 0;
    i   <- 0;
    while (i < 10) {
      w();
      reset();
      i <- i + 1;
    }
  }
}.

lemma fel_specs_inv &m :
  Pr[H.main() @ &m : H.bad] <= q%r * (1%r / 2%r).
proof.
fel 3 H.c (fun _ => 1%r / 2%r) q H.bad
  [H.o : (H.c < q); H.reset : false] (H.k = 0 /\ H.c <= q) => //.
+ by rewrite BRA.sumr_const RField.intmulr count_predT size_range; smt(ge0_q).
+ by auto=> />; smt(ge0_q).
+ proc; rcondt 1=> //; wp; rnd (pred1 true); auto=> />.
  + by move=> &hr *; rewrite dbool1E.
  by smt().
+ by move=> c; proc; rcondt 1=> //; auto=> /#.
+ by move=> b c; proc; rcondf 1=> //; auto.
+ by exfalso=> /#.
by move=> b c; proc; auto.
qed.

(* -------------------------------------------------------------------- *)
(* Error paths.                                                         *)
module G' (A : Adv) = {
  proc main() : unit = {
    O.bad <- false;
    O.c   <- 0;
    A(O).a();
    O.bad <- false;
  }
}.

lemma fel_errors (A <: Adv {-O}) &m :
  Pr[G(A).main() @ &m : O.bad /\ O.c <= q] = 0%r.
proof.
(* not a [Pr[_] <= _] goal *)
fail fel 2 O.c (fun _ => 1%r / 2%r) q O.bad [].
abort.

lemma fel_errors_abs (A <: Adv {-O}) &m :
  Pr[A(O).a() @ &m : O.bad] <= 1%r.
proof.
(* abstract procedure *)
fail fel 1 O.c (fun _ => 1%r / 2%r) q O.bad [].
abort.

lemma fel_errors_pos (A <: Adv {-O}) &m :
  Pr[G(A).main() @ &m : O.bad /\ O.c <= q] <= q%r * (1%r / 2%r).
proof.
(* invalid initialization position *)
fail fel 7 O.c (fun _ => 1%r / 2%r) q O.bad [].
abort.

lemma fel_errors_written (A <: Adv {-O}) &m :
  Pr[G'(A).main() @ &m : O.bad /\ O.c <= q] <= q%r * (1%r / 2%r).
proof.
(* the event is written outside of the oracles *)
fail fel 2 O.c (fun _ => 1%r / 2%r) q O.bad [].
(* the invariant is written outside of the oracles *)
fail fel 2 O.c (fun _ => 1%r / 2%r) q (O.c < 0) [] (!O.bad).
abort.
