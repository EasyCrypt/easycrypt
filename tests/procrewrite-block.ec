(* Tests for `proc rewrite` over positions, ranges and whole statements:
   the rewrite recurses into the bodies of if/while/match and applies to
   every expression of the selected instructions. *)

require import AllCore Distr.

op foo : int -> int.
op bar : int -> int.

axiom fooE (x : int) : foo x = x + 1.
axiom barE (x : int) : bar x = x * 2.

hint simplify fooE, barE.

(* -------------------------------------------------------------------- *)
(* Whole body, `/=` mode: guards, right-hand sides, then- and
   else-branches, sampling and call arguments are all normalised. *)
theory BlockSimpl.
  module M = {
    proc h(y : int) : int = {
      return y;
    }

    proc f(a : int, b : int) : int = {
      var c, i, d : int;

      c <- foo a;
      i <- 0;
      while (i < bar b) {
        if (foo i = 0) {
          c <- c + foo i;
        } else {
          c <- c + bar i;
        }
        i <- i + 1;
      }
      d <$ dunit (foo c);
      c <@ h(bar d);
      return c;
    }

    proc g(a : int, b : int) : int = {
      var c, i, d : int;

      c <- a + 1;
      i <- 0;
      while (i < b * 2) {
        if (i + 1 = 0) {
          c <- c + (i + 1);
        } else {
          c <- c + i * 2;
        }
        i <- i + 1;
      }
      d <$ dunit (c + 1);
      c <@ h(d * 2);
      return c;
    }
  }.

  lemma L : equiv[M.f ~ M.g : ={arg} ==> ={res}].
  proof.
  proc.
  proc rewrite {1} /=.
  by sim.
  qed.

  (* No side, non-relational goal *)
  lemma L' : hoare[M.f : true ==> true].
  proof.
  proc.
  proc rewrite /=.
  proc rewrite /=.
  admit.
  qed.
end BlockSimpl.

(* -------------------------------------------------------------------- *)
(* Ranges: only the selected instructions are touched, deeply. *)
theory RangeSimpl.
  module M = {
    proc f(a : int, b : int) : int = {
      var c, i : int;

      c <- foo a;
      i <- 0;
      while (i < bar b) {
        if (foo i = 0) {
          c <- c + foo i;
        } else {
          c <- c + bar i;
        }
        i <- i + 1;
      }
      return c;
    }

    proc g(a : int, b : int) : int = {
      var c, i : int;

      c <- foo a;
      i <- 0;
      while (i < b * 2) {
        if (i + 1 = 0) {
          c <- c + (i + 1);
        } else {
          c <- c + i * 2;
        }
        i <- i + 1;
      }
      return c;
    }

    proc k(a : int, b : int) : int = {
      var c, i : int;

      c <- foo a;
      i <- 0;
      while (i < bar b) {
        if (i + 1 = 0) {
          c <- c + (i + 1);
        } else {
          c <- c + bar i;
        }
        i <- i + 1;
      }
      return c;
    }
  }.

  lemma L : equiv[M.f ~ M.g : ={arg} ==> ={res}].
  proof.
  proc.
  proc rewrite {1} [3..3] /=.
  by sim.
  qed.

  (* A single position is the singleton range: the while body is
     rewritten too *)
  lemma L0 : equiv[M.f ~ M.g : ={arg} ==> ={res}].
  proof.
  proc.
  proc rewrite {1} 3 /=.
  by sim.
  qed.

  (* Range inside a nested block *)
  lemma L' : equiv[M.f ~ M.k : ={arg} ==> ={res}].
  proof.
  proc.
  proc rewrite {1} ^while.:[1..1] /=.
  proc rewrite {2} ^while.1?:[1..1] /=.
  by sim.
  qed.

  lemma L'' : equiv[M.f ~ M.g : ={arg} ==> ={res}].
  proof.
  proc.
  proc rewrite {1} [1..2] /=.
  proc rewrite {2} [1..2] /=.
  proc rewrite {1} [3..3] /=.
  by sim.
  qed.
end RangeSimpl.

(* -------------------------------------------------------------------- *)
(* Match arms: the arm binders are in scope for the rewrite, even when
   their names clash with the proof context. *)
theory MatchSimpl.
  module M = {
    proc f(o : int option) : int = {
      var c : int;

      match o with
      | None   => c <- foo 0;
      | Some x => c <- foo x;
      end;
      return c;
    }

    proc g(o : int option) : int = {
      var c : int;

      match o with
      | None   => c <- 0 + 1;
      | Some x => c <- x + 1;
      end;
      return c;
    }

    proc k(o : int option) : int = {
      var c : int;

      match o with
      | None   => c <- 0 + 1;
      | Some x => c <- 1 + x;
      end;
      return c;
    }
  }.

  lemma L (x : int) : equiv[M.f ~ M.g : ={arg} /\ x = 0 ==> ={res}].
  proof.
  proc.
  proc rewrite {1} /=.
  by sim.
  qed.

  lemma L' (x : int) : equiv[M.g ~ M.k : ={arg} /\ x = 0 ==> ={res}].
  proof.
  proc.
  proc rewrite {1} ^match#Some.:[1..1] addzC.
  by sim.
  qed.
end MatchSimpl.

(* -------------------------------------------------------------------- *)
(* Lemma mode: instructions without an occurrence are skipped; the
   tactic fails only when nothing is rewritten. *)
theory BlockRw.
  module M = {
    proc f(a : int, b : int) : int = {
      var c : int;

      c <- a + b;
      if (a + b = 0) {
        c <- 0;
      } else {
        c <- c * (b + a);
      }
      return c;
    }

    proc g(a : int, b : int) : int = {
      var c : int;

      c <- b + a;
      if (b + a = 0) {
        c <- 0;
      } else {
        c <- c * (a + b);
      }
      return c;
    }
  }.

  lemma L : equiv[M.f ~ M.g : ={arg} ==> ={res}].
  proof.
  proc.
  proc rewrite {1} addzC.
  by sim.
  qed.

  lemma L' : equiv[M.f ~ M.g : ={arg} ==> ={res}].
  proof.
  proc.
  proc rewrite {1} [2..2] addzC.
  proc rewrite {1} [1..1] addzC.
  by sim.
  qed.

  lemma L'' : hoare[M.f : true ==> true].
  proof.
  proc.
  fail proc rewrite [1..1] mulzC.
  fail proc rewrite mulzA.
  proc rewrite mulzC.
  admit.
  qed.
end BlockRw.
