(* [proc change] on a fragment inside a [while] loop: the fragment runs
   again on the next iterations, after the loop guard, the rest of the
   loop body and its own previous runs. *)
require import AllCore.

(* -------------------------------------------------------------------- *)
(* The precondition [x = 0] does not hold anymore when the fragment runs
   again, as the fragment itself writes [x]. *)
theory ProcChangeLoopFrame.
  module M = {
    proc f(x : int, a : int) : int = {
      var i : int;
      i <- 0;
      while (i < 2) {
        x <- x + a;
        i <- i + 1;
      }
      return x;
    }
  }.

  lemma L : hoare [M.f : x = 0 /\ a = 1 ==> res = 1].
  proof.
  proc => /=.
  (* Local goal: equiv [x <- x + a ~ x <- 1 : a{1} = 1 ==> ={x}]. *)
  proc change ^while.1 : { x <- 1; }.
  fail by auto.
  abort.

  (* [a] is not written in the loop: [a = 1] can still be used. *)
  lemma L' : hoare [M.f : x = 0 /\ a = 1 ==> res = 2].
  proof.
  proc => /=.
  proc change ^while.1 : { x <- x + 1; }.
  - by auto.
  abort.

  lemma E : equiv [M.f ~ M.f : ={arg} /\ x{1} = 0 /\ a{1} = 1 ==> ={res}].
  proof.
  proc => /=.
  proc change {1} ^while.1 : { x <- 1; }.
  fail by auto.
  abort.

  lemma E' : equiv [M.f ~ M.f : ={arg} /\ a{1} = 1 ==> ={res}].
  proof.
  proc => /=.
  proc change {1} ^while.1 : { x <- x + 1; }.
  - by auto.
  abort.
end ProcChangeLoopFrame.

(* -------------------------------------------------------------------- *)
(* The fragment reads [t], which it writes: its next runs observe [t]. *)
theory ProcChangeLoopReads.
  module M = {
    proc f(a : int) : int = {
      var i, t, y : int;
      i <- 0;
      t <- 0;
      y <- 0;
      while (i < 2) {
        t <- t + a;
        y <- t;
        i <- i + 1;
      }
      return y;
    }
  }.

  lemma L : hoare [M.f : a = 1 ==> res = 1].
  proof.
  proc => /=.
  (* Local goal: equiv [t <- t + a; y <- t ~ y <- t + a :
       a{1} = 1 /\ ={a, t} ==> ={t, y}]. *)
  proc change ^while.:[1..2] : { y <- t + a; }.
  fail by auto.
  abort.

  lemma L' : hoare [M.f : a = 1 ==> res = 2].
  proof.
  proc => /=.
  proc change ^while.:[1..2] : { t <- a + t; y <- t + 0; }.
  - by auto => /#.
  proc change ^while.:[1..2] : [u : int] { u <- t; t <- u + a; y <- t; }.
  - by auto => /#.
  abort.
end ProcChangeLoopReads.
