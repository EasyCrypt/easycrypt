(* Under +strict_bullets, the last sibling of a split point can be
   continued at the parent level without a bullet: when the previous
   sibling is closed and exactly one sibling remains, the inner frame
   pops automatically. *)
require import AllCore.

pragma +strict_bullets.

(* The motivating pattern: a flat chain of hoare `seq N : <post>'
   phrases, each discharged with a single `+' for the side obligation;
   the continuation runs at the parent level without further bullets. *)
module M = {
  proc f() : int = {
    var x : int;
    x <- 1;
    x <- x + 1;
    x <- x + 1;
    return x;
  }
}.

lemma seq_chain : hoare[M.f : true ==> res = 3].
proof.
proc.
seq 1 : (x = 1).
+ by auto.
seq 1 : (x = 2).
+ by auto.
auto.
qed.

(* A 2-way propositional split: the last subgoal can be dispatched
   without a bullet. *)
lemma last_no_bullet (p q : bool) : p => q => p /\ q.
proof.
move=> hp hq; split.
- exact hp.
exact hq.
qed.

(* A 3-way split keeps its enumeration discipline for the first two
   subgoals, but the third may be unbulleted. *)
lemma three_ways (p q r : bool) :
  p => q => r => p /\ q /\ r.
proof.
move=> hp hq hr; do! split.
- exact hp.
- exact hq.
exact hr.
qed.

(* Cascading auto-pop: a nested split whose inner level reaches its
   last sibling AND whose outer level reaches its last sibling can be
   continued at the outermost level with no bullets. *)
lemma cascade (p q r s : bool) :
  p => q => r => s => (p /\ q) /\ (r /\ s).
proof.
move=> hp hq hr hs; split.
- split.
  + exact hp.
  exact hq.
split.
+ exact hr.
exact hs.
qed.
