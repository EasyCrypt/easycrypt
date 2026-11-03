(* A rule of an activated database applies inside crush even when the
   term it rewrites only appears after a delta step: the head reductions
   of split/elim see the activated databases too. *)
require import AllCore.

op c : int.
op g : int -> bool.
op sw (x y : int) = (y, x).

axiom gE : g c = true.
hint simplify in db : gE.

lemma crush_db : g (sw c c).`2.
proof. hint +db. by move=> />. qed.

lemma crush_db_split (b : bool) : b => g (sw c c).`2 /\ b.
proof. hint +db. by move=> />. qed.
