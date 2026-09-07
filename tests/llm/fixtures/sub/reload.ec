(* LOADed twice in one session, to pin what a reload costs nothing:
   `Neighbour' is elaborated once and served from the theory cache the
   second time, and the two replies have to be indistinguishable. *)
require import AllCore Neighbour.

lemma warm : neighbour = 3.
proof.
rewrite /neighbour.
trivial.
qed.
