require import AllCore TcMonoid TcRing.

(* Tvar carrier with multi-parent + factory *)
type class my_comring <: addgroup & (mulmonoid with idm = oner, (+) = mymul) = {
  op oner  : my_comring
  op mymul : my_comring -> my_comring -> my_comring
}.

section.
declare type t <: my_comring.

(* Multiplicative side: factory inheritance, abbrev-mediated. *)
lemma test_mulrA : associative ( * )<:t>.
proof. apply addmA. qed.

lemma test_mulrC : commutative ( * )<:t>.
proof. apply addmC. qed.

lemma test_mul1r : left_id one<:t> ( * )<:t>.
proof. apply add0m. qed.

(* Additive side on a multi-parent carrier: [(+)<:t>] is reachable
   via two paths to [monoid] (addgroup and mulmonoid-with-renaming),
   but only the addgroup path leaves [(+)] unrenamed. Op-name-aware
   path resolution should pick that path uniquely. *)
lemma test_addrA : associative (+)<:t>.
proof. apply addmA. qed.

lemma test_addrC : commutative (+)<:t>.
proof. apply addmC. qed.

lemma test_add0r : left_id zero<:t> (+)<:t>.
proof. apply add0m. qed.

end section.
