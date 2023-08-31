(* -------------------------------------------------------------------- *)
require import AllCore List Finite.

(* ==================================================================== *)
abstract theory FinType.
type t.

op enum : t list.

op card : int = size enum.

axiom enum_spec : forall x, count (pred1 x) enum = 1.

(* -------------------------------------------------------------------- *)
lemma enumP : forall x, mem enum x.
proof.
move=> x; have: 0 < count (pred1 x) enum by rewrite enum_spec.
by move/has_count/hasP; case=> y [h @/pred1 <-].
qed.

lemma enum_uniq : uniq enum.
proof. by apply/count_mem_uniq=> x; rewrite enumP enum_spec. qed.

lemma card_gt0 : 0 < card.
proof.
rewrite /card; have: mem enum witness by rewrite enumP.
by case: enum=> //= x s _; rewrite addzC ltzS size_ge0.
qed.

lemma count_mem xs :
  uniq xs => count (mem xs) enum = size xs.
proof.
move=> eq_xs; rewrite count_swap // 1:&(enum_uniq).
by rewrite count_predT_eq // &(enumP).
qed.

lemma is_finite_for : is_finite_for predT enum.
proof. by split=> [|x]; [apply: enum_uniq | rewrite enumP]. qed.

lemma is_finite : finite_type<:t>.
proof. exact: (finite_for_finite _ _ is_finite_for). qed.

lemma perm_eq_enum_to_seq : perm_eq enum (Finite.to_seq predT).
proof.
apply: uniq_perm_eq.
- by apply: enum_uniq.
- by apply/uniq_to_seq/is_finite.
- by move=> x; rewrite mem_to_seq 1:&(is_finite) enumP.
qed.

lemma card_size_to_seq : card = size (Finite.to_seq<:t> predT).
proof. by apply/perm_eq_size/perm_eq_enum_to_seq. qed.
end FinType.

(* ==================================================================== *)
abstract theory FinProdType.
type t1, t2.

clone FinType as FT1 with type t <- t1.
clone FinType as FT2 with type t <- t2.

clone include FinType
  with type t    = t1 * t2,
         op enum = allpairs (fun x y => (x, y)) FT1.enum FT2.enum
  proof *.

realize enum_spec.
proof.
case=> x y; rewrite count_uniq_mem.
+ by apply/allpairs_uniq => //; [apply FT1.enum_uniq | apply FT2.enum_uniq].
+ by apply/b2i_eq1/allpairsP; exists (x, y); rewrite !(FT1.enumP, FT2.enumP).
qed.
end FinProdType.
