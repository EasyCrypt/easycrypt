require import Int.

(* ==================================================================== *)
(* Abstract monoid: where all the lemmas live, written once. Names use
   the neutral [mop]/[idm] vocabulary and the [m] (monoid) suffix so
   downstream additive ([addmonoid]) and multiplicative ([mulmonoid])
   subclasses can introduce conventional ring-theoretic spellings
   without ambiguity at multi-monoid carriers like [comring].          *)
(* ==================================================================== *)
type class monoid = {
  op idm : monoid
  op mop : monoid -> monoid -> monoid

  axiom mopA : associative mop
  axiom mopC : commutative mop
  axiom mop0 : left_id idm mop
}.

(* -------------------------------------------------------------------- *)
section.
declare type t <: monoid.

lemma mop0m: right_id idm<:t> mop.
proof. by move=> x; rewrite mopC mop0. qed.

lemma mopCAm: left_commutative mop<:t>.
proof. by move=> x y z; rewrite !mopA (mopC x). qed.

lemma mopACm: right_commutative mop<:t>.
proof. by move=> x y z; rewrite -!mopA (mopC y). qed.

lemma mopACAm: interchange mop<:t> mop.
proof. by move=> x y z t; rewrite -!mopA (mopCAm y). qed.

lemma iteropE n (x : t): iterop n mop x idm = iter n (mop x) idm.
proof.
elim/natcase n => [n le0_n|n ge0_n].
+ by rewrite ?(iter0, iterop0).
+ by rewrite iterSr // mop0m iteropS.
qed.
end section.

(* ==================================================================== *)
(* Additive flavor of [monoid]. Renames [idm]/[mop] to [zero]/[(+)] at
   every [addmonoid] carrier. Below, section lemmas re-export the
   monoid lemmas under [add]-prefixed names; because [`a <: addmonoid]
   has exactly one [monoid] view, [mopA]/[mopC]/[mop0]/[mop0m]/...
   resolve unambiguously here without explicit selectors.              *)
(* ==================================================================== *)
type class addmonoid <: (monoid with idm = zero, mop = (+)) = {}.

section.
declare type t <: addmonoid.

lemma addmA: associative (+)<:t>.
proof. by apply: mopA. qed.

lemma addmC: commutative (+)<:t>.
proof. by apply: mopC. qed.

lemma add0m: left_id zero<:t> (+).
proof. by apply: mop0. qed.

lemma addm0: right_id zero<:t> (+).
proof. by apply: mop0m. qed.

lemma addmCA: left_commutative (+)<:t>.
proof. by apply: mopCAm. qed.

lemma addmAC: right_commutative (+)<:t>.
proof. by apply: mopACm. qed.

lemma addmACA: interchange (+)<:t> (+).
proof. by apply: mopACAm. qed.
end section.

(* ==================================================================== *)
(* Multiplicative flavor of [monoid]. Symmetric to [addmonoid]: renames
   [idm]/[mop] to [oner]/[( * )]. Section lemmas use [mul]-prefixed
   names and [1m] for left-identity. Unambiguous at [`a <: mulmonoid]. *)
(* ==================================================================== *)
type class mulmonoid <: (monoid with idm = oner, mop = ( * )) = {}.

section.
declare type t <: mulmonoid.

lemma mulmA: associative ( * )<:t>.
proof. by apply: mopA. qed.

lemma mulmC: commutative ( * )<:t>.
proof. by apply: mopC. qed.

lemma mul1m: left_id oner<:t> ( * ).
proof. by apply: mop0. qed.

lemma mulm1: right_id oner<:t> ( * ).
proof. by apply: mop0m. qed.

lemma mulmCA: left_commutative ( * )<:t>.
proof. by apply: mopCAm. qed.

lemma mulmAC: right_commutative ( * )<:t>.
proof. by apply: mopACm. qed.

lemma mulmACA: interchange ( * )<:t> ( * ).
proof. by apply: mopACAm. qed.
end section.
