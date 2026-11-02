(* -------------------------------------------------------------------- *)
(* Unsigned/signed integer interpretation of indexed words, at symbolic
   and concrete widths.  Exercises the [get_to_uint] bit<->int bridge and
   the round-trip lemmas from [IWord].

   Also a regression for the SMT translation of symbolic indices: an
   indexed type in scope (e.g. [w : word<:k>]) no longer poisons the goal
   — the index is a first-class Why3 int, so [smt] reasons through it. *)
require import AllCore IntDiv IArray IWord.

(* Symbolic width: round-trips and bounds. *)
lemma uintK {k} (w : word<:k>) : of_int (to_uint w) = w by apply to_uintK.
lemma uint_cmp {k} (w : word<:k>) : 0 <= to_uint w < 2 ^ k by apply to_uint_cmp.
lemma uintP {k} (w1 w2 : word<:k>) :
  w1 = w2 <=> to_uint w1 = to_uint w2 by apply to_uint_eq.

(* The bit <-> int bridge. *)
lemma bit_of_uint {k} (w : word<:k>) i :
  w.[i] = (0 <= i < k /\ to_uint w %/ 2 ^ i %% 2 <> 0) by apply get_to_uint.

(* Constants relate the bitwise and numeric views. *)
lemma z0 {k} : to_uint zerow[:k] = 0 by apply to_uint_zerow.
lemma o1 {k} : to_uint onew[:k] = 2 ^ k - 1 by apply to_uint_onew.

(* ==================================================================== *)
(* SMT reaches through symbolic indices. *)

(* A pure-int goal is provable even with an indexed-type local in scope
   (this used to be skipped: "constructs not yet exported to Why3"). *)
lemma smt_thru {k} (w : word<:k+1>) : 0 <= k => 0 < k + 1.
proof. smt(). qed.

(* [smt] uses an indexed-op fact at symbolic width. *)
lemma smt_uint {k} (w : word<:k>) : to_uint w < 2 ^ k.
proof. smt(to_uint_cmp). qed.

lemma smt_uint2 {k} (w1 w2 : word<:k>) :
  to_uint w1 = to_uint w2 => w1 = w2.
proof. smt(to_uint_eq). qed.

(* Signed view (positive width). *)
lemma sint_cmp {k} (w : word<:k+1>) : 0 <= k =>
  - 2 ^ k <= to_sint w <= 2 ^ k - 1.
proof.
move=> ge0; have h := to_sint_cmp w _; first by smt().
have e : 2 ^ (k + 1 - 1) = 2 ^ k by congr; ring.
by move: h; rewrite e.
qed.

(* Concrete width. *)
lemma c8 (w : word<:8>) : 0 <= to_uint w < 2 ^ 8 by apply to_uint_cmp.
