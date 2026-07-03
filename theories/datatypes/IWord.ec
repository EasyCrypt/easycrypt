(* -------------------------------------------------------------------- *)
(* Length-indexed bit words, built on top of [IArray]: a [ word<:n> ] wraps
   a [ bool array<:n> ] but reads [false] out of range (like [BitWord.eca]).
   The width [n] lives in the index; the derived layer is developed in a
   [declare index {n}] section (so ops/lemmas drop their [{n}] binder). *)

require import AllCore Bool.
require import IArray.

(* -------------------------------------------------------------------- *)
(* Signature. *)
type {n} word.

op ofword {n} (w : word<:n>) : bool array<:n>.
op mkword {n} (a : bool array<:n>) : word<:n>.

axiom ofwordK {n} (w : word<:n>) : mkword (ofword w) = w.
axiom mkwordK {n} (a : bool array<:n>) : ofword (mkword[:n] a) = a.

(* ==================================================================== *)
section IWord.
declare index {n}.

(* Out-of-range bits read as [false]. *)
op "_.[_]" (w : word<:n>) (i : int) : bool =
  if 0 <= i < n then (ofword w).[i] else false.

lemma getE (w : word<:n>) i :
  w.[i] = if 0 <= i < n then (ofword w).[i] else false.
proof. by move=> _; rewrite /"_.[_]". qed.

lemma get_in (w : word<:n>) i :
  0 <= i < n => w.[i] = (ofword w).[i].
proof. by move=> _ hi; rewrite getE (ifT _ _ _ hi). qed.

lemma get_out (w : word<:n>) i :
  !(0 <= i < n) => w.[i] = false.
proof. by move=> _ hi; rewrite getE (ifF _ _ _ hi). qed.

(* -------------------------------------------------------------------- *)
lemma wordP (w1 w2 : word<:n>) :
  (forall i, 0 <= i < n => w1.[i] = w2.[i]) <=> w1 = w2.
proof.
move=> _; split=> [eqi|-> //]; rewrite -(ofwordK w1) -(ofwordK w2); congr.
apply/IArray.eq_from_get=> i hi; move: (eqi i hi).
by rewrite !getE hi.
qed.

(* -------------------------------------------------------------------- *)
op offunw (f : int -> bool) : word<:n> = mkword (offun[:n] f).

lemma offunwE (f : int -> bool) i :
  (offunw f).[i] = if 0 <= i < n then f i else false.
proof.
move=> _; rewrite getE /offunw mkwordK.
by case: (0 <= i < n) => hi //=; rewrite offunE.
qed.

(* -------------------------------------------------------------------- *)
op zerow : word<:n> = offunw (fun _ => false).
op onew  : word<:n> = offunw (fun _ => true).

op ( +^ ) (w1 w2 : word<:n>) : word<:n> =
  offunw (fun i => w1.[i] ^^ w2.[i]).

op andw (w1 w2 : word<:n>) : word<:n> =
  offunw (fun i => w1.[i] /\ w2.[i]).

op oppw (w : word<:n>) : word<:n> = w.

op invw (w : word<:n>) : word<:n> =
  offunw (fun i => !w.[i]).

(* -------------------------------------------------------------------- *)
lemma zerowE i : (zerow).[i] = false.
proof. by move=> _; rewrite offunwE if_same. qed.

lemma onewE i : (onew).[i] = (0 <= i < n).
proof. by move=> _; rewrite offunwE; case: (0 <= i < n). qed.

lemma xorwE (w1 w2 : word<:n>) i :
  (w1 +^ w2).[i] = w1.[i] ^^ w2.[i].
proof.
move=> _; rewrite offunwE; case: (0 <= i < n) => hi //=.
by rewrite !get_out // xor_false.
qed.

lemma andwE (w1 w2 : word<:n>) i :
  (andw w1 w2).[i] = (w1.[i] /\ w2.[i]).
proof.
move=> _; rewrite offunwE; case: (0 <= i < n) => hi //=.
by rewrite !get_out.
qed.

lemma invwE (w : word<:n>) i :
  0 <= i < n => (invw w).[i] = !w.[i].
proof. by move=> _ hi; rewrite offunwE hi. qed.

lemma oppwE (w : word<:n>) i : (oppw w).[i] = w.[i].
proof. by move=> _. qed.

hint rewrite bwordE : zerowE onewE xorwE andwE invwE.

(* -------------------------------------------------------------------- *)
lemma onew_neq0 : 0 < n => onew <> zerow.
proof.
move=> _ gt0n; apply/negP => /wordP /(_ 0).
by rewrite !bwordE /= gt0n.
qed.

lemma xorw0 : right_id zerow ( +^ ).
proof. by move=> _ w; apply/wordP=> i _; rewrite !bwordE xor_false. qed.

lemma xorwA : associative (( +^ )).
proof. by move=> _ w1 w2 w3; apply/wordP=> i _; rewrite !bwordE xorA. qed.

lemma xorwC : commutative (( +^ )).
proof. by move=> _ w1 w2; apply/wordP=> i _; rewrite !bwordE xorC. qed.

lemma xorwK (w : word<:n>) : w +^ w = zerow.
proof. by move=> _; apply/wordP=> i _; rewrite !bwordE xorK. qed.

lemma andw1 : right_id onew andw.
proof. by move=> _ w; apply/wordP=> i h; rewrite !bwordE h. qed.

lemma andwA : associative (andw).
proof. by move=> _ w1 w2 w3; apply/wordP=> i h; rewrite !bwordE andbA. qed.

lemma andwC : commutative (andw).
proof. by move=> _ w1 w2; apply/wordP=> i h; rewrite !bwordE andbC. qed.

lemma andwK : idempotent (andw).
proof. by move=> _ w; apply/wordP=> i h; rewrite !bwordE andbb. qed.

lemma andwDl : left_distributive (andw) ( +^ ).
proof.
move=> _ w1 w2 w3; apply/wordP=> i h; rewrite !bwordE.
by move: (w1.[i]) (w2.[i]) (w3.[i]) => b1 b2 b3; case: b1; case: b2; case: b3.
qed.

end section IWord.
