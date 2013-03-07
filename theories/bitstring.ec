require bool.
require import int.
require export array.

type bitstring = bool array.

(* Xor *)
op [^^](bs0:bitstring, bs1:bitstring): bitstring = Functional.map2 bool.xorb bs0 bs1.

lemma xor_length: forall (bs0 bs1:bitstring),
  length bs0 = length bs1 =>
  length (bs0 ^^ bs1) = length bs0.

lemma xor_get: forall (bs0 bs1:bitstring) (i:int),
  length bs0 = length bs1 =>
  0 <= i => i < length bs0 =>
  (bs0 ^^ bs1).[i] = bool.xorb bs0.[i] bs1.[i].

(* Zero for bitstrings *)
op zeros: int -> bitstring.

axiom zeros_length: forall (l:int),
  0 <= l =>
  length(zeros l) = l.

axiom zeros_get: forall (l i:int),
  0 <= l => 0 <= i => i < l =>
  (zeros l).[i] = false.

(* Lemmas *)
lemma xor_nilpotent: forall (bs:bitstring),
  bs ^^ bs = zeros (length bs)
proof.
  intros bs.
  apply extentionality<:bool> ((bs ^^ bs),(zeros (length bs)),_).
  trivial.
save.
