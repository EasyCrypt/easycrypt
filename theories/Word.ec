(* --------------------------------------------------------------------
 * Copyright IMDEA Software Institute / INRIA - 2013, 2014
 * -------------------------------------------------------------------- *)

require Bool.
require import Int.

op length: int.
axiom length_pos: 0 <= length.

(* A word only has the get operator: its size is fixed. *)
(* Ideally, we would have cloned bitstrings, but they are equipped with an empty operator. *)
type word.
op "_.[_]": word -> int -> bool.

pred (==)(w0, w1:word) = forall i,
  0 <= i => i < length =>
  w0.[i] = w1.[i].

axiom word_ext w0 w1:
  w0 == w1 => w0 = w1.

(* set *)
op "_.[_<-_]": word -> int -> bool -> word.
axiom get_set w i j b:
  0 <= i => i < length =>
  w.[i <- b].[j] = (i = j) ? b : w.[j].

(* zeros *)
op zeros: word.
axiom get_zeros i:
  0 <= i < length =>
  zeros.[i] = false.

(* xor *)
op (^^): word -> word -> word.
axiom get_xor w0 w1 i:
  0 <= i < length =>
  (w0 ^^ w1).[i] = Bool.(^^) w0.[i] w1.[i].

lemma xorK w:
  w ^^ w = zeros.
proof strict.
by apply word_ext; smt.
qed.

lemma xorC w0 w1:
  w0 ^^ w1 = w1 ^^ w0.
proof strict.
by apply word_ext; smt.
qed.

lemma xorA x y z:
  x ^^ (y ^^ z) = (x ^^ y) ^^ z.
proof strict.
by apply word_ext; smt.
qed.

lemma xor0 w: w ^^ zeros = w.
proof strict.
by apply word_ext; smt.
qed.

lemma xor_opt x y: x ^^ y ^^ y = x.
proof strict.
by rewrite -xorA xorK xor0.
qed.

(* TODO: Finish writing the conversions *)
(** Array conversions *)
require        Array.
op to_bits: word -> bool Array.array.
axiom length_to_array w:
  Array.length (to_bits w) = length.
axiom get_to_array w i:
  0 <= i < length =>
  Array."_.[_]" (to_bits w) i = w.[i].

op from_bits: bool Array.array -> word.
axiom get_from_bits a i:
  Array.length a = length =>
  0 <= i < length =>
  (from_bits a).[i] = Array."_.[_]" a i.

lemma to_from_array a:
  Array.length a = length =>
  to_bits (from_bits a) = a.
proof strict.
by intros Hlen; apply Array.array_ext; smt.
qed.

lemma from_to_bits w:
  from_bits (to_bits w) = w.
proof strict.
by apply word_ext; smt.
qed.

(** Integer conversion *)
op to_int: word -> int.
op from_int: int -> word.

axiom to_from_int i:
  0 <= i < 2^length =>
  to_int (from_int i) = i.

axiom from_to_int w:
  from_int (to_int w) = w.

require import Real.
require import Distr.
require import FSet.

(* Uniform distribution on fixed-length words *)
theory Dword.
  op dword : word distr.

  axiom mu_x_def (w:word): mu_x dword w = 1%r / (2 ^ length)%r.

  axiom dwordL: weight dword = 1%r.
  
  lemma supp_def (w:word): in_supp w dword.
  proof strict.
  rewrite /in_supp mu_x_def; smt.
  qed.

  lemma mu_cpMemw (s : word set):
    mu dword (cpMem s) = (card s)%r *( 1%r / (2^length)%r).
  proof strict.
  rewrite (mu_cpMem _ _ (1%r / (2^length)%r))=> //.
  intros x; rewrite mu_x_def; smt.
  qed.

  import FSet.Dexcepted.  
  lemma restrwL (X : word set):
    FSet.card X < 2^length =>
    weight (dword \ X) = 1%r.
  proof strict.
  intros=> Hcard; rewrite lossless_restr ?dwordL ?mu_cpMemw //.
  apply (real_lt_trans _ ((2^length)%r * (1%r / (2 ^ length)%r)) _);
    last smt.
  apply mulrM; last by rewrite from_intM.
  smt.
  qed.
end Dword.
