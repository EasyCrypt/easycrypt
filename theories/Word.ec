require        Bool.
require import Int.

op length: int.
axiom length_pos: 0 <= length.

(* A word only has the get operator: its size is fixed. *)
(* Ideally, we would have cloned bitstrings, but they are equipped with an empty operator. *)
type word.
op __get: word -> int -> bool.

pred (==)(w0, w1:word) = forall i,
  0 <= i => i < length =>
  w0.[i] = w1.[i].

axiom extentionality: forall w0 w1,
  w0 == w1 => w0 = w1.

(* set *)
op __set: word -> int -> bool -> word.
axiom set_get: forall w i j b,
  0 <= i => i < length =>
  w.[i <- b].[j] = (i = j) ? b : w.[j].

(* zeros *)
op zeros: word.
axiom zeros_get: forall i,
  0 <= i => i < length =>
  zeros.[i] = false.

(* xor *)
op (^^): word -> word -> word.
axiom xor_get: forall w0 w1 i,
  0 <= i => i < length =>
  (w0 ^^ w1).[i] = Bool.xorb w0.[i] w1.[i].

lemma xor_nilpotent: forall w,
  w ^^ w = zeros
proof.
intros w;
  apply (extentionality (w ^^ w) zeros _);
  trivial.
save.

lemma xor_commutative: forall w0 w1,
  w0 ^^ w1 = w1 ^^ w0
proof.
intros w0 w1;
  apply (extentionality (w0 ^^ w1) (w1 ^^ w0) _);
  cut xorb_commute: (forall i, 0 <= i => i < length =>
                      (w0 ^^ w1).[i] = (w1 ^^ w0).[i]);
  trivial.
save.

lemma xor_zeros: forall w,
  w ^^ zeros = w
proof.
intros w;
  apply (extentionality (w ^^ zeros) w _);
  cut xorb_zeros: (forall i, 0 <= i => i < length =>
                    (w ^^ zeros).[i] = w.[i]);
  trivial.
save.

(* TODO: Finish writing the conversions *)
require        Array.
op to_array: word -> bool Array.array.
axiom to_array_length: forall w,
  Array.length (to_array w) = length.
axiom to_array_get: forall w i,
  0 <= i => i < length =>
  Array.__get (to_array w) i = w.[i].

op from_array: bool Array.array -> word.
axiom from_array_get: forall a i,
  Array.length a = length =>
  0 <= i => i < length =>
  (from_array a).[i] = Array.__get a i.

lemma to_array_from_array: forall a,
  Array.length a = length =>
  to_array (from_array a) = a
proof.
intros a Length;
  apply (Array.extentionality<:bool> (to_array (from_array a)) a _);
  trivial.
save.

lemma from_array_to_array: forall w,
  from_array (to_array w) = w
proof.
intros w;
  apply (extentionality (from_array (to_array w)) w _);
  trivial.
save.

require import Real.
require import Distr.

(* Uniform distribution on fixed-length words *)
theory Dword.
  op dword: word distr.

  axiom supp_def: forall (w:word), in_supp w dword.

  axiom mu_x_def: forall (w:word),
    mu_x dword w = 1%r/(2^length)%r.

  axiom mu_weight_pos: mu_weight dword = 1%r.
end Dword.
