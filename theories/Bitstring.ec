require        Distr.
require        Bool.
require import Int.
require import Array.

type bitstring = bool array.

(* Xor *)
op (^^)(bs0 bs1:bitstring): bitstring = map2 Bool.(^^) bs0 bs1.

lemma length_xor (bs0 bs1:bitstring):
  length bs0 = length bs1 =>
  length (bs0 ^^ bs1) = length bs0
by [].

lemma get_xor (bs0 bs1:bitstring) (i:int):
  length bs0 = length bs1 =>
  0 <= i => i < length bs0 =>
  (bs0 ^^ bs1).[i] = Bool.(^^) bs0.[i] bs1.[i]
by [].

(* Zero and one for bitstrings *)
op zeros: int -> bitstring.
op ones : int -> bitstring.

axiom zeros_spec (l:int): zeros l = make l false.
axiom ones_spec (l:int): ones l = make l true.

lemma length_zeros (l:int): 0 <= l => length (zeros l) = l.
proof strict.
by rewrite zeros_spec; apply length_make.
qed.

lemma get_zeros (l i:int):
  0 <= i < l =>
  (zeros l).[i] = false.
proof strict.
by rewrite zeros_spec; apply get_make.
qed.

lemma length_ones (l:int): 0 <= l => length (ones l) = l.
proof strict.
by rewrite ones_spec; apply length_make.
qed.

lemma get_ones (l i:int):
  0 <= i < l =>
  (ones l).[i] = true.
proof strict.
by rewrite ones_spec; apply get_make.
qed.

lemma zeros_ones (l:int):
  0 < l =>
  zeros l <> ones l.
proof strict.
rewrite -not_def=> lt0_l eq_z_o.
by (cut: false = true)=> //;
   rewrite -(get_zeros l 0) // -(get_ones l 0) //;
   congr.
qed.

(* Lemmas *)
lemma xorN (bs:bitstring):
  bs ^^ bs = zeros (length bs).
proof strict.
by apply array_ext; split; smt.
qed.

lemma xorA (x y z : bitstring):
  length x = length y =>
  length y = length z =>
  x ^^ (y ^^ z) = (x ^^ y) ^^ z.
proof strict.
intros=> x_y y_z;
  cut x_z: length x = length z by (by rewrite x_y);
  cut x_xy: length x = length (x ^^ y) by (by rewrite length_xor);
  cut x_yz: length x = length (y ^^ z) by (by rewrite length_xor);
  apply array_ext; split.
    by rewrite ?length_xor.
    intros=> i [leq0_i lti_l]; rewrite ?get_xor //; first 5 smt.
    by rewrite Bool.xor_associative.
qed.

lemma xor0 (x : bitstring):
  x ^^ zeros (length x) = x.
proof strict.
apply array_ext; split; first smt.
by cut lx_x0: length (zeros (length x)) = length x
     by (by rewrite length_zeros ?length_pos);
   intros=> i; rewrite length_xor ?lx_x0 // => [leq0_i lti_lx];
   rewrite get_xor 1?rw_eq_sym // get_zeros // Bool.xor_false.
qed.

require import Real.
require import Distr.

(* Uniform distributions on length-parametric bitstrings *)
theory Dbitstring.
  op dbitstring: int -> bitstring distr.

  axiom mu_x_def_in (k:int) (s:bitstring):
    length s = k =>
    mu_x (dbitstring k) s = 1%r/(2^k)%r.

  axiom mu_x_def_other (k:int) (s:bitstring):
    length s <> k =>
    mu_x (dbitstring k) s = 0%r.

  lemma supp_def (k:int) (s:bitstring):
    in_supp s (dbitstring k) <=> length s = k.
  proof strict.
  rewrite /in_supp; split=> H; first smt.
  by rewrite mu_x_def_in; last smt.
  qed.     

  axiom weight_pos (k:int):
    0 <= k =>
    weight (dbitstring k) = 1%r.

  axiom mu_weight_neg (k:int):
    k < 0 =>
    weight (dbitstring k) = 0%r.
end Dbitstring.
