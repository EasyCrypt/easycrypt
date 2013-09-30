require        Distr.
require        Bool.
require import Int.
require        Array.

(* We make a clone of the array theory so we
   can further restrict to fixed size arrays. *)
clone Array as Bits.
export Bits.

type bitstring = bool array.

(* Conversions for interaction with other array types *)
op to_array: bitstring -> bool Array.array.

axiom to_array_length: forall bs,
  Array.length (to_array bs) = length bs.

axiom to_array_get: forall bs i,
  0 <= i => i < length bs =>
  Array."_.[_]" (to_array bs) i = bs.[i].

op from_array: bool Array.array -> bitstring.

axiom from_array_length: forall bs,
  length (from_array bs) = Array.length bs.

axiom from_array_get: forall bs i,
  0 <= i => i < Array.length bs =>
  (from_array bs).[i] = Array."_.[_]" bs i.

lemma to_array_from_array: forall bs,
  from_array (to_array bs) = bs.
proof.
intros bs; apply extensionality; smt.
save.

lemma from_array_to_array: forall bs,
  to_array (from_array bs) = bs.
proof.
intros bs; apply Array.extensionality; smt.
save.

(* Xor *)
op (^^)(bs0 bs1:bitstring): bitstring = map2 Bool.(^^) bs0 bs1.

lemma xor_length: forall (bs0 bs1:bitstring),
  length bs0 = length bs1 =>
  length (bs0 ^^ bs1) = length bs0
by [].

lemma xor_get: forall (bs0 bs1:bitstring) (i:int),
  length bs0 = length bs1 =>
  0 <= i => i < length bs0 =>
  (bs0 ^^ bs1).[i] = Bool.(^^) bs0.[i] bs1.[i]
by [].

(* Zero and one for bitstrings *)

op zeros: int -> bitstring.
op ones : int -> bitstring.

axiom zeros_spec (l:int) : zeros l = create l false.
axiom ones_spec (l:int) : ones l = create l true.

lemma zeros_length (l:int): 0 <= l => length (zeros l) = l.
proof.
 rewrite zeros_spec; apply create_length.
qed.

lemma zeros_get (l i:int):
  0 <= l => 0 <= i => i < l =>
  (zeros l).[i] = false.
proof.
 rewrite zeros_spec;apply create_get.
qed.

lemma ones_length (l:int): 0 <= l => length (ones l) = l.
proof.
 rewrite ones_spec; apply create_length.
qed.

lemma ones_get (l i:int):
  0 <= l => 0 <= i => i < l =>
  (ones l).[i] = true.
proof.
 rewrite ones_spec;apply create_get.
qed.

lemma zeros_ones (l:int): 0 < l =>
  ! ((zeros l) = (ones l)).
proof.
 intros Hl;rewrite - not_def.
 intros Heq;cut H : true = false; last smt.
 rewrite - (zeros_get l 0) //;first smt.
 by rewrite - (ones_get l 0) //;smt.
save.

(* Lemmas *)
lemma xor_nilpotent: forall (bs:bitstring),
  bs ^^ bs = zeros (length bs).
proof.
  intros bs;apply extensionality;smt.
save.

lemma xor_assoc : forall (x y z : bitstring), 
length(x) = length(y) => length(y) = length(z) =>
 (x ^^ y) ^^ z = x ^^ (y ^^ z).
proof.
 intros x y z Hleq1 Hleq2; apply extensionality.
 cut Hxz : length x = length z by by rewrite Hleq1.
 cut Hxxy : length x = length (x ^^ y) by by rewrite xor_length.
 cut Hxyz : length x = length (y ^^ z) by by rewrite xor_length.
 split; first by rewrite ?xor_length // Hleq1.
 intros _ i Hle Hlt;rewrite ?xor_get //; first 5 smt.
 apply Bool.xor_associative.
save.

lemma xor_zeros_neutral : forall (x : bitstring),
  x ^^ zeros(length(x)) = x.
proof.
 intros x; apply extensionality;split;first by smt.
 intros Heq;rewrite Heq => i Hle Hlt;rewrite xor_get //.
   by rewrite zeros_length //;smt.
 rewrite zeros_get //; first smt.
 apply Bool.xor_false.
qed.

require import Real.
require import Distr.

(* Uniform distributions on length-parametric bitstrings *)
theory Dbitstring.
  op dbitstring: int -> bitstring distr.

  axiom mu_x_def_in: forall (k:int, s:bitstring),
    length s = k => mu_x (dbitstring k) s = 1%r/(2^k)%r.

  axiom mu_x_def_other: forall (k:int, s:bitstring),
    length s <> k => mu_x (dbitstring k) s = 0%r.

  lemma supp_def: forall (k:int, s:bitstring),
    in_supp s (dbitstring k) <=> length s = k.
  proof.
    intros k s; delta in_supp mu; simplify; split; intros H.
    smt.
    rewrite (mu_x_def_in k s _).
    smt.
    cut H1: (0%r < (2 ^ k)%r); [smt | ].
    cut H2: (0%r < Real.one * inv (2 ^ k)%r).
    rewrite -(Real.Inverse (2 ^ k)%r _); smt.
    smt.  
  qed.     

  axiom weight_pos: forall (k:int), 0 <= k => weight (dbitstring k) = 1%r.

  (* TODO Santi: write a proof if you really think this is a lemma *) 
  axiom mu_weight_neg: forall (k:int), k < 0 => weight (dbitstring k) = 0%r.

end Dbitstring.
