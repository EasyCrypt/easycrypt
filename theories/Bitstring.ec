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
  Array.__get (to_array bs) i = bs.[i].

op from_array: bool Array.array -> bitstring.

axiom from_array_length: forall bs,
  length (from_array bs) = Array.length bs.

axiom from_array_get: forall bs i,
  0 <= i => i < Array.length bs =>
  (from_array bs).[i] = Array.__get bs i.

lemma to_array_from_array: forall bs,
  from_array (to_array bs) = bs.
proof.
intros bs; apply extensionality; trivial.
save.

lemma from_array_to_array: forall bs,
  to_array (from_array bs) = bs.
proof.
intros bs; apply Array.extensionality; trivial.
save.

(* Xor *)
op (^^)(bs0 bs1:bitstring): bitstring = map2 Bool.xorb bs0 bs1.

lemma xor_length: forall (bs0 bs1:bitstring),
  length bs0 = length bs1 =>
  length (bs0 ^^ bs1) = length bs0
by [].

lemma xor_get: forall (bs0 bs1:bitstring) (i:int),
  length bs0 = length bs1 =>
  0 <= i => i < length bs0 =>
  (bs0 ^^ bs1).[i] = Bool.xorb bs0.[i] bs1.[i]
by [].

(* Zero for bitstrings *)
op zeros: int -> bitstring.

axiom zeros_length: forall (l:int),
  0 <= l =>
  length (zeros l) = l.

axiom zeros_get: forall (l i:int),
  0 <= l => 0 <= i => i < l =>
  (zeros l).[i] = false.

(* Lemmas *)
lemma xor_nilpotent: forall (bs:bitstring),
  bs ^^ bs = zeros (length bs).
proof.
  intros bs; apply extensionality.
  delta (==); simplify; split; first trivial.
  intros i i_pos i_upbd.
  delta (^^); simplify.
  rewrite (zeros_get (length bs) i _ _ _);
    [trivial | trivial | trivial | ].
  rewrite (map2_get<:bool,bool,bool> bs bs Bool.xorb i _ _ _);
    trivial.
save.

lemma xor_assoc : forall (x y z : bitstring), 
length(x) = length(y) => length(y) = length(z) =>
 (x ^^ y) ^^ z = x ^^ (y ^^ z).
proof.
 intros x y z Hleq1 Hleq2.
 apply extensionality.
 delta (==);simplify.
 split;try trivial.
 delta (^^);simplify.
 intros i H H0.
 rewrite (map2_get<:bool,bool,bool> (map2 Bool.xorb x y) z Bool.xorb i _ _ _);
  [trivial | trivial | trivial | ].
 rewrite (map2_get<:bool,bool,bool> x y Bool.xorb i _ _ _);
  [trivial | trivial | trivial | ].
 rewrite (map2_get<:bool,bool,bool> x (map2 Bool.xorb y z)  Bool.xorb i _ _ _);
 trivial.
save.

lemma xor_zeroes_neutral : forall (x : bitstring),
x ^^ zeros(length(x)) = x.
proof.
 intros x; apply extensionality.
 delta (==); simplify; split; first trivial.
 intros i i_pos i_upbd; delta (^^); simplify.
 rewrite (map2_get<:bool,bool,bool> x (zeros (length x)) Bool.xorb i _ _ _);
  [trivial | trivial | trivial | ].
 rewrite (zeros_get (length x) i _ _ _);
 trivial.
save.

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
    trivial.
    rewrite (mu_x_def_in k s _).
    trivial.
    cut H1: (0%r < (2 ^ k)%r); [trivial | ].
    cut H2: (0%r < Real.one * inv (2 ^ k)%r).
    rewrite <-(Real.Inverse (2 ^ k)%r _); trivial.
    trivial.  
  qed.     

  axiom weight_pos: forall (k:int), 0 <= k => weight (dbitstring k) = 1%r.

  (* TODO Santi: write a proof if you really think this is a lemma *) 
  axiom mu_weight_neg: forall (k:int), k < 0 => weight (dbitstring k) = 0%r.

end Dbitstring.
