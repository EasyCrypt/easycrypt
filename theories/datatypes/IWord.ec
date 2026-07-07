(* -------------------------------------------------------------------- *)
(* Length-indexed bit words, built on top of [IArray]: a [ word<:n> ] wraps
   a [ bool array<:n> ] but reads [false] out of range (like [BitWord.eca]).
   The width [n] lives in the index; the derived layer is developed in a
   [declare index {n}] section (so ops/lemmas drop their [{n}] binder). *)

require import AllCore Bool IntDiv Ring StdOrder List BitEncoding.
import BS2Int.
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

op orw (w1 w2 : word<:n>) : word<:n> =
  offunw (fun i => w1.[i] \/ w2.[i]).

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

lemma orwE (w1 w2 : word<:n>) i :
  (orw w1 w2).[i] = (w1.[i] \/ w2.[i]).
proof.
move=> _; rewrite offunwE; case: (0 <= i < n) => hi //=.
by rewrite !get_out.
qed.

lemma invwE (w : word<:n>) i :
  0 <= i < n => (invw w).[i] = !w.[i].
proof. by move=> _ hi; rewrite offunwE hi. qed.

lemma oppwE (w : word<:n>) i : (oppw w).[i] = w.[i].
proof. by move=> _. qed.

lemma oppwK (w : word<:n>) : oppw w = w.
proof. by move=> _. qed.

hint rewrite bwordE : zerowE onewE xorwE andwE orwE invwE.

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

lemma andw0 (w : word<:n>) : andw w zerow = zerow.
proof. by move=> _; apply/wordP=> i _; rewrite !bwordE andbF. qed.

lemma orwA : associative (orw).
proof. by move=> _ w1 w2 w3; apply/wordP=> i _; rewrite !bwordE orbA. qed.

lemma orwC : commutative (orw).
proof. by move=> _ w1 w2; apply/wordP=> i _; rewrite !bwordE orbC. qed.

lemma orwK : idempotent (orw).
proof. by move=> _ w; apply/wordP=> i _; rewrite !bwordE orbb. qed.

lemma orw0 (w : word<:n>) : orw w zerow = w.
proof. by move=> _; apply/wordP=> i _; rewrite !bwordE orbF. qed.

lemma orw1 (w : word<:n>) : orw w onew = onew.
proof. by move=> _; apply/wordP=> i h; rewrite !bwordE h orbT. qed.

end section IWord.

(* ==================================================================== *)
(* Boolean-ring structure.  [ word<:n> ] is the trivial ring at [n = 0]
   ([onew = zerow]), so no ring instance holds for the whole family.  We
   instead register the instance over [ word<:n+1> ], whose width is
   provably positive: [oner_neq0] discharges unconditionally, and instance
   resolution then fires for any manifestly-nonzero width — concrete
   ([word<:8>]) or symbolic ([word<:k+1>]) — while refusing an arbitrary
   [word<:m>] (which could be [word<:0>]). *)
section IWordRing.
declare index {n}.

pred unitw (w : word<:n+1>) = w = onew.

clone import Ring.BoolRing as WRing with
  type t     <- word<:n+1>,
  op   zeror <- zerow[:n+1],
  op   ( + ) <- ( +^ )[:n+1],
  op   [ - ] <- oppw[:n+1],
  op   oner  <- onew[:n+1],
  op   ( * ) <- andw[:n+1],
  op   invr  <- oppw[:n+1],
  pred unit  <- unitw
  proof *.
realize addrA.     proof. by move=> ge0; apply/xorwA. qed.
realize addrC.     proof. by move=> ge0; apply/xorwC. qed.
realize add0r.     proof. by move=> ge0 x; rewrite xorwC xorw0. qed.
realize addNr.     proof. by move=> ge0 x; rewrite /oppw; apply/xorwK. qed.
realize oner_neq0. proof. by move=> ge0; apply/onew_neq0; smt(). qed.
realize mulrA.     proof. by move=> ge0; apply/andwA. qed.
realize mulrC.     proof. by move=> ge0; apply/andwC. qed.
realize mul1r.     proof. by move=> ge0 x; rewrite andwC andw1. qed.
realize mulrDl.    proof. by move=> ge0; apply/andwDl. qed.
realize mulrr.     proof. by move=> ge0 x; apply/andwK. qed.
realize unitout.   proof. by move=> ge0 x hnu; apply/oppwK. qed.
realize mulVr.
proof. by move=> ge0 x; rewrite /unitw => hx; rewrite oppwK andwK; exact hx. qed.
realize unitP.
proof.
move=> ge0 x y; rewrite /unitw -wordP => h; rewrite -wordP => i hi.
by move: (h i hi); rewrite andwE onewE hi; smt().
qed.
end section IWordRing.

(* ==================================================================== *)
(* Numeric interpretation.  [to_uint] reads a word as an unsigned integer
   in [ [0, 2^n) ]; [of_int] is its (mod 2^n) inverse.  The bridge
   [get_to_uint] ties the bit view to the numeric view.  The signed view
   ([to_sint]/[msb]) needs a positive width, so its range lemmas carry a
   [0 < n] hypothesis. *)

section IWordNum.
declare index {n}.

abbrev modulus = 2 ^ n.

op w2bits (w : word<:n>) : bool list = ofarr (ofword w).
op bits2w (s : bool list) : word<:n> = mkword (mkarr s).

op to_uint (w : word<:n>) : int = bs2int (w2bits w).
op of_int (x : int) : word<:n> = bits2w (int2bs n (x %% modulus)).

lemma size_w2bits (w : word<:n>) : size (w2bits w) = n.
proof. by move=> ge0; rewrite /w2bits size_ofarr. qed.

lemma w2bitsE (w : word<:n>) i : 0 <= i < n => nth false (w2bits w) i = w.[i].
proof.
move=> ge0 hi; rewrite /w2bits get_in //= IArray.getE.
by rewrite (nth_change_dfl witness false) // size_ofarr.
qed.

lemma get_to_uint (w : word<:n>) i :
  w.[i] = (0 <= i < n /\ to_uint w %/ 2 ^ i %% 2 <> 0).
proof.
move=> ge0; case: (0 <= i < n) => hi /=; last by rewrite get_out.
rewrite -w2bitsE // /to_uint -{1}(bs2intK (w2bits w)) size_w2bits.
by rewrite /int2bs nth_mkseq //= size_w2bits.
qed.

lemma gt0_modulus : 0 < modulus.
proof. by move=> ge0; rewrite StdOrder.IntOrder.expr_gt0. qed.

lemma bits2wK (s : bool list) : size s = n => w2bits (bits2w s) = s.
proof. by move=> ge0 hs; rewrite /w2bits /bits2w mkwordK mkarrK. qed.

lemma w2bitsK (w : word<:n>) : bits2w (w2bits w) = w.
proof. by move=> ge0; rewrite /bits2w /w2bits ofarrK ofwordK. qed.

lemma to_uint_cmp (w : word<:n>) : 0 <= to_uint w < modulus.
proof.
move=> ge0; rewrite /to_uint; split; first by apply bs2int_ge0.
by move=> _; rewrite -(size_w2bits w) bs2int_le2Xs.
qed.

lemma of_uintK (x : int) : to_uint (of_int x) = x %% modulus.
proof.
move=> ge0; rewrite /to_uint /of_int bits2wK.
- by rewrite size_int2bs; smt().
rewrite int2bsK //; smt(gt0_modulus modz_ge0 ltz_pmod).
qed.

lemma to_uintK (w : word<:n>) : of_int (to_uint w) = w.
proof.
move=> ge0; rewrite /of_int pmod_small 1:to_uint_cmp.
by rewrite /to_uint -(size_w2bits w) bs2intK w2bitsK.
qed.

lemma to_uint_eq (w1 w2 : word<:n>) : (w1 = w2) <=> (to_uint w1 = to_uint w2).
proof. by move=> ge0; split=> [->//|h]; rewrite -(to_uintK w1) -(to_uintK w2) h. qed.

(* Dual of [get_to_uint]: the bit of a numeral. *)
lemma of_intwE (x : int) i :
  (of_int x).[i] = (0 <= i < n /\ (x %% modulus) %/ 2 ^ i %% 2 <> 0).
proof.
move=> ge0; rewrite get_to_uint; case: (0 <= i < n) => //= hi.
by rewrite of_uintK.
qed.

(* -------------------------------------------------------------------- *)
(* The [n]-bit slice of an integer, i.e. the value of bit [i] of [x] once
   [x] has been reduced modulo [modulus].  This is what indexing a word
   [(of_int x).[i]] computes; the two lemmas below are pure-integer facts
   about how multiplying / dividing by [2^k] shifts those bits. *)
lemma gt0_pow2 (k : int) : 0 < 2 ^ k.
proof. smt(StdOrder.IntOrder.expr_gt0). qed.

lemma dvd2_pow2 (m : int) : 1 <= m => 2 %| 2 ^ m.
proof. by move=> hm; rewrite -{1}expr1 dvdz_exp2l /#. qed.

lemma modz_cmp (m d : int) : 0 < d => 0 <= m %% d < d.
proof. smt(edivzP). qed.

lemma divz_cmp (d i m : int) : 0 < d => 0 <= i < m * d => 0 <= i %/ d < m.
proof. by move=> hd [hi1 hi2]; rewrite divz_ge0 // hi1 /= ltz_divLR. qed.

lemma bound_abs (i j : int) : 0 <= i < j => 0 <= i < `|j|.
proof. smt(). qed.

op int_bit (x i : int) : bool = (x %% modulus) %/ 2 ^ i %% 2 <> 0.

lemma of_intbE (x i : int) : (of_int x).[i] = (0 <= i < n /\ int_bit x i).
proof. by rewrite of_intwE. qed.

lemma int_bitMP x j k : 0 <= k => 0 <= j < n =>
  int_bit (x * 2 ^ k) j = (0 <= j - k < n /\ int_bit x (j - k)).
proof.
move=> ge0 hk [h0j hjn]; rewrite /int_bit modz_pow2_div 1:/# modz_dvd.
+ by apply dvd2_pow2 => /#.
case: (0 <= j - k < n) => [[hjk1 hjk2] | hjk] /=; last first.
+ have hlt : j < k by smt().
  have ->: k = (k - j - 1) + 1 + j by ring.
  rewrite exprD_nneg 1:/# 1:// -mulzA mulzK; 1: by smt(gt0_pow2).
  by rewrite exprD_nneg 1:/# //= expr1 -mulzA modzMl.
rewrite (modz_pow2_div n) 1:/# modz_dvd.
+ by apply dvd2_pow2 => /#.
have {1}-> : j = (j - k) + k by ring.
by rewrite exprD_nneg 1,2:// divzMpr 1:gt0_pow2.
qed.

lemma int_bitDP x j k : 0 <= x < modulus => 0 <= k => 0 <= j < n =>
  int_bit (x %/ 2 ^ k) j = (0 <= j + k < n /\ int_bit x (j + k)).
proof.
move=> ge0 hx hk [h0j hjn]; rewrite /int_bit.
rewrite !(modz_small _ modulus); 1,2: apply bound_abs; 2:done.
+ by apply divz_cmp; [apply gt0_pow2 | smt(gt0_pow2)].
case: (0 <= j + k < n) => hjk.
+ have {1}-> := divz_eq x (2 ^ (j + k)).
  have {1}-> := divz_eq (x %% 2 ^ (j + k)) (2 ^ k).
  pose xd := x %/ 2 ^ (j + k). pose xm := x %% 2 ^ (j + k).
  have -> : xd * 2 ^ (j + k) + (xm %/ 2 ^ k * 2 ^ k + xm %% 2 ^ k) =
         (xd * 2 ^ j + xm %/ 2 ^ k) * 2 ^ k + xm %% 2 ^ k.
  + by rewrite exprD_nneg 1,2://; ring.
  rewrite divzMDl. smt(gt0_pow2).
  rewrite (divz_small (xm %% 2 ^ k) (2 ^ k)).
  + apply bound_abs; apply modz_cmp; apply gt0_pow2.
  rewrite /= divzMDl. smt(gt0_pow2).
  rewrite (divz_small (xm %/ 2 ^ k) (2 ^ j)) 2://.
  apply bound_abs; apply divz_cmp; 1: by apply gt0_pow2.
  by rewrite -exprD_nneg 1,2://; apply modz_cmp; apply gt0_pow2.
rewrite /= (divz_small (x %/ 2 ^ k) (2 ^ j)) 2://.
apply bound_abs; apply divz_cmp; 1: by apply gt0_pow2.
by rewrite -exprD_nneg 1,2://; smt(StdOrder.IntOrder.ler_weexpn2l).
qed.

lemma w2bits_zerow : w2bits zerow = nseq n false.
proof.
move=> ge0; apply/(eq_from_nth false); first by rewrite size_w2bits size_nseq; smt().
by move=> i; rewrite size_w2bits => hi; rewrite w2bitsE // zerowE nth_nseq.
qed.

lemma w2bits_onew : w2bits onew = nseq n true.
proof.
move=> ge0; apply/(eq_from_nth false); first by rewrite size_w2bits size_nseq; smt().
by move=> i; rewrite size_w2bits => hi; rewrite w2bitsE // onewE hi nth_nseq.
qed.

lemma to_uint_zerow : to_uint zerow = 0.
proof. by move=> ge0; rewrite /to_uint w2bits_zerow bs2int_nseq_false. qed.

lemma to_uint_onew : to_uint onew = modulus - 1.
proof. by move=> ge0; rewrite /to_uint w2bits_onew bs2int_nseq_true. qed.

lemma zerowP : zerow = of_int 0.
proof. by move=> ge0; rewrite -(to_uintK zerow) to_uint_zerow. qed.

lemma onewP : onew = of_int (modulus - 1).
proof. by move=> ge0; rewrite -(to_uintK onew) to_uint_onew. qed.

(* -------------------------------------------------------------------- *)
(* Signed interpretation.  The signed range needs a positive width, so
   the range/msb lemmas carry a [0 < n] hypothesis (vacuous at [word<:0>],
   the one-element word). *)
abbrev min_sint = - 2 ^ (n - 1).
abbrev max_sint =   2 ^ (n - 1) - 1.

op smod (i : int) : int = if 2 ^ (n - 1) <= i then i - modulus else i.
op to_sint (w : word<:n>) : int = smod (to_uint w).
op msb (w : word<:n>) : bool = 2 ^ (n - 1) <= to_uint w.

lemma half_modulus : 0 < n => 2 * 2 ^ (n - 1) = modulus.
proof. by move=> ge0 gt0; rewrite -exprS 1:/# /#. qed.

lemma gt0_half : 0 < n => 0 < 2 ^ (n - 1).
proof. by move=> ge0 gt0; rewrite StdOrder.IntOrder.expr_gt0. qed.

lemma to_sint_cmp (w : word<:n>) : 0 < n => min_sint <= to_sint w <= max_sint.
proof. by move=> ge0 gt0; rewrite /to_sint /smod; smt(to_uint_cmp half_modulus). qed.

lemma msbE (w : word<:n>) : 0 < n => msb w = w.[n - 1].
proof. by move=> ge0 gt0; rewrite /msb get_to_uint; smt(to_uint_cmp half_modulus). qed.

(* -------------------------------------------------------------------- *)
(* Arithmetic (ℤ/2ⁿ) operators: [+]/[*]/unary [-] lift the integer
   operations through [to_uint]/[of_int], i.e. act modulo [modulus].  The
   comm-ring structure is registered below over [word<:n+1>]. *)
op ( + ) (x y : word<:n>) : word<:n> = of_int (to_uint x + to_uint y).
op oppa  (x   : word<:n>) : word<:n> = of_int (- to_uint x).
op ( * ) (x y : word<:n>) : word<:n> = of_int (to_uint x * to_uint y).

lemma of_int_mod (x : int) : of_int (x %% modulus) = of_int x.
proof. by move=> ge0; rewrite /of_int modz_mod. qed.

lemma to_uintD (x y : word<:n>) : to_uint (x + y) = (to_uint x + to_uint y) %% modulus.
proof. by move=> ge0; rewrite /( + ) of_uintK. qed.

lemma to_uintM (x y : word<:n>) : to_uint (x * y) = (to_uint x * to_uint y) %% modulus.
proof. by move=> ge0; rewrite /( * ) of_uintK. qed.

lemma to_uintN (x : word<:n>) : to_uint (oppa x) = (- to_uint x) %% modulus.
proof. by move=> ge0; rewrite /oppa of_uintK. qed.

lemma of_intD (x y : int) : of_int (x + y) = of_int x + of_int y.
proof. by move=> ge0; rewrite to_uint_eq to_uintD !of_uintK modzDm. qed.

lemma of_intN (x : int) : of_int (- x) = oppa (of_int x).
proof. by move=> ge0; rewrite to_uint_eq to_uintN !of_uintK modzNm. qed.

lemma of_intM (x y : int) : of_int (x * y) = of_int x * of_int y.
proof. by move=> ge0; rewrite to_uint_eq to_uintM !of_uintK modzMm. qed.

(* -------------------------------------------------------------------- *)
(* Unsigned / signed comparisons. *)
op ( \ule ) (x y : word<:n>) = to_uint x <= to_uint y.
op ( \ult ) (x y : word<:n>) = to_uint x <  to_uint y.
op ( \sle ) (x y : word<:n>) = to_sint x <= to_sint y.
op ( \slt ) (x y : word<:n>) = to_sint x <  to_sint y.

lemma uleNgt (x y : word<:n>) : (x \ule y) = !(y \ult x).
proof. by move=> ge0; rewrite /( \ule ) /( \ult ) lezNgt. qed.

lemma ultNge (x y : word<:n>) : (x \ult y) = !(y \ule x).
proof. by move=> ge0; rewrite /( \ult ) /( \ule ) ltzNge. qed.

lemma sleNgt (x y : word<:n>) : (x \sle y) = !(y \slt x).
proof. by move=> ge0; rewrite /( \sle ) /( \slt ) lezNgt. qed.

lemma sltNge (x y : word<:n>) : (x \slt y) = !(y \sle x).
proof. by move=> ge0; rewrite /( \slt ) /( \sle ) ltzNge. qed.

(* -------------------------------------------------------------------- *)
(* Shifts and rotates.  All are bit reindexings: [ >>> ] logical right,
   [ <<< ] left, [ sar ] arithmetic right (sign-extends the top bit),
   [ ror ]/[ rol ] rotate.  Out-of-range bit reads give [false]. *)
op ( `>>>` ) (x : word<:n>) (i : int) : word<:n> = offunw (fun j => x.[j + i]).
op ( `<<<` ) (x : word<:n>) (i : int) : word<:n> = offunw (fun j => x.[j - i]).
op sar      (x : word<:n>) (i : int) : word<:n> = offunw (fun j => x.[min (n - 1) (j + i)]).
op ror      (x : word<:n>) (i : int) : word<:n> = offunw (fun j => x.[(j + i) %% n]).
op rol      (x : word<:n>) (i : int) : word<:n> = offunw (fun j => x.[(j - i) %% n]).

lemma shrwE (x : word<:n>) i j : 0 <= j < n => (x `>>>` i).[j] = x.[j + i].
proof. by move=> ge0 hj; rewrite offunwE hj. qed.

lemma shlwE (x : word<:n>) i j : 0 <= j < n => (x `<<<` i).[j] = x.[j - i].
proof. by move=> ge0 hj; rewrite offunwE hj. qed.

lemma sarwE (x : word<:n>) i j : 0 <= j < n => (sar x i).[j] = x.[min (n - 1) (j + i)].
proof. by move=> ge0 hj; rewrite offunwE hj. qed.

lemma rorwE (x : word<:n>) i j : 0 <= j < n => (ror x i).[j] = x.[(j + i) %% n].
proof. by move=> ge0 hj; rewrite offunwE hj. qed.

lemma rolwE (x : word<:n>) i j : 0 <= j < n => (rol x i).[j] = x.[(j - i) %% n].
proof. by move=> ge0 hj; rewrite offunwE hj. qed.

(* -------------------------------------------------------------------- *)
(* Shift <-> arithmetic:  [ >>> ] is unsigned division by [2^i]. *)
(* [ >>> ] is unsigned division, [ <<< ] is (truncated) multiplication.
   Both reduce to [int_bitDP] / [int_bitMP] via [of_int]. *)
lemma shlMP x k : 0 <= k => (of_int x `<<<` k) = of_int (x * 2 ^ k).
proof.
move=> ge0 hk; apply/wordP => j hj.
by rewrite (shlwE _ _ _ hj) !of_intbE hj /= -(int_bitMP x j k hk hj).
qed.

lemma shrDP x k : 0 <= k => (of_int x `>>>` k) = of_int (x %% modulus %/ 2 ^ k).
proof.
move=> ge0 hk; rewrite -(of_int_mod x); apply/wordP => j hj.
rewrite (shrwE _ _ _ hj) !of_intbE hj /= -(int_bitDP (x %% modulus) j k _ hk hj) //.
by apply modz_cmp; apply gt0_modulus.
qed.

lemma to_uint_shl (w : word<:n>) i :
  0 <= i => to_uint (w `<<<` i) = (to_uint w * 2 ^ i) %% modulus.
proof. by move=> ge0 hi; rewrite -{1}(to_uintK w) shlMP // of_uintK. qed.

lemma to_uint_shr (w : word<:n>) i :
  0 <= i => to_uint (w `>>>` i) = to_uint w %/ 2 ^ i.
proof.
move=> ge0 hi; rewrite -{1}(to_uintK w) shrDP // of_uintK.
rewrite (modz_small (to_uint w)).
+ by apply bound_abs; apply to_uint_cmp.
rewrite modz_small 2://.
apply bound_abs; apply divz_cmp; 1: by apply gt0_pow2.
smt(to_uint_cmp gt0_pow2).
qed.

end section IWordNum.

(* ==================================================================== *)
(* Arithmetic comm-ring structure (ℤ/2ⁿ⁺¹).  Registered over [word<:n+1>]
   for the same positivity reason as the boolean ring: [oner_neq0] needs a
   modulus [> 1].  [ComRingDflInv] supplies the (choice-based) unit/inverse
   and discharges [mulVr]/[unitP]/[unitout]; only the ring axioms remain. *)
section IWordRingA.
declare index {n}.

clone import Ring.ComRingDflInv as WRingA with
  type t     <- word<:n+1>,
  op   zeror <- of_int[:n+1] 0,
  op   ( + ) <- ( + )[:n+1],
  op   [ - ] <- oppa[:n+1],
  op   oner  <- of_int[:n+1] 1,
  op   ( * ) <- ( * )[:n+1]
  proof *.
realize addrA.
proof. by move=> ge0 x y z; rewrite to_uint_eq !to_uintD modzDmr modzDml addrA. qed.
realize addrC.
proof. by move=> ge0 x y; rewrite to_uint_eq !to_uintD addzC. qed.
realize add0r.
proof.
move=> ge0 x; rewrite to_uint_eq to_uintD of_uintK mod0z /=.
by rewrite pmod_small 1:to_uint_cmp.
qed.
realize addNr.
proof. by move=> ge0 x; rewrite to_uint_eq to_uintD to_uintN of_uintK modzDml addNz. qed.
realize oner_neq0.
proof.
move=> ge0; rewrite to_uint_eq !of_uintK.
have h1 : 2 ^ (n + 1) = 2 * 2 ^ n by rewrite exprS //.
have h2 : 0 < 2 ^ n by rewrite StdOrder.IntOrder.expr_gt0.
smt().
qed.
realize mulrA.
proof. by move=> ge0 x y z; rewrite to_uint_eq !to_uintM modzMmr modzMml mulrA. qed.
realize mulrC.
proof. by move=> ge0 x y; rewrite to_uint_eq !to_uintM mulzC. qed.
realize mul1r.
proof.
move=> ge0 x; rewrite to_uint_eq to_uintM of_uintK.
by rewrite modzMml /= pmod_small 1:to_uint_cmp.
qed.
realize mulrDl.
proof.
move=> ge0 x y z; rewrite to_uint_eq to_uintM !to_uintD !to_uintM.
by rewrite modzMml modzDml modzDmr mulzDl.
qed.
end section IWordRingA.

