(* -------------------------------------------------------------------- *)
(* Length-indexed bit words, built on top of [IArray]: a [ word<:n> ] wraps
   a [ bool array<:n> ] but reads [false] out of range (like [BitWord.eca]).
   The width [n] lives in the index; the derived layer is developed in a
   [declare index {n}] section (so ops/lemmas drop their [{n}] binder).

   Not yet ported (vs BitWord.eca / Jasmin's JWord):
   - the uniform distribution (DWord) -- blocked on an indexed
     counterpart of FinType/Distr;
   - division/remainder ([\udiv], [\umod], [\sdiv], [\smod]);
   - the [sar] law kit and JWord's [rol_xor] shift tricks;
   - richer [int_bit] machinery (splitting/recombination lemmas). *)

require import AllCore Bool IntDiv Ring StdOrder List BitEncoding.
import BS2Int.
require import IArray.

(* -------------------------------------------------------------------- *)
(* Signature. *)
type {n} word.

(* Model for the two axioms: [word<:n>] IS [bool array<:n>] (i.e.
   length-[n] bool lists), [ofword]/[mkword] the identity. *)
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
proof. by rewrite /"_.[_]". qed.

lemma get_in (w : word<:n>) i :
  0 <= i < n => w.[i] = (ofword w).[i].
proof. by move=> hi; rewrite getE (ifT _ _ _ hi). qed.

lemma get_out (w : word<:n>) i :
  !(0 <= i < n) => w.[i] = false.
proof. by move=> hi; rewrite getE (ifF _ _ _ hi). qed.

(* -------------------------------------------------------------------- *)
lemma wordP (w1 w2 : word<:n>) :
  (forall i, 0 <= i < n => w1.[i] = w2.[i]) <=> w1 = w2.
proof.
split=> [eqi|-> //]; rewrite -(ofwordK w1) -(ofwordK w2); congr.
apply/IArray.eq_from_get=> i hi; move: (eqi i hi).
by rewrite !getE hi.
qed.

lemma ofword_inj (w1 w2 : word<:n>) :
  ofword w1 = ofword w2 => w1 = w2.
proof. by move=> h; rewrite -(ofwordK w1) -(ofwordK w2) h. qed.

(* [mkwordK] is unconditional, so [mkword] is genuinely injective
   (unlike the subtype-based Word.eca, whose mkword collapses
   off-size lists). *)
lemma mkword_inj (a1 a2 : bool array<:n>) :
  mkword[:n] a1 = mkword[:n] a2 => a1 = a2.
proof. by move=> h; rewrite -(mkwordK[:n] a1) -(mkwordK[:n] a2) h. qed.

lemma wordW (P : word<:n> -> bool) :
  (forall a, P (mkword a)) => forall w, P w.
proof. by move=> ih w; rewrite -(ofwordK w); apply/ih. qed.

(* -------------------------------------------------------------------- *)
(* Bit-set, delegated to IArray's set layer. *)
op "_.[_<-_]" (w : word<:n>) (i : int) (b : bool) : word<:n> =
  mkword ((ofword w).[i <- b]).

lemma setE (w : word<:n>) (i : int) (b : bool) :
  w.[i <- b] = mkword ((ofword w).[i <- b]).
proof. by rewrite /"_.[_<-_]". qed.

lemma get_set_if (w : word<:n>) (x : bool) (i j : int) :
  w.[i <- x].[j] = if 0 <= i < n /\ j = i then x else w.[j].
proof.
rewrite getE setE mkwordK; case: (0 <= j < n) => hj.
+ by rewrite IArray.get_set_if getE; smt().
+ by rewrite getE hj /=; smt().
qed.

lemma get_set (w : word<:n>) (x : bool) (i j : int) :
  0 <= i < n => w.[i <- x].[j] = if j = i then x else w.[j].
proof. by move=> lt_in; rewrite get_set_if lt_in. qed.

lemma set_out (i : int) (x : bool) (w : word<:n>) :
  ! (0 <= i < n) => w.[i <- x] = w.
proof. by move=> Nlt_in; rewrite setE IArray.set_out // ofwordK. qed.

lemma set_neg (i : int) (a : bool) (w : word<:n>) :
  i < 0 => w.[i <- a] = w.
proof. by move=> lt0_i; rewrite set_out // lezNgt lt0_i. qed.

lemma set_above (i : int) (a : bool) (w : word<:n>) :
  n <= i => w.[i <- a] = w.
proof. by move=> le_ni; rewrite set_out // ltzNge le_ni. qed.

lemma set_set_if (w : word<:n>) (k k' : int) (x x' : bool) :
      w.[k <- x].[k' <- x']
   =  if   k = k'
      then w.[k' <- x']
      else w.[k' <- x'].[k <- x].
proof.
by apply/wordP=> i hi; case: (k = k') => h; rewrite !get_set_if; smt().
qed.

lemma set_set_eq (w : word<:n>) (k : int) (x x' : bool) :
  w.[k <- x].[k <- x'] = w.[k <- x'].
proof. by rewrite set_set_if. qed.

lemma set_set_swap (w : word<:n>) (k k' : int) (x x' : bool) :
  k <> k' => w.[k <- x].[k' <- x'] = w.[k' <- x'].[k <- x].
proof. by rewrite set_set_if => ->. qed.

(* -------------------------------------------------------------------- *)
op offunw (f : int -> bool) : word<:n> = mkword (offun[:n] f).

lemma offunwE (f : int -> bool) i :
  (offunw f).[i] = if 0 <= i < n then f i else false.
proof.
rewrite getE /offunw mkwordK.
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
proof. by rewrite offunwE if_same. qed.

lemma onewE i : (onew).[i] = (0 <= i < n).
proof. by rewrite offunwE; case: (0 <= i < n). qed.

lemma xorwE (w1 w2 : word<:n>) i :
  (w1 +^ w2).[i] = w1.[i] ^^ w2.[i].
proof.
rewrite offunwE; case: (0 <= i < n) => hi //=.
by rewrite !get_out // xor_false.
qed.

lemma andwE (w1 w2 : word<:n>) i :
  (andw w1 w2).[i] = (w1.[i] /\ w2.[i]).
proof.
rewrite offunwE; case: (0 <= i < n) => hi //=.
by rewrite !get_out.
qed.

lemma orwE (w1 w2 : word<:n>) i :
  (orw w1 w2).[i] = (w1.[i] \/ w2.[i]).
proof.
rewrite offunwE; case: (0 <= i < n) => hi //=.
by rewrite !get_out.
qed.

lemma invwE (w : word<:n>) i :
  0 <= i < n => (invw w).[i] = !w.[i].
proof. by move=> hi; rewrite offunwE hi. qed.

lemma oppwE (w : word<:n>) i : (oppw w).[i] = w.[i].
proof. by rewrite /oppw. qed.

lemma oppwK (w : word<:n>) : oppw w = w.
proof. by rewrite /oppw. qed.

hint rewrite bwordE : zerowE onewE xorwE andwE orwE invwE.

(* -------------------------------------------------------------------- *)
lemma onew_neq0 : 0 < n => onew <> zerow.
proof.
move=> gt0n; apply/negP => /wordP /(_ 0).
by rewrite !bwordE /= gt0n.
qed.

lemma xorw0 : right_id zerow ( +^ ).
proof. by move=> w; apply/wordP=> i _; rewrite !bwordE xor_false. qed.

lemma xorwA : associative (( +^ )).
proof. by move=> w1 w2 w3; apply/wordP=> i _; rewrite !bwordE xorA. qed.

lemma xorwC : commutative (( +^ )).
proof. by move=> w1 w2; apply/wordP=> i _; rewrite !bwordE xorC. qed.

lemma xorwK (w : word<:n>) : w +^ w = zerow.
proof. by apply/wordP=> i _; rewrite !bwordE xorK. qed.

lemma andw1 : right_id onew andw.
proof. by move=> w; apply/wordP=> i h; rewrite !bwordE h. qed.

lemma andwA : associative (andw).
proof. by move=> w1 w2 w3; apply/wordP=> i h; rewrite !bwordE andbA. qed.

lemma andwC : commutative (andw).
proof. by move=> w1 w2; apply/wordP=> i h; rewrite !bwordE andbC. qed.

lemma andwK : idempotent (andw).
proof. by move=> w; apply/wordP=> i h; rewrite !bwordE andbb. qed.

lemma andwDl : left_distributive (andw) ( +^ ).
proof.
move=> w1 w2 w3; apply/wordP=> i h; rewrite !bwordE.
by move: (w1.[i]) (w2.[i]) (w3.[i]) => b1 b2 b3; case: b1; case: b2; case: b3.
qed.

lemma andw0 (w : word<:n>) : andw w zerow = zerow.
proof. by apply/wordP=> i _; rewrite !bwordE andbF. qed.

lemma orwA : associative (orw).
proof. by move=> w1 w2 w3; apply/wordP=> i _; rewrite !bwordE orbA. qed.

lemma orwC : commutative (orw).
proof. by move=> w1 w2; apply/wordP=> i _; rewrite !bwordE orbC. qed.

lemma orwK : idempotent (orw).
proof. by move=> w; apply/wordP=> i _; rewrite !bwordE orbb. qed.

lemma orw0 (w : word<:n>) : orw w zerow = w.
proof. by apply/wordP=> i _; rewrite !bwordE orbF. qed.

lemma orw1 (w : word<:n>) : orw w onew = onew.
proof. by apply/wordP=> i h; rewrite !bwordE h orbT. qed.

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
realize addrA.     proof. by apply/xorwA. qed.
realize addrC.     proof. by apply/xorwC. qed.
realize add0r.     proof. by move=> x; rewrite xorwC xorw0. qed.
realize addNr.     proof. by move=> x; rewrite /oppw; apply/xorwK. qed.
realize oner_neq0. proof. by apply/onew_neq0; smt(ge0_index). qed.
realize mulrA.     proof. by apply/andwA. qed.
realize mulrC.     proof. by apply/andwC. qed.
realize mul1r.     proof. by move=> x; rewrite andwC andw1. qed.
realize mulrDl.    proof. by apply/andwDl. qed.
realize mulrr.     proof. by move=> x; apply/andwK. qed.
realize unitout.   proof. by move=> x hnu; apply/oppwK. qed.
realize mulVr.
proof. by move=> x; rewrite /unitw => hx; rewrite oppwK andwK; exact hx. qed.
realize unitP.
proof.
move=> x y; rewrite /unitw -wordP => h; rewrite -wordP => i hi.
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
proof. by rewrite /w2bits size_ofarr. qed.

lemma w2bitsE (w : word<:n>) i : 0 <= i < n => nth false (w2bits w) i = w.[i].
proof.
move=> hi; rewrite /w2bits get_in //= IArray.getE.
by rewrite (nth_change_dfl witness false) // size_ofarr.
qed.

lemma get_to_uint (w : word<:n>) i :
  w.[i] = (0 <= i < n /\ to_uint w %/ 2 ^ i %% 2 <> 0).
proof.
case: (0 <= i < n) => hi /=; last by rewrite get_out.
rewrite -w2bitsE // /to_uint -{1}(bs2intK (w2bits w)) size_w2bits.
by rewrite /int2bs nth_mkseq //= size_w2bits.
qed.

lemma gt0_modulus : 0 < modulus.
proof. by rewrite StdOrder.IntOrder.expr_gt0. qed.

lemma bits2wK (s : bool list) : size s = n => w2bits (bits2w s) = s.
proof. by move=> hs; rewrite /w2bits /bits2w mkwordK mkarrK. qed.

lemma w2bitsK (w : word<:n>) : bits2w (w2bits w) = w.
proof. by rewrite /bits2w /w2bits ofarrK ofwordK. qed.

lemma to_uint_cmp (w : word<:n>) : 0 <= to_uint w < modulus.
proof.
rewrite /to_uint; split; first by apply bs2int_ge0.
by move=> _; rewrite -(size_w2bits w) bs2int_le2Xs.
qed.

lemma of_uintK (x : int) : to_uint (of_int x) = x %% modulus.
proof.
have ge0 := ge0_index[:n]; rewrite /to_uint /of_int bits2wK.
- by rewrite size_int2bs; smt().
rewrite int2bsK //; smt(gt0_modulus modz_ge0 ltz_pmod).
qed.

lemma to_uintK (w : word<:n>) : of_int (to_uint w) = w.
proof.
rewrite /of_int pmod_small 1:to_uint_cmp.
by rewrite /to_uint -(size_w2bits w) bs2intK w2bitsK.
qed.

lemma to_uint_eq (w1 w2 : word<:n>) : (w1 = w2) <=> (to_uint w1 = to_uint w2).
proof. by split=> [->//|h]; rewrite -(to_uintK w1) -(to_uintK w2) h. qed.

(* Dual of [get_to_uint]: the bit of a numeral. *)
lemma of_intwE (x : int) i :
  (of_int x).[i] = (0 <= i < n /\ (x %% modulus) %/ 2 ^ i %% 2 <> 0).
proof.
rewrite get_to_uint; case: (0 <= i < n) => //= hi.
by rewrite of_uintK.
qed.

(* -------------------------------------------------------------------- *)
(* The [n]-bit slice of an integer, i.e. the value of bit [i] of [x] once
   [x] has been reduced modulo [modulus].  This is what indexing a word
   [(of_int x).[i]] computes; the two lemmas below are pure-integer facts
   about how multiplying / dividing by [2^k] shifts those bits.  The
   generic integer range facts they rely on (gt0_pow2, modz_cmp, ...)
   live in IntDiv. *)
op int_bit (x i : int) : bool = (x %% modulus) %/ 2 ^ i %% 2 <> 0.

lemma of_intbE (x i : int) : (of_int x).[i] = (0 <= i < n /\ int_bit x i).
proof. by rewrite of_intwE. qed.

lemma int_bitMP x j k : 0 <= k => 0 <= j < n =>
  int_bit (x * 2 ^ k) j = (0 <= j - k < n /\ int_bit x (j - k)).
proof.
move=> hk [h0j hjn]; rewrite /int_bit modz_pow2_div 1:/# modz_dvd.
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
move=> hx hk [h0j hjn]; rewrite /int_bit.
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
have ge0 := ge0_index[:n]; apply/(eq_from_nth false); first by rewrite size_w2bits size_nseq; smt().
by move=> i; rewrite size_w2bits => hi; rewrite w2bitsE // zerowE nth_nseq.
qed.

lemma w2bits_onew : w2bits onew = nseq n true.
proof.
have ge0 := ge0_index[:n]; apply/(eq_from_nth false); first by rewrite size_w2bits size_nseq; smt().
by move=> i; rewrite size_w2bits => hi; rewrite w2bitsE // onewE hi nth_nseq.
qed.

lemma to_uint_zerow : to_uint zerow = 0.
proof. by rewrite /to_uint w2bits_zerow bs2int_nseq_false. qed.

lemma to_uint_onew : to_uint onew = modulus - 1.
proof. by have ge0 := ge0_index[:n]; rewrite /to_uint w2bits_onew bs2int_nseq_true. qed.

lemma zerowP : zerow = of_int 0.
proof. by rewrite -(to_uintK zerow) to_uint_zerow. qed.

lemma onewP : onew = of_int (modulus - 1).
proof. by rewrite -(to_uintK onew) to_uint_onew. qed.

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
proof. by move=> gt0; rewrite -exprS 1:/# /#. qed.

lemma gt0_half : 0 < n => 0 < 2 ^ (n - 1).
proof. by move=> gt0; rewrite StdOrder.IntOrder.expr_gt0. qed.

lemma to_sint_cmp (w : word<:n>) : 0 < n => min_sint <= to_sint w <= max_sint.
proof. by move=> gt0; rewrite /to_sint /smod; smt(to_uint_cmp half_modulus). qed.

(* The 2^(n-1) power is generalized away before any arithmetic step, so
   no prover ever sees an exponential (CI provers rejected the one-shot
   smt of the previous version). *)
lemma msbE (w : word<:n>) : 0 < n => msb w = w.[n - 1].
proof.
move=> gt0; rewrite /msb get_to_uint.
have -> /=: 0 <= n - 1 < n by smt().
have hcmp: 0 <= to_uint w < 2 * 2 ^ (n - 1).
- by rewrite half_modulus //; apply/to_uint_cmp.
move: hcmp (gt0_half gt0); move: (2 ^ (n - 1)) => p hcmp gt0_p.
rewrite modz_small.
- by rewrite /= divz_ge0 //= ltz_divLR //= (mulzC 2) /#.
rewrite eq_iff -{1}(mul1r p) -lez_divRL //.
smt(divz_ge0 ltz_divLR).
qed.

(* -------------------------------------------------------------------- *)
(* Arithmetic (ℤ/2ⁿ) operators: [+]/[*]/unary [-] lift the integer
   operations through [to_uint]/[of_int], i.e. act modulo [modulus].  The
   comm-ring structure is registered below over [word<:n+1>]. *)
op ( + ) (x y : word<:n>) : word<:n> = of_int (to_uint x + to_uint y).
op oppa  (x   : word<:n>) : word<:n> = of_int (- to_uint x).
op ( * ) (x y : word<:n>) : word<:n> = of_int (to_uint x * to_uint y).

lemma of_int_mod (x : int) : of_int (x %% modulus) = of_int x.
proof. by rewrite /of_int modz_mod. qed.

lemma to_uintD (x y : word<:n>) : to_uint (x + y) = (to_uint x + to_uint y) %% modulus.
proof. by rewrite /( + ) of_uintK. qed.

lemma to_uintM (x y : word<:n>) : to_uint (x * y) = (to_uint x * to_uint y) %% modulus.
proof. by rewrite /( * ) of_uintK. qed.

lemma to_uintN (x : word<:n>) : to_uint (oppa x) = (- to_uint x) %% modulus.
proof. by rewrite /oppa of_uintK. qed.

lemma of_intD (x y : int) : of_int (x + y) = of_int x + of_int y.
proof. by rewrite to_uint_eq to_uintD !of_uintK modzDm. qed.

lemma of_intN (x : int) : of_int (- x) = oppa (of_int x).
proof. by rewrite to_uint_eq to_uintN !of_uintK modzNm. qed.

lemma of_intM (x y : int) : of_int (x * y) = of_int x * of_int y.
proof. by rewrite to_uint_eq to_uintM !of_uintK modzMm. qed.

(* -------------------------------------------------------------------- *)
(* Unsigned / signed comparisons. *)
op ( \ule ) (x y : word<:n>) = to_uint x <= to_uint y.
op ( \ult ) (x y : word<:n>) = to_uint x <  to_uint y.
op ( \sle ) (x y : word<:n>) = to_sint x <= to_sint y.
op ( \slt ) (x y : word<:n>) = to_sint x <  to_sint y.

lemma uleNgt (x y : word<:n>) : (x \ule y) = !(y \ult x).
proof. by rewrite /( \ule ) /( \ult ) lezNgt. qed.

lemma ultNge (x y : word<:n>) : (x \ult y) = !(y \ule x).
proof. by rewrite /( \ult ) /( \ule ) ltzNge. qed.

lemma sleNgt (x y : word<:n>) : (x \sle y) = !(y \slt x).
proof. by rewrite /( \sle ) /( \slt ) lezNgt. qed.

lemma sltNge (x y : word<:n>) : (x \slt y) = !(y \sle x).
proof. by rewrite /( \slt ) /( \sle ) ltzNge. qed.

(* -------------------------------------------------------------------- *)
(* Order theory of the unsigned comparisons. *)
lemma ule_refl (x : word<:n>) : x \ule x.
proof. by rewrite /( \ule ). qed.

lemma ule_trans (y x z : word<:n>) : x \ule y => y \ule z => x \ule z.
proof. by rewrite /( \ule ); apply lez_trans. qed.

lemma ule_anti (x y : word<:n>) : x \ule y => y \ule x => x = y.
proof.
by rewrite /( \ule ) => h1 h2; rewrite to_uint_eq eqz_leq h1 h2.
qed.

lemma ule_total (x y : word<:n>) : x \ule y \/ y \ule x.
proof. by rewrite /( \ule ); exact lez_total. qed.

lemma ult_irr (x : word<:n>) : ! (x \ult x).
proof. by rewrite /( \ult ) ltzz. qed.

lemma ultW (x y : word<:n>) : x \ult y => x \ule y.
proof. by rewrite /( \ult ) /( \ule ); apply ltzW. qed.

(* -------------------------------------------------------------------- *)
(* Subtraction. *)
abbrev ( - ) (x y : word<:n>) : word<:n> = x + oppa y.

lemma to_uintD_small (x y : word<:n>) :
  to_uint x + to_uint y < modulus =>
  to_uint (x + y) = to_uint x + to_uint y.
proof. by move=> h; rewrite to_uintD modz_small //; smt(to_uint_cmp). qed.

lemma to_uintB (x y : word<:n>) :
  y \ule x => to_uint (x - y) = to_uint x - to_uint y.
proof.
rewrite /( \ule ) => hle.
by rewrite to_uintD to_uintN modzDmr modz_small //; smt(to_uint_cmp).
qed.

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
proof. by move=> hj; rewrite offunwE hj. qed.

lemma shlwE (x : word<:n>) i j : 0 <= j < n => (x `<<<` i).[j] = x.[j - i].
proof. by move=> hj; rewrite offunwE hj. qed.

lemma sarwE (x : word<:n>) i j : 0 <= j < n => (sar x i).[j] = x.[min (n - 1) (j + i)].
proof. by move=> hj; rewrite offunwE hj. qed.

lemma rorwE (x : word<:n>) i j : 0 <= j < n => (ror x i).[j] = x.[(j + i) %% n].
proof. by move=> hj; rewrite offunwE hj. qed.

lemma rolwE (x : word<:n>) i j : 0 <= j < n => (rol x i).[j] = x.[(j - i) %% n].
proof. by move=> hj; rewrite offunwE hj. qed.

(* -------------------------------------------------------------------- *)
(* Shift <-> arithmetic:  [ >>> ] is unsigned division by [2^i]. *)
(* [ >>> ] is unsigned division, [ <<< ] is (truncated) multiplication.
   Both reduce to [int_bitDP] / [int_bitMP] via [of_int]. *)
lemma shlMP x k : 0 <= k => (of_int x `<<<` k) = of_int (x * 2 ^ k).
proof.
move=> hk; apply/wordP => j hj.
by rewrite (shlwE _ _ _ hj) !of_intbE hj /= -(int_bitMP x j k hk hj).
qed.

lemma shrDP x k : 0 <= k => (of_int x `>>>` k) = of_int (x %% modulus %/ 2 ^ k).
proof.
move=> hk; rewrite -(of_int_mod x); apply/wordP => j hj.
rewrite (shrwE _ _ _ hj) !of_intbE hj /= -(int_bitDP (x %% modulus) j k _ hk hj) //.
by apply modz_cmp; apply gt0_modulus.
qed.

lemma to_uint_shl (w : word<:n>) i :
  0 <= i => to_uint (w `<<<` i) = (to_uint w * 2 ^ i) %% modulus.
proof. by move=> hi; rewrite -{1}(to_uintK w) shlMP // of_uintK. qed.

lemma to_uint_shr (w : word<:n>) i :
  0 <= i => to_uint (w `>>>` i) = to_uint w %/ 2 ^ i.
proof.
move=> hi; rewrite -{1}(to_uintK w) shrDP // of_uintK.
rewrite (modz_small (to_uint w)).
+ by apply bound_abs; apply to_uint_cmp.
rewrite modz_small 2://.
apply bound_abs; apply divz_cmp; 1: by apply gt0_pow2.
smt(to_uint_cmp gt0_pow2).
qed.

(* -------------------------------------------------------------------- *)
(* Shift-by-zero, shift composition, rotate normalization/inverses.
   None of these need [0 < n]: at width 0, [%% 0] is the identity and
   [wordP]'s quantification is vacuous. *)
lemma shrw0 (x : word<:n>) : x `>>>` 0 = x.
proof. by apply/wordP=> i hi; rewrite shrwE // addz0. qed.

lemma shlw0 (x : word<:n>) : x `<<<` 0 = x.
proof. by apply/wordP=> i hi; rewrite shlwE // subz0. qed.

lemma shrw_add (x : word<:n>) (i j : int) :
  0 <= i => 0 <= j => x `>>>` i `>>>` j = x `>>>` (i + j).
proof.
move=> hi hj; apply/wordP=> k hk.
rewrite /( `>>>` ) !offunwE hk /= offunwE.
case: (0 <= k + j < n) => hkj /=; first by congr; ring.
by rewrite get_out /#.
qed.

lemma shlw_add (x : word<:n>) (i j : int) :
  0 <= i => 0 <= j => x `<<<` i `<<<` j = x `<<<` (i + j).
proof.
move=> hi hj; apply/wordP=> k hk.
rewrite /( `<<<` ) !offunwE hk /= offunwE.
case: (0 <= k - j < n) => hkj /=; first by congr; ring.
by rewrite get_out /#.
qed.

lemma rorw_mod (x : word<:n>) (i : int) : ror x (i %% n) = ror x i.
proof. by apply/wordP=> k hk; rewrite !rorwE // modzDmr. qed.

lemma rolw_mod (x : word<:n>) (i : int) : rol x (i %% n) = rol x i.
proof.
apply/wordP=> k hk; rewrite !rolwE //; congr.
by rewrite -{1}(modz_small k n) 1:/# modzBm.
qed.

lemma rorwK (x : word<:n>) (i : int) : rol (ror x i) i = x.
proof.
apply/wordP=> k hk; rewrite rolwE // rorwE; first by smt(modz_cmp).
by congr; rewrite modzDml; smt(modz_small).
qed.

lemma rolwK (x : word<:n>) (i : int) : ror (rol x i) i = x.
proof.
apply/wordP=> k hk; rewrite rorwE // rolwE; first by smt(modz_cmp).
by congr; rewrite modzDml; smt(modz_small).
qed.

(* -------------------------------------------------------------------- *)
(* The modular ring laws, family-wide (they hold at EVERY width,
   including the trivial ring [word<:0>]), plus an iterated-product
   exponent: the obligations of the [warith] instance below. *)
lemma waddr0 (x : word<:n>) : x + of_int 0 = x.
proof. by rewrite to_uint_eq to_uintD of_uintK mod0z /= pmod_small 1:to_uint_cmp. qed.

lemma waddrA (x y z : word<:n>) : x + (y + z) = (x + y) + z.
proof. by rewrite to_uint_eq !to_uintD modzDmr modzDml addzA. qed.

lemma waddrC (x y : word<:n>) : x + y = y + x.
proof. by rewrite to_uint_eq !to_uintD addzC. qed.

lemma waddrN (x : word<:n>) : x + oppa x = of_int 0.
proof. by rewrite to_uint_eq to_uintD to_uintN of_uintK modzDmr addzN. qed.

lemma wmulr1 (x : word<:n>) : x * of_int 1 = x.
proof. by rewrite to_uint_eq to_uintM of_uintK modzMmr /= pmod_small 1:to_uint_cmp. qed.

lemma wmulrA (x y z : word<:n>) : x * (y * z) = (x * y) * z.
proof. by rewrite to_uint_eq !to_uintM modzMmr modzMml mulzA. qed.

lemma wmulrC (x y : word<:n>) : x * y = y * x.
proof. by rewrite to_uint_eq !to_uintM mulzC. qed.

lemma wmulrDl (x y z : word<:n>) : (x + y) * z = x * z + y * z.
proof.
by rewrite to_uint_eq to_uintM !to_uintD !to_uintM modzMml modzDml modzDmr mulzDl.
qed.

op wexp (x : word<:n>) (k : int) : word<:n> =
  iter k (fun (y : word<:n>) => x * y) (of_int 1).

lemma wexp0 (x : word<:n>) : wexp x 0 = of_int 1.
proof. by rewrite /wexp iter0. qed.

lemma wexpS (x : word<:n>) (i : int) :
  0 <= i => wexp x (i + 1) = x * wexp x i.
proof. by move=> ge0i; rewrite /wexp iterS. qed.

end section IWordNum.

(* ==================================================================== *)
(* Arithmetic comm-ring THEORY (ℤ/2ⁿ⁺¹).  The clone lives at
   [word<:n+1>] because [Ring.ComRing] is a non-trivial-ring theory
   ([oner_neq0] needs a modulus [> 1]); the [warith] tactic INSTANCE
   below is family-wide and does not go through this clone.
   [ComRingDflInv] supplies the (choice-based) unit/inverse and
   discharges [mulVr]/[unitP]/[unitout]; only the ring axioms remain. *)
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
proof. by move=> x y z; rewrite to_uint_eq !to_uintD modzDmr modzDml addrA. qed.
realize addrC.
proof. by move=> x y; rewrite to_uint_eq !to_uintD addzC. qed.
realize add0r.
proof.
move=> x; rewrite to_uint_eq to_uintD of_uintK mod0z /=.
by rewrite pmod_small 1:to_uint_cmp.
qed.
realize addNr.
proof. by move=> x; rewrite to_uint_eq to_uintD to_uintN of_uintK modzDml addNz. qed.
realize oner_neq0.
proof.
have ge0 := ge0_index[:n]; rewrite to_uint_eq !of_uintK.
have h1 : 2 ^ (n + 1) = 2 * 2 ^ n by rewrite exprS //.
have h2 : 0 < 2 ^ n by rewrite StdOrder.IntOrder.expr_gt0.
smt().
qed.
realize mulrA.
proof. by move=> x y z; rewrite to_uint_eq !to_uintM modzMmr modzMml mulrA. qed.
realize mulrC.
proof. by move=> x y; rewrite to_uint_eq !to_uintM mulzC. qed.
realize mul1r.
proof.
move=> x; rewrite to_uint_eq to_uintM of_uintK.
by rewrite modzMml /= pmod_small 1:to_uint_cmp.
qed.
realize mulrDl.
proof.
move=> x y z; rewrite to_uint_eq to_uintM !to_uintD !to_uintM.
by rewrite modzMml modzDml modzDmr mulzDl.
qed.

end section IWordRingA.

(* The BoolRing clone registers its (anonymous) instance on the
   carrier [word<:n+1>], and instance lookup returns the first match:
   the arithmetic structure would be unreachable by the [ring] tactic.
   Register it NAMED and FAMILY-WIDE: [ring [warith]] selects ℤ/2ⁿ at
   any width -- concrete, symbolic [word<:k+1>], bare symbolic
   [word<:m>], and even the trivial ring [word<:0>] (ring instances do
   not require [oner_neq0]: the tactic's certificates are purely
   equational).  Bare [ring] keeps selecting the boolean structure. *)
op zeroa {n} : word<:n> = of_int 0.
op onea  {n} : word<:n> = of_int 1.

instance ring [warith] with {n} word<:n>
  op rzero = zeroa
  op rone  = onea
  op add   = ( + )
  op mul   = ( * )
  op opp   = oppa
  op expr  = wexp
  op ofint = of_int

  proof addr0     by exact (waddr0[:n])
  proof addrA     by exact (waddrA[:n])
  proof addrC     by exact (waddrC[:n])
  proof addrN     by exact (waddrN[:n])
  proof mulr1     by exact (wmulr1[:n])
  proof mulrA     by exact (wmulrA[:n])
  proof mulrC     by exact (wmulrC[:n])
  proof mulrDl    by exact (wmulrDl[:n])
  proof expr0     by exact (wexp0[:n])
  proof exprS     by exact (wexpS[:n])
  proof ofint0    by rewrite /zeroa
  proof ofint1    by rewrite /onea
  proof ofintS    by (move=> i _; rewrite /onea addzC of_intD)
  proof ofintN    by exact (of_intN[:n]).

