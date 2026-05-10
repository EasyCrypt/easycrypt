(* -------------------------------------------------------------------- *)
require import AllCore List.
require import TcMonoid TcRing TcBigop TcBigalg TcInt TcNumber TcReal.

(* ==================================================================== *)
(* TC port of [theories/algebra/Binomial.ec].                            *)
(* ==================================================================== *)

(* -------------------------------------------------------------------- *)
op fact (n : int) = bigiM predT idfun 1 (n+1).

lemma fact0 (n : int) : n <= 0 => fact n = 1.
proof.
move=> le0n; rewrite /fact /bigiM /bigM range_geq /#.
qed.

lemma factS (n : int) : 0 <= n => fact (n+1) = (n+1) * (fact n).
proof.
move=> ge0_n; rewrite /fact /bigiM /bigM rangeSr 1:/# -cats1 big_cat big_seq1 /=.
by rewrite mulrC.
qed.

lemma fact1 : fact 1 = 1.
proof. by rewrite -{1}[1]add0r factS //= fact0. qed.

(* -------------------------------------------------------------------- *)
op bin1 (s : int list) =
  1 :: (map (fun i => nth 0 s i + nth 0 s (i+1)) (range 0 (size s))).

op bin (n k : int) : int =
  if n < 0 \/ k < 0 then 0 else nth 0 (iter n bin1 [1]) k.

(* -------------------------------------------------------------------- *)
lemma size_bin1 (s : int list) : size (bin1 s) = 1 + size s.
proof. by rewrite /bin1 /= size_map size_range /#. qed.

lemma size_bin (s : int list) n : 0 <= n =>
  size (iter n bin1 s) = n + size s.
proof.
elim: n => [|n ge0_n ih]; first by rewrite iter0.
by rewrite iterS // size_bin1 ih; ring.
qed.

(* -------------------------------------------------------------------- *)
lemma binp (n k : int) :
  0 <= n => 0 <= k => bin n k = nth 0 (iter n bin1 [1]) k.
proof. by rewrite /bin !ltrNge=> -> ->. qed.

lemma bin_lt0l (n m : int) : n < 0 => bin n m = 0.
proof. by move=> @/bin ->. qed.

lemma bin_lt0r (n m : int) : m < 0 => bin n m = 0.
proof. by move=> @/bin ->. qed.

lemma bin0 (n : int) : 0 <= n => bin n 0 = 1.
proof.
move=> ge0_n; rewrite binp //; elim/natind: n ge0_n=> n h.
+ by rewrite iter0.
+ by move=> ih; rewrite iterS.
qed.

lemma binn (n : int) : 0 <= n => bin n n = 1.
proof.
move=> ge0_n; rewrite binp //; pose s := iter _ _ _.
have sz_s: size s = n + 1 by rewrite size_bin.
rewrite (_ : n = n + 1 - 1) // -sz_s nth_last /s.
elim: {s sz_s} n ge0_n 0; first by rewrite iter0.
move=> i ge0_i ih k; rewrite iterS //.
pose s := iter _ _ _; rewrite /bin1 /=.
pose F i := nth 0 s i + nth 0 s (i + 1).
have ->: 1 = F ((size s) - 1).
+ by rewrite /F nth_last ih nth_default.
rewrite last_map (rangeSr _ (size s - 1)) 1:size_bin //.
by rewrite last_rcons.
qed.

lemma bin0n (m : int) : bin 0 m = b2i (m = 0).
proof. by rewrite /bin iter0 //=; case: (m = 0). qed.

lemma binSn n m : 0 <= n => 0 <= m =>
  bin (n + 1) (m + 1) = bin n (m + 1) + bin n m.
proof.
move=> ge0_n ge0_m; rewrite binp 1,2:/# iterS //.
pose s := iter n bin1 [1]; rewrite /bin1 -nth_behead //=.
case: (m < size s) => [lt_m_s|/lerNgt gt_m_s]; last first.
+ rewrite nth_default.
  * by rewrite size_map size_range /#.
  by rewrite !binp // ~-1:/# !nth_default ~-1://#.
rewrite (nth_map 0) 1:size_range /=; first by smt(size_ge0).
by rewrite !nth_range //= !binp //#.
qed.

lemma ge0_bin (n k : int) : 0 <= bin n k.
proof.
case: (n < 0 \/ k < 0) => [@/bin ->//|].
rewrite negb_or => -[/lezNgt ge0_n /lezNgt ge0_k].
elim: n ge0_n k ge0_k => [|n ge0_n ih] k ge0_k.
+ by rewrite bin0n b2i_ge0.
case: k ge0_k => [|k ge0_k _]; 1: rewrite bin0 //#.
have h1 := ih (k+1) _; first by smt().
have h2 := ih k _; first by smt().
by rewrite binSn //; smt().
qed.

lemma bin_gt (n k : int) : n < k => bin n k = 0.
proof.
move=> lt_nk; rewrite /bin; case _: (_ \/ _) => //=.
rewrite negb_or => -[ge0_n ge0_k].
by rewrite nth_out // size_bin /#.
qed.

(* ==================================================================== *)
(* Binomial theorem on a [comring] carrier. Mirrors the legacy           *)
(* [BinomialCoeffs] abstract theory but as a [section] over [t <:        *)
(* comring]: the [clone Bigalg.BigComRing as BCR with ...] dance         *)
(* disappears since [TcBigalg]'s lemmas are already polymorphic.        *)
(* ==================================================================== *)
section.
declare type t <: comring.

lemma binomial (x y : t) n : 0 <= n => exp (x + y) n =
  bigiA predT (fun i => intmul (exp x i * exp y (n - i)) (bin n i)) 0 (n + 1).
proof.
elim: n => [|i ge0_i ih].
+ by rewrite big_int1 /= !expr0 mul1r bin0 // mulr1z.
rewrite exprS // ih /= mulrDl 2!mulr_sumr.
rewrite (big_addn 1 _ (-1)) /= (big_int_recr (i+1)) 1:/# /=.
pose s1 := bigi _ _ _ _; rewrite binn // mulr1z.
rewrite !expr0 mulr1 -exprS // addrAC.
apply: eq_sym; rewrite (big_int_recr (i+1)) 1:/# /=.
rewrite binn 1:/# mulr1z !expr0 mulr1; congr.
apply: eq_sym; rewrite (big_int_recl _ 0) //=.
rewrite bin0 // mulr1z !expr0 mul1r -exprS // addrCA addrC; apply: eq_sym.
rewrite (big_int_recl _ 0) //= bin0 1:/# mulr1z !expr0 mul1r addrC.
congr; apply: eq_sym; rewrite /s1 => {s1}.
rewrite !(big_addn 1 _ (-1)) /= -big_split /=.
rewrite !big_seq &(eq_bigr) => /= j /mem_range rg_j.
rewrite mulrnAr ?ge0_bin mulrA -exprS 1:/# /= addrC.
rewrite mulrnAr ?ge0_bin mulrCA -exprS 1:/#.
rewrite addrAC opprB addrA.
by rewrite -mulrDz; congr; rewrite (binSn i (j-1)) 1,2:/#.
qed.

end section.

(* ==================================================================== *)
(* Specialisation at [real]: the binomial theorem with the real-valued  *)
(* binomial coefficient written via [%r]. Mirrors [BCR.binomial].       *)
(* ==================================================================== *)
(* TC equivalent of [RField.intmulr]: at carrier [real], [intmul x c =
   x * c%r]. Proved here since the legacy lives in [Real.ec:RField]. *)
lemma intmulr_real (x : real) (c : int) : intmul x c = x * c%r.
proof.
have h: forall cp, 0 <= cp => intmul x cp = x * cp%r.
+ elim=> /= [|cp ge0_cp ih]; first by rewrite mulr0z.
  by rewrite mulrS // ih fromintD mulrDr mulr1 addrC.
case: (lezWP c 0) => [le0c|_ /h //].
rewrite -{2}(@oppzK c) fromintN mulrN -h 1:/#.
by rewrite mulrNz opprK.
qed.

lemma binomial_r (x y : real) n : 0 <= n => (x + y) ^ n =
  bigiA predT (fun i => (bin n i)%r * (x ^ i * y ^ (n - i))) 0 (n + 1).
proof.
move=> ge0_n.
have h := binomial<:real> x y n ge0_n.
rewrite (_ : (x + y) ^ n =
  bigiA predT (fun i => intmul (x ^ i * y ^ (n - i)) (bin n i)) 0 (n + 1));
  first by exact h.
by apply: eq_bigr => /= k _; rewrite intmulr_real mulrC mulrA.
qed.
