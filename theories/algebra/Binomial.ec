(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
require import AllCore List Ring StdBigop StdOrder.
(*---*) import Bigint IntOrder.

(* -------------------------------------------------------------------- *)
op fact (n : int) = BIM.bigi predT idfun 1 (n+1).

lemma fact0 (n : int) : n <= 0 => fact n = 1.
proof. by move=> le0n; rewrite /fact BIM.big_geq // ler_naddl. qed.

lemma factS (n : int) : 0 <= n => fact (n+1) = (n+1) * (fact n).
proof.
move=> ge1n; rewrite /fact BIM.big_int_recr //=.
by apply/ler_addr. by rewrite IntID.mulrC.
qed.

lemma fact1 (n : int) : fact 1 = 1.
proof. by rewrite -{1}IntID.add0r factS //= fact0. qed.

(* -------------------------------------------------------------------- *)
op bin1 (s : int list) =
  1 :: (map (fun i => nth 0 s i + nth 0 s (i+1)) (range 0 (size s))).

op bin (n k : int) : int =
  if n < 0 \/ k < 0 then 0 else nth 0 (iter n bin1 [1]) k.

(* -------------------------------------------------------------------- *)
lemma size_bin1 (s : int list) : size (bin1 s) = 1 + size s.
proof.
by rewrite /bin1 /= size_map size_range subz0 ler_maxr ?size_ge0.
qed.

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
  by rewrite iter0. by move=> ih; rewrite iterS.
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
  * by rewrite size_map size_range /= ler_maxr ?size_ge0.
  by rewrite !binp // ~-1:/# !nth_default ~-1://#.
rewrite (nth_map 0) 1:size_range /= 1:ler_maxr // 1:size_ge0.
by rewrite !nth_range //= !binp //#.
qed.

lemma ge0_bin (n k : int) : 0 <= bin n k.
proof.
case: (n < 0 \/ k < 0) => [@/bin ->//|].
rewrite negb_or => -[/lezNgt ge0_n /lezNgt ge0_k].
elim: n ge0_n k ge0_k => [|n ge0_n ih] k ge0_k.
+ by rewrite bin0n b2i_ge0.
case: k ge0_k => [|k ge0_k _]; 1: rewrite bin0 //#.
by rewrite binSn // addr_ge0 &(ih) /#.
qed.

lemma bin_gt (n k : int) : n < k => bin n k = 0.
proof.
move=> lt_nk; rewrite /bin; case _: (_ \/ _) => //=.
rewrite negb_or -!lerNgt => -[ge0_n ge0_k].
by rewrite nth_out // size_bin //= ltzS ge0_k lerNgt.
qed.

(* -------------------------------------------------------------------- *)
abstract theory BinomialCoeffs.
type t.

clone import Ring.ComRing as R with type t <- t.
clear [R.* R.AddMonoid.* R.MulMonoid.*].

clone import Bigalg.BigComRing as BCR with
  type t <- t,
  pred CR.unit   <- R.unit,
    op CR.zeror  <- R.zeror,
    op CR.oner   <- R.oner,
    op CR.( + )  <- R.( + ),
    op CR.([-])  <- R.([-]),
    op CR.( * )  <- R.( * ),
    op CR.invr   <- R.invr,
    op CR.intmul <- R.intmul,
    op CR.ofint  <- R.ofint,
    op CR.exp    <- R.exp

    proof CR.*

    remove abbrev CR.(-)
    remove abbrev CR.(/).

realize CR.addrA      by exact/R.addrA     .
realize CR.addrC      by exact/R.addrC     .
realize CR.add0r      by exact/R.add0r     .
realize CR.addNr      by exact/R.addNr     .
realize CR.oner_neq0  by exact/R.oner_neq0 .
realize CR.mulrA      by exact/R.mulrA     .
realize CR.mulrC      by exact/R.mulrC     .
realize CR.mul1r      by exact/R.mul1r     .
realize CR.mulrDl     by exact/R.mulrDl    .
realize CR.mulVr      by exact/R.mulVr     .
realize CR.unitP      by exact/R.unitP     .
realize CR.unitout    by exact/R.unitout   .

clear [BCR.* BCR.BAdd.* BCR.BMul.*].

lemma binomial (x y : t) n : 0 <= n => exp (x + y) n =
  BAdd.bigi predT (fun i => intmul (exp x i * exp y (n - i)) (bin n i)) 0 (n + 1).
proof.
elim: n => [|i ge0_i ih].
+ by rewrite BAdd.big_int1 /= !expr0 mul1r bin0 // mulr1z.
rewrite exprS // ih /= mulrDl 2!BAdd.mulr_sumr.
rewrite (BAdd.big_addn 1 _ (-1)) /= (BAdd.big_int_recr (i+1)) 1:/# /=.
pose s1 := BAdd.bigi _ _ _ _; rewrite binn // mulr1z.
rewrite !expr0 mulr1 -exprS // addrAC.
apply: eq_sym; rewrite (BAdd.big_int_recr (i+1)) 1:/# /=.
rewrite binn 1:/# mulr1z !expr0 mulr1; congr.
apply: eq_sym; rewrite (BAdd.big_int_recl _ 0) //=.
rewrite bin0 // mulr1z !expr0 mul1r -exprS // addrCA addrC; apply: eq_sym.
rewrite (BAdd.big_int_recl _ 0) //= bin0 1:/# mulr1z !expr0 mul1r addrC.
congr; apply: eq_sym; rewrite /s1 => {s1}.
rewrite !(BAdd.big_addn 1 _ (-1)) /= -BAdd.big_split /=.
rewrite !BAdd.big_seq &(BAdd.eq_bigr) => /= j /mem_range rg_j.
rewrite mulrnAr ?ge0_bin mulrA -exprS 1:/# /= addrC.
rewrite mulrnAr ?ge0_bin mulrCA -exprS 1:/#.
rewrite IntID.addrAC IntID.opprB IntID.addrA.
by rewrite -mulrDz; congr; rewrite (binSn i (j-1)) 1,2:/#.
qed.
end BinomialCoeffs.

(* -------------------------------------------------------------------- *)
import RField.

theory BCR.
clone include BinomialCoeffs with
  type t <- real,

  pred R.unit   <- (fun x => x <> 0%r),
    op R.zeror  <- 0%r,
    op R.oner   <- 1%r,
    op R.( + )  <- Real.( + ),
    op R.([-])  <- Real.([-]),
    op R.( * )  <- Real.( * ),
    op R.invr   <- Real.inv,
    op R.intmul <- RField.intmul,
    op R.ofint  <- RField.ofint,
    op R.exp    <- RField.exp,

    op BCR.BAdd.big <- Bigreal.BRA.big<:'a>,
    op BCR.BMul.big <- Bigreal.BRM.big<:'a>

  proof *

  remove abbrev R.(-)
  remove abbrev R.(/)
  remove abbrev BCR.BAdd.bigi
  remove abbrev BCR.BMul.bigi

  rename "binomial" as "binomial_r".

realize R.addrA      by exact/RField.addrA     .
realize R.addrC      by exact/RField.addrC     .
realize R.add0r      by exact/RField.add0r     .
realize R.addNr      by exact/RField.addNr     .
realize R.oner_neq0  by exact/RField.oner_neq0 .
realize R.mulrA      by exact/RField.mulrA     .
realize R.mulrC      by exact/RField.mulrC     .
realize R.mul1r      by exact/RField.mul1r     .
realize R.mulrDl     by exact/RField.mulrDl    .
realize R.mulVr      by exact/RField.mulVr     .
realize R.unitP      by exact/RField.unitP     .
realize R.unitout    by exact/RField.unitout   .

lemma binomial (x y : real) n : 0 <= n => (x + y) ^ n =
  Bigreal.BRA.bigi predT (fun i => (bin n i)%r * (x ^ i * y ^ (n - i))) 0 (n + 1).
proof.
move=> ge0_n; have := binomial_r x y n ge0_n => ->.
by apply: Bigreal.BRA.eq_bigr=> /= k _; rewrite intmulr mulrC mulrA.
qed.
end BCR.
