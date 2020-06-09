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
proof. by move=> le0n; rewrite BIM.big_geq // ler_naddl. qed.

lemma factS (n : int) : 0 <= n => fact (n+1) = (n+1) * (fact n).
proof.
move=> ge1n; rewrite BIM.big_int_recr //=.
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

(* -------------------------------------------------------------------- *)
(*
op multn (s : int list) : int =
  let k = fun i => nth 0 s i in
  BIM.bigi predT
    (fun i => bin (BIM.bigi predT k 0 (i+1)) (k i))
    0 (size s).
*)
