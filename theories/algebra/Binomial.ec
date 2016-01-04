(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2016 - Inria
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
require import Pred Int IntExtra List Ring StdBigop StdOrder.
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
  if n < 0 || k < 0 then 0 else nth 0 (iter n bin1 [1]) k.

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

lemma bin0n (m : int) : bin 0 m = b2i (m = 0).
proof. by rewrite /bin iter0 //=; case: (m = 0). qed.

(*
Lemma binS n m : 'C(n.+1, m.+1) = 'C(n, m.+1) + 'C(n, m). Proof. by []. Qed.
*)

(* -------------------------------------------------------------------- *)
op multn (s : int list) : int =
  let k = fun i => nth 0 s i in
  BIM.bigi predT
    (fun i => bin (BIM.bigi predT k 0 (i+1)) (k i))
    0 (size s).
