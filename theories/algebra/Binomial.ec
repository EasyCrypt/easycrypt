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
  nth 0 (iter n bin1 []) k.

(* -------------------------------------------------------------------- *)
op multn (s : int list) : int =
  let k = fun i => nth 0 s i in
  BIM.bigi predT
    (fun i => bin (BIM.bigi predT k 0 (i+1)) (k i))
    0 (size s).
