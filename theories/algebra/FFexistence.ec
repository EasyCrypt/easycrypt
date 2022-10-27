(* ==================================================================== *)
require import AllCore List Ring Int IntMin IntDiv Poly.
require import StdBigop StdPoly Binomial Counting Perms.
(*---*) import StdOrder.IntOrder.


theory SIterOp.

  op siter ['a] (n : int) (f : int -> (int -> 'a) -> 'a) (x : 'a) : 'a =
    (iteri n (fun k m i => if i = k + 1 then f i m else m i) (fun (_ : int) => x)) n.

  lemma siter0 ['a] n f (x : 'a) :
    n <= 0 =>
    siter n f x = x.
  proof. by rewrite /siter => ?; rewrite iteri0. qed.

  lemma siterS ['a] n f (x : 'a) :
    0 <= n =>
    siter (n + 1) f x =
    f (n + 1) (fun k => if (0 <= k <= n) then siter k f x else x).
  proof.
    move => le0n; rewrite /siter; pose g:= (fun k m i => if i = k + 1 then f i m else m i); pose c:= (fun _ => x).
    have iteri_eq: forall i j , iteri i g c j = if (0 <= j <= i) then iteri j g c j else x; last first.
    + by rewrite iteriS // {1}/g /=; congr; apply/fun_ext => k /=; apply/iteri_eq.
    move => i j; case (0 <= i) => [le0i|/ltrNge lti0]; last first.
    + rewrite iteri0 //; [by apply/ltzW|]; rewrite {1}/c /=; case (0 <= j) => //= le0j.
      by rewrite lerNgt (ltr_le_trans _ _ _ lti0 le0j).
    move => {le0n}; elim: i le0i {1 3 4}i  (lerr i) j => [|i le0i IHi] j lej_ k.
    + rewrite iteri0 //; case (0 <= k) => [le0k|/ltrNge ltk0]; rewrite {1}/c //=.
      by case/ler_eqVlt: (ler_trans _ _ _ lej_ le0k) => [<<-/=|]; [rewrite iteri0|move/ltrNge => ->].
    case/ler_eqVlt: lej_ => [->>|/ltzS leji]; [|by apply/IHi].
    case (k = i + 1) => [->>|/ltr_total [/ltzS leki|lt_k]]; [by rewrite addr_ge0| |].
    + by rewrite iteriS // {1}/g ltr_eqF ?ltzS //= IHi // leki /= (ler_trans _ _ _ leki) //; apply/ltzW/ltzS.
    by rewrite iteriS // {1}/g gtr_eqF //= IHi // !(lerNgt k) lt_k /= (ler_lt_trans _ _ _ _ lt_k) //; apply/ltzW/ltzS.
  qed.

end SIterOp.


theory Counting_Argument.

  clone include SIterOp.
  clone import PolyReal.
  clone import Bigint.BIA.
  clone import Bigint.BIM.

  op PI (n : int) =
    siter n
      (fun k m =>
        polyXn k -
        PCA.big
          predT
          (fun a =>
            PCM.bigi
              predT
              (fun i => PCM.bigi predT (fun j => m i + polyC j%r) 0 (nth 0 a i) * polyC (1%r / (fact (nth 0 a i))%r))
              1 (k + 1))
          (allshapes k) )
      poly0.

  op I n q = floor (peval (PI n) q%r).

  lemma le0I n q :
    0 < n =>
    1 < q =>
    0 <= I n q.
  proof.
    admit.
  qed.

  lemma eqI n q :
    0 < n =>
    1 < q =>
    BIA.big
      predT
      (fun a =>
        BIM.bigi
          predT
          (fun d => bin (I d q + nth 0 a d - 1) (nth 0 a d))
          1 (n + 1))
      (allshapes n) =
    q ^ n.
  proof.
    admit.
  qed.

  lemma lt0I n :
    0 < n =>
    exists (q : int) , forall r , q <= r => 0 < I n r.
  proof.
    admit.
  qed.

end Counting_Argument.
