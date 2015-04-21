(* --------------------------------------------------------------------
 * Copyright (c) - 2012-2015 - IMDEA Software Institute and INRIA
 * Distributed under the terms of the CeCILL-B licence.
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
require import Pred.
require import Fun.
require import Int.
require import NewList.
require import Ring.

(* -------------------------------------------------------------------- *)
theory Comoid.
  type comoid.

  op I     : comoid.
  op ( * ) : comoid -> comoid -> comoid.

  axiom addmA (x y z : comoid): x * (y * z) = (x * y) * z.
  axiom addmC (x y   : comoid): x * y = y * x.
  axiom add0m (x     : comoid): I * x = x.
  lemma addm0 (x     : comoid): x * I = x by smt.

  lemma addmCA (x y z : comoid): (x * y) * z = (x * z) * y.
  proof. by rewrite -addmA (addmC y) addmA. qed.

  lemma addmAC (x y z : comoid): x * (y * z) = y * (x * z).
  proof. by rewrite addmA (addmC x) -addmA. qed.

  lemma addmACA (x y z t : comoid): (x * y) * (z * t) = (x * z) * (y * t).
  proof. by rewrite addmA -(addmA x) (addmC y) !addmA. qed.
end Comoid.

(* -------------------------------------------------------------------- *)
theory Bigop.
  op big ['a 'b] (id : 'a) (op_ : 'a -> 'a -> 'a) (s : 'b list) P F =
    foldr op_ id (map F (filter P s)).
end Bigop.

(* -------------------------------------------------------------------- *)
theory BigComoid.
  clone export Comoid.
  (*-*) import Iota.

  op big (s : 'a list) P F = Bigop.big I Comoid.( * ) s P F.

  lemma nosmt bigE (s : 'a list) P F:
    big s P F = foldr Comoid.( * ) I (map F (filter P s)).
  proof. by []. qed.

  lemma nosmt big_nil P (F : 'a -> comoid): big [] P F = I.
  proof. by []. qed.

  lemma nosmt big_cons i r P (F : 'a -> comoid):
    big (i :: r) P F = if P i then (F i) * (big r P F) else (big r P F).
  proof. by rewrite (bigE (i :: r)) /=; case (P i). qed.

  (* -------------------------------------------------------------------- *)
  (*                      Induction principle                             *)
  (* -------------------------------------------------------------------- *)
  lemma nosmt big_rec (K : comoid -> bool) r P (F : 'a -> comoid):
    K I => (forall i x, P i => K x => K (F i * x)) => K (big r P F).
  proof.
    move=> Kidx Kop; elim r => //= i r; rewrite big_cons.
    by case (P i) => //=; apply Kop.
  qed.

  lemma nosmt big_ind (K : comoid -> bool) r P (F : 'a -> comoid):
       (forall x y, K x => K y => K (x * y))
    => K I => (forall i, P i => K (F i))
    => K (big r P F).
  proof.
    move=> Kop Kidx K_F; apply big_rec => //.
    by move=> i x Pi Kx; apply Kop => //; apply K_F.
  qed.

  lemma nosmt big_rec2:
    forall (K : comoid -> comoid -> bool) r P (F1 F2 : 'a -> comoid),
         K I I
      => (forall i y1 y2, P i => K y1 y2 => K (F1 i * y1) (F2 i * y2))
      => K (big r P F1) (big r P F2).
  proof.
    move=> K r P F1 F2 KI KF; elim r => //= i r IHr.
    by rewrite !big_cons; case (P i) => _ //=; apply KF.
  qed.
  
  lemma nosmt big_ind2:
    forall (K : comoid -> comoid -> bool) r P (F1 F2 : 'a -> comoid),
         (forall x1 x2 y1 y2, K x1 x2 => K y1 y2 => K (x1 * y1) (x2 * y2))
      => K I I
      => (forall i, P i => K (F1 i) (F2 i))
      => K (big r P F1) (big r P F2).
  proof.
    move=> K r P F1 F2 Kop KI KF; apply big_rec2 => //.
    by move=> i x1 x2 Pi Kx1x2; apply Kop => //; apply KF.
  qed.

  lemma nosmt big_endo (f : comoid -> comoid):
       f I  = I
    => (forall (x y : comoid), f (x * y) = f x * f y)
    => forall r P (F : 'a -> comoid),
         f (big r P F) = big r P (f \o F).
  proof.
    (* FIX: should be a consequence of big_morph *)
    move=> fI fM; elim=> //= i r IHr P F; rewrite !big_cons.
    by case (P i) => //=; rewrite 1?fM IHr.
  qed.

  (* -------------------------------------------------------------------- *)
  (*                    Mapping, filtering, ...                           *)
  (* -------------------------------------------------------------------- *)
  lemma nosmt big_map (h : 'b -> 'a) r P F:
    big (map h r) P F = big r (P \o h) (F \o h).
  proof. by elim r => //= x s IHs; rewrite !big_cons IHs. qed.

  lemma nosmt big_nth x0 (r : 'a list) P F:
      big r P F
    = big (iota_ 0 (size r))
        (fun i, P (nth x0 r i))
        (fun i, F (nth x0 r i)).
  proof. by rewrite -{1}(mkseq_nth x0 r) /mkseq big_map. qed.

  lemma nosmt big_filter r P (F : 'a -> comoid):
    big (filter P r) predT F = big r P F.
  proof.
    elim r => //= i r IHr; rewrite !big_cons -IHr.
    by case (P i); rewrite ?big_cons.
  qed.

  lemma nosmt big_filter_cond r P1 P2 (F : 'a -> comoid):
    big (filter P1 r) P2 F = big r (predI P1 P2) F.
  proof.
    rewrite -big_filter -(big_filter r); congr=> //.
    rewrite -filter_predI; apply eq_filter=> x.
    by rewrite /predI andC.
  qed.

  lemma nosmt big_hasC r P (F : 'a -> comoid):
    !has P r => big r P F = I.
  proof. smt. qed.

  (* -------------------------------------------------------------------- *)
  (*               Extentional version of congruence.                     *)
  (* -------------------------------------------------------------------- *)
  lemma nosmt eq_bigr r P (F1 F2 : 'a -> comoid):
    (forall i, P i => F1 i = F2 i) =>  big r P F1 = big r P F2.
  proof. by move=> eqF12; apply big_rec2 => // i x y Pi <-; rewrite eqF12. qed.

  lemma nosmt eq_bigl r P1 P2 (F : 'a -> comoid):
    (forall x, P1 x <=> P2 x) => big r P1 F = big r P2 F.
  proof. by move=> eqP12; rewrite -!(big_filter r) (eq_filter P1 P2). qed.

  lemma nosmt eq_big r P1 P2 (F1 F2 : 'a -> comoid):
       (forall x, P1 x <=> P2 x)
    => (forall i, P1 i => F1 i = F2 i)
    => big r P1 F1 = big r P2 F2.
  proof.
    move=> h; rewrite -(eq_bigl r P1 P2 F2) // => {h}.
    by move=> h; rewrite (eq_bigr r P1 F1 F2).
  qed.

  lemma nosmt congr_big r1 r2 P1 P2 (F1 F2 : 'a -> comoid):
       r1 = r2
    => (forall x, P1 x <=> P2 x)
    => (forall i, P1 i => F1 i = F2 i)
    => big r1 P1 F1 = big r2 P2 F2.
  proof. by move=> <-{r2}; apply eq_big. qed.

  (* -------------------------------------------------------------------- *)
  (*                   Bigop and false predicate                          *)
  (* -------------------------------------------------------------------- *)
  lemma nosmt big_pred0_eq r (F : 'a -> comoid): big r pred0 F = I.
  proof. by rewrite big_hasC // has_pred0. qed.

  lemma nosmt big_pred0 (r : 'a list) P F:
    (forall x, P x <=> false) => big r P F = I.
  proof. by move=> h; rewrite (eq_bigl _ _ pred0) // big_pred0_eq. qed.

  (* ------------------------------------------------------------------- *)
  (*                         Bigop and cat                               *)
  (* ------------------------------------------------------------------- *)
  lemma big_cat_nested r1 r2 P (F : 'a -> comoid):
    big (r1 ++ r2) P F = Bigop.big (big r2 P F) Comoid.( * ) r1 P F.
  proof. (* FIX: /Bigop.big should unfold all occurences *)
    rewrite /big; do! rewrite /Bigop.big.
    by rewrite filter_cat map_cat foldr_cat.
  qed.
end BigComoid.
