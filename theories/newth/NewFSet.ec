(* --------------------------------------------------------------------
 * Copyright (c) - 2012-2015 - IMDEA Software Institute and INRIA
 * Distributed under the terms of the CeCILL-B licence.
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
require import Pred NewLogic NewList.

(* -------------------------------------------------------------------- *)
(* Finite sets are abstractely represented as the quotient by [perm_eq] *)
(* of lists without duplicates - i.e. as the quotient of lists by the   *)
(* membership operation.                                                *)

type 'a fset.

op elems  : 'a fset -> 'a list.
op oflist : 'a list -> 'a fset.

axiom elemsK  (s : 'a fset): oflist (elems  s) = s.
axiom oflistK (s : 'a list): perm_eq (undup s) (elems (oflist s)).

lemma uniq_elems (s : 'a fset): uniq (elems s).
proof.
  rewrite -(elemsK s); move: (elems s) => {s} s.
  by rewrite -(perm_eq_uniq (undup s)) ?(undup_uniq, oflistK).
qed.

axiom fset_eq (s1 s2 : 'a fset):
  (perm_eq (elems s1) (elems s2)) => (s1 = s2).

lemma oflist_perm_eq (s1 s2 : 'a list):
  perm_eq s1 s2 =>
  oflist s1 = oflist s2.
proof.
  move=> h; apply/fset_eq.
  apply/(perm_eq_trans (undup s1)).
  + by apply/perm_eq_sym/oflistK.
  apply/(perm_eq_trans (undup s2)); first last.
  + by apply/oflistK.
  apply/uniq_perm_eq; 1..2:apply/undup_uniq.
  by move=> x; rewrite !mem_undup; apply/perm_eq_mem.
qed.

(* -------------------------------------------------------------------- *)
op card ['a] (s : 'a fset) = size (elems s) axiomatized by cardE.

(* -------------------------------------------------------------------- *)
op mem ['a] (s : 'a fset) (x : 'a) = mem (elems s) x
  axiomatized by memE.

lemma mem_oflist (s : 'a list):
  forall x, mem (oflist s) x <=> mem s x.
proof.
  move=> x; rewrite !memE /= (perm_eq_mem _ (undup s)).
    by rewrite perm_eq_sym oflistK.
  by rewrite mem_undup.
qed.

lemma fsetP (s1 s2 : 'a fset):
  (s1 = s2) <=> (forall x, mem s1 x <=> mem s2 x).
proof.
  by split=> [-> | h] //; apply/fset_eq; rewrite uniq_perm_eq;
    rewrite 1?uniq_elems // => x; move: (h x); rewrite !memE.
qed.

(* -------------------------------------------------------------------- *)
op fset0 ['a] = oflist [<:'a>] axiomatized by set0E.
op fset1 ['a] (z : 'a) = oflist [z] axiomatized by set1E.

op (`|`) ['a] (s1 s2 : 'a fset) = oflist (elems s1 ++ elems s2)
  axiomatized by setUE.

op (`&`) ['a] (s1 s2 : 'a fset) = oflist (filter (mem s2) (elems s1))
  axiomatized by setIE.

op (`\`) ['a] (s1 s2 : 'a fset) = oflist (filter (predC (mem s2)) (elems s1))
  axiomatized by setDE.

(* -------------------------------------------------------------------- *)
lemma in_fset0: forall x, mem fset0<:'a> x <=> false.
proof. by move=> x; rewrite set0E mem_oflist. qed.

lemma in_fset1 z: forall x, mem (fset1<:'a> z) x <=> x = z.
proof. by move=> x; rewrite set1E /= mem_oflist. qed.

lemma elems_fset1 (x : 'a) : elems (fset1 x) = [x].
proof.
  rewrite set1E; apply/perm_eq_small/perm_eq_sym=> //=.
  by rewrite -{1}(undup_id [x]) ?oflistK.
qed.

lemma in_fsetU (s1 s2 : 'a fset):
  forall x, mem (s1 `|` s2) x <=> mem s1 x \/ mem s2 x.
proof. by move=> x; rewrite setUE mem_oflist mem_cat !memE. qed.

lemma in_fsetI (s1 s2 : 'a fset):
  forall x, mem (s1 `&` s2) x <=> mem s1 x /\ mem s2 x.
proof. by move=> x; rewrite setIE mem_oflist mem_filter !memE. qed.

lemma in_fsetD (s1 s2 : 'a fset):
  forall x, mem (s1 `\` s2) x <=> mem s1 x /\ !mem s2 x.
proof. by move=> x; rewrite setDE mem_oflist mem_filter /predC !memE. qed.

(* -------------------------------------------------------------------- *)
hint rewrite inE : in_fset0 in_fset1 in_fsetU in_fsetI in_fsetD.

(* -------------------------------------------------------------------- *)
op filter ['a] (p : 'a -> bool) (s : 'a fset) =
  oflist (filter p (elems s))
  axiomatized by filterE.

(* -------------------------------------------------------------------- *)
lemma in_filter (p : 'a -> bool) (s : 'a fset):
  forall x, mem (filter p s) x <=> p x /\ mem s x.
proof. by move=> x; rewrite filterE mem_oflist mem_filter memE. qed.

(* -------------------------------------------------------------------- *)
pred (<=) (s1 s2 : 'a fset) = mem s1 <= mem s2.
pred (< ) (s1 s2 : 'a fset) = mem s1 <  mem s2.

lemma nosmt subsetE (s1 s2 : 'a fset):
  (s1 <= s2) <=> (mem s1 <= mem s2).
proof. by []. qed.

(* -------------------------------------------------------------------- *)
lemma nosmt eqEsubset (A B : 'a fset) : (A = B) <=> (A <= B) /\ (B <= A).
proof. by rewrite fsetP !subsetE; rewrite subpred_eqP. qed.

(* -------------------------------------------------------------------- *)
lemma nosmt cards0: card fset0<:'a> = 0.
proof. by rewrite cardE set0E -(perm_eq_size (undup [])) 1:oflistK. qed.

lemma nosmt card_ge0 (A : 'a fset) : Int.(<=) 0 (card A).
proof. by rewrite cardE size_ge0. qed.

(* -------------------------------------------------------------------- *)
lemma nosmt fset_ind (p : 'a fset -> bool):
  p fset0 =>
  (forall x s, p s => p (s `|` (fset1 x))) =>
  (forall s, p s).
proof.
  move=> p0 pa s; rewrite -elemsK.
  elim (elems s) (uniq_elems s)=> {s}.
    by rewrite -set0E.
  move=> x s ih /cons_uniq [] x_notin_s uniq_s.
  have /(pa x) := ih _=> //; rewrite setUE.
  rewrite elems_fset1 (oflist_perm_eq (elems (oflist s) ++ [x]) (x::s)) //.
  apply/perm_catCl=> /=; apply/perm_cons/perm_eq_sym.
  by rewrite -{1}(undup_id s _) // oflistK.
qed.

(* ------------------------------------------------------------------ *)
lemma fsetUC (A B : 'a fset) : A `|` B = B `|` A.
proof. by apply/fsetP => x; rewrite !inE orbC. qed.

lemma fset0U (A : 'a fset) : fset0 `|` A = A.
proof. by apply/fsetP => x; rewrite !inE. qed.

lemma fsetU0 (A : 'a fset) : A `|` fset0 = A.
proof. by rewrite fsetUC fset0U. qed.

lemma fsetUA (A B C : 'a fset) : A `|` (B `|` C) = A `|` B `|` C.
proof. by apply/fsetP => x; rewrite !inE orbA. qed.

lemma fsetUCA (A B C : 'a fset) : A `|` (B `|` C) = B `|` (A `|` C).
proof. by rewrite !fsetUA (fsetUC B). qed.

lemma fsetUAC (A B C : 'a fset) : A `|` B `|` C = A `|` C `|` B.
proof. by rewrite -!fsetUA (fsetUC B). qed.

lemma fsetUACA (A B C D : 'a fset) : (A `|` B) `|` (C `|` D) = (A `|` C) `|` (B `|` D).
proof. by rewrite -!fsetUA (fsetUCA B). qed.

lemma fsetUid (A : 'a fset) : A `|` A = A.
proof. by apply/fsetP=> x; rewrite !inE orbb. qed.

lemma fsetUUl (A B C : 'a fset) : A `|` B `|` C = (A `|` C) `|` (B `|` C).
proof. by rewrite fsetUA (fsetUAC _ C) -(fsetUA _ C) fsetUid. qed.

lemma fsetUUr (A B C : 'a fset) : A `|` (B `|` C) = (A `|` B) `|` (A `|` C).
proof. by rewrite !(fsetUC A) fsetUUl. qed.

(* ------------------------------------------------------------------ *)
lemma fsetIC (A B : 'a fset) : A `&` B = B `&` A.
proof. by apply/fsetP => x; rewrite !inE andbC. qed.

lemma fset0I (A : 'a fset) : fset0 `&` A = fset0.
proof. by apply/fsetP => x; rewrite !inE andFb. qed.

lemma fsetI0 (A : 'a fset) : A `&` fset0 = fset0.
proof. by rewrite fsetIC fset0I. qed.

lemma fsetIA (A B C : 'a fset) : A `&` (B `&` C) = A `&` B `&` C.
proof. by apply/fsetP=> x; rewrite !inE andbA. qed.

lemma fsetICA (A B C : 'a fset) : A `&` (B `&` C) = B `&` (A `&` C).
proof. by rewrite !fsetIA (fsetIC A). qed.

lemma fsetIAC (A B C : 'a fset) : A `&` B `&` C = A `&` C `&` B.
proof. by rewrite -!fsetIA (fsetIC B). qed.

lemma fsetIACA (A B C D : 'a fset) : (A `&` B) `&` (C `&` D) = (A `&` C) `&` (B `&` D).
proof. by rewrite -!fsetIA (fsetICA B). qed.

lemma fsetIid (A : 'a fset) : A `&` A = A.
proof. by apply/fsetP=> x; rewrite !inE andbb. qed.

lemma fsetIIl (A B C : 'a fset) : A `&` B `&` C = (A `&` C) `&` (B `&` C).
proof. by rewrite fsetIA (fsetIAC _ C) -(fsetIA _ C) fsetIid. qed.

lemma fsetIIr (A B C : 'a fset) : A `&` (B `&` C) = (A `&` B) `&` (A `&` C).
proof. by rewrite !(fsetIC A) fsetIIl. qed.

(* ------------------------------------------------------------------ *)
lemma fsetIUr (A B C : 'a fset) : A `&` (B `|` C) = (A `&` B) `|` (A `&` C).
proof. by apply/fsetP=> x; rewrite !inE andb_orr. qed.

lemma fsetIUl (A B C : 'a fset) : (A `|` B) `&` C = (A `&` C) `|` (B `&` C).
proof. by apply/fsetP=> x; rewrite !inE andb_orl. qed.

lemma fsetUIr (A B C : 'a fset) : A `|` (B `&` C) = (A `|` B) `&` (A `|` C).
proof. by apply/fsetP=> x; rewrite !inE orb_andr. qed.

lemma fsetUIl (A B C : 'a fset) : (A `&` B) `|` C = (A `|` C) `&` (B `|` C).
proof. by apply/fsetP=> x; rewrite !inE orb_andl. qed.

lemma fsetUK (A B : 'a fset) : (A `|` B) `&` A = A.
proof. by apply/fsetP=> x; rewrite !inE orbK. qed.

lemma fsetKU (A B : 'a fset) : A `&` (B `|` A) = A.
proof. by apply/fsetP=> x; rewrite !inE orKb. qed.

lemma fsetIK (A B : 'a fset) : (A `&` B) `|` A = A.
proof. by apply/fsetP=> x; rewrite !inE andbK. qed.

lemma fsetKI (A B : 'a fset) : A `|` (B `&` A) = A.
proof. by apply/fsetP=> x; rewrite !inE andKb. qed.

(* ------------------------------------------------------------------ *)
lemma fsetD0 (A : 'a fset) : A `\` fset0 = A.
proof. by apply/fsetP=> x; rewrite !inE andbT. qed.

lemma fset0D (A : 'a fset) : fset0 `\` A = fset0.
proof. by apply/fsetP=> x; rewrite !inE. qed.

lemma fsetDv (A : 'a fset) : A `\` A = fset0.
proof. by apply/fsetP=> x; rewrite !inE andbN. qed.

lemma fsetID (A B : 'a fset) : A `&` B `|` A `\` B = A.
proof. by apply/fsetP=> x; rewrite !inE -andb_orr orbN andbT. qed.

lemma fsetII (A B : 'a fset) : (A `&` B) `&` (A `\` B) = fset0.
proof. by apply/fsetP=> x; rewrite !inE andbACA andbN andbF. qed.

lemma fsetDUl (A B C : 'a fset) : (A `|` B) `\` C = (A `\` C) `|` (B `\` C).
proof. by apply/fsetP=> x; rewrite !inE -andb_orl. qed.

lemma fsetDUr (A B C : 'a fset) : A `\` (B `|` C) = (A `\` B) `&` (A `\` C).
proof. by apply/fsetP=> x; rewrite !inE andbACA andbb negb_or. qed.

lemma fsetDIl (A B C : 'a fset) : (A `&` B) `\` C = (A `\` C) `&` (B `\` C).
proof. by apply/fsetP=> x; rewrite !inE andbACA andbb. qed.

lemma fsetIDA (A B C : 'a fset) : A `&` (B `\` C) = (A `&` B) `\` C.
proof. by apply/fsetP=> x; rewrite !inE !andbA. qed.

lemma fsetIDAC (A B C : 'a fset) : (A `\` B) `&` C = (A `&` C) `\` B.
proof. by apply/fsetP=> x; rewrite !inE andbAC. qed.

lemma fsetDIr (A B C : 'a fset) : A `\` (B `&` C) = (A `\` B) `|` (A `\` C).
proof. by apply/fsetP=> x; rewrite !inE -andb_orr negb_and. qed.

lemma fsetDDl (A B C : 'a fset) : (A `\` B) `\` C = A `\` (B `|` C).
proof. by apply/fsetP=> x; rewrite !inE !negb_or !andbA. qed.

lemma fsetDDr (A B C : 'a fset) : A `\` (B `\` C) = (A `\` B) `|` (A `&` C).
proof. by apply/fsetP=> x; rewrite !inE -andb_orr negb_and negbK. qed.

lemma fsetDK (A B : 'a fset) : (A `|` B) `\` B = A `\` B.
proof. by rewrite fsetDUl fsetDv fsetU0. qed.

lemma fsetDKv (A B : 'a fset) : (A `&` B) `\` B = fset0.
proof. by rewrite fsetDIl fsetDv fsetI0. qed.
