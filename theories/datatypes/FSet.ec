(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2015 - IMDEA Software Institute
 * Copyright (c) - 2012--2015 - Inria
 * 
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
require import Pred Fun Int NewLogic List StdRing StdOrder.
(*---*) import IntOrder.

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

(* -------------------------------------------------------------------- *)
lemma oflist_perm_eq (s1 s2 : 'a list):
  perm_eq s1 s2 => oflist s1 = oflist s2.
proof.
  (* FIXME: named cuts for h1/h2 should not be necessary *)
  move=> peq_s1s2; apply/fset_eq; apply/uniq_perm_eq.
    by apply/uniq_elems. by apply/uniq_elems.
  move=> x; have h1 := oflistK s1; have h2 := oflistK s2.
  rewrite -(perm_eq_mem _ _ h1) -(perm_eq_mem _ _ h2).
  by rewrite !mem_undup; apply/perm_eq_mem.
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
op pick ['a] : 'a fset -> 'a.

axiom pick0: pick<:'a> fset0 = Option.witness.

axiom mem_pick (A : 'a fset): A <> fset0 => mem A (pick A).

(* -------------------------------------------------------------------- *)
lemma in_fset0: forall x, mem fset0<:'a> x <=> false.
proof. by move=> x; rewrite set0E mem_oflist. qed.

lemma elems_fset0 ['a]: elems fset0 = [<:'a>].
proof.
  rewrite set0E; apply/perm_eq_small/perm_eq_sym=> //=.
  by rewrite -{1}(undup_id []) ?oflistK.
qed.

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

lemma filter0 (p : 'a -> bool): filter p fset0 = fset0.
proof. by apply/fsetP=> x; rewrite in_filter in_fset0. qed.

lemma filter1 (p : 'a -> bool) (a : 'a):
  filter p (fset1 a) = if (p a) then fset1 a else fset0.
proof.
  apply/fsetP=> x; rewrite in_filter fun_if2 in_fset1 in_fset0.
  by case (x = a).
qed.

lemma filterU (p : 'a -> bool) (A B : 'a fset):
  filter p (A `|` B) = filter p A `|` filter p B.
proof. by apply/fsetP=> x; rewrite !(inE,in_filter) andC; smt. qed.

lemma filter_pred1 (a : 'a) (A : 'a fset):
  filter (pred1 a) A = if mem A a then fset1 a else fset0.
proof.
  by apply/fsetP=> x; rewrite in_filter /pred1 fun_if2 !inE; case (x = a).
qed.

(* -------------------------------------------------------------------- *)
pred (<=) (s1 s2 : 'a fset) = mem s1 <= mem s2.
pred (< ) (s1 s2 : 'a fset) = mem s1 <  mem s2.

lemma nosmt subsetP (s1 s2 : 'a fset):
  (s1 <= s2) <=> (mem s1 <= mem s2).
proof. by []. qed.

(* -------------------------------------------------------------------- *)
lemma nosmt eqEsubset (A B : 'a fset) : (A = B) <=> (A <= B) /\ (B <= A).
proof. by rewrite fsetP 2!subsetP subpred_eqP. qed.

(* -------------------------------------------------------------------- *)
lemma nosmt fset_ind (p : 'a fset -> bool):
  p fset0 =>
  (forall x s, !mem s x => p s => p (s `|` (fset1 x))) =>
  (forall s, p s).
proof.
  move=> p0 pa s; rewrite -elemsK.
  elim (elems s) (uniq_elems s)=> {s}; 1: by rewrite -set0E.
  move=> x s ih /cons_uniq []; rewrite -mem_oflist=> x_notin_s uniq_s. (* FIXME: views *)
  have /(pa x _ x_notin_s) := ih _=> //; rewrite setUE.
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

lemma fset1I (x : 'a) (D : 'a fset):
  fset1 x `&` D = if mem D x then fset1 x else fset0.
proof. by apply/fsetP=> y; rewrite !inE; case: (mem D x); smt. qed.

lemma fsetI1 (x : 'a) (D : 'a fset):
  D `&` fset1 x = if mem D x then fset1 x else fset0.
proof. by rewrite fsetIC fset1I. qed.

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

lemma fset1D (x : 'a) (D : 'a fset):
  fset1 x `\` D = if mem D x then fset0 else fset1 x.
proof. by apply/fsetP=> y; rewrite !inE; case: (mem D x); smt. qed.

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

(* -------------------------------------------------------------------- *)
lemma subsetIl (A B : 'a fset) : (A `&` B) <= A.
proof. by apply/subsetP=> x; rewrite inE; case. qed.

lemma subsetIr (A B : 'a fset) : (A `&` B) <= B.
proof. by apply/subsetP=> x; rewrite inE; case. qed.

(* -------------------------------------------------------------------- *)
lemma subsetDl (A B : 'a fset) : A `\` B <= A.
proof. by apply/subsetP=> x; rewrite !inE; case. qed.

(* -------------------------------------------------------------------- *)
lemma sub0set (A : 'a fset) : fset0 <= A.
proof. by apply/subsetP=> x; rewrite !inE. qed.

(* -------------------------------------------------------------------- *)
lemma fcards0: card fset0<:'a> = 0.
proof. by rewrite cardE set0E -(perm_eq_size (undup [])) 1:oflistK. qed.

lemma eq_fcards0 (A : 'a fset): A = fset0 => card A = 0.
proof. by move=> ->; apply/fcards0. qed.

lemma fcard_ge0 (A : 'a fset) : 0 <= card A.
proof. by rewrite cardE size_ge0. qed.

lemma fcard1 (x : 'a) : card (fset1 x) = 1.
proof. by rewrite cardE elems_fset1. qed.

(* -------------------------------------------------------------------- *)
lemma nosmt fcardUI_indep (A B : 'a fset) : A `&` B = fset0 =>
  card (A `|` B) = card A + card B.
proof.
  move/fsetP=> h; rewrite setUE !cardE; pose s := _ ++ _.
  have <- := perm_eq_size _ _ (oflistK s). (* FIXME *)
  rewrite undup_id /s 2:size_cat // cat_uniq ?uniq_elems /=.
  rewrite -implybF => /hasP [x [Bx Ax]]; have := h x.
  by rewrite in_fsetI in_fset0 !memE Bx Ax.
qed.

lemma fcardUI (A B : 'a fset) :
  card (A `|` B) + card (A `&` B) = card A + card B.
proof.
  rewrite -(fsetID (A `|` B) A) fsetUK (fsetUC A B) fsetDK.
  rewrite fcardUI_indep.
    by rewrite fsetIDA fsetDIl fsetDv fset0I.
  by rewrite addzAC fsetIC -addzA -fcardUI_indep ?fsetID ?fsetII.
qed.

(* -------------------------------------------------------------------- *)
lemma nosmt fcardU (A B : 'a fset) :
  card (A `|` B) = card A + card B - card (A `&` B).
proof. by rewrite -fcardUI smt. qed.

lemma nosmt fcardI (A B : 'a fset) :
  card (A `&` B) = card A + card B - card (A `|` B).
proof. by rewrite -fcardUI smt. qed.

(* -------------------------------------------------------------------- *)
lemma nosmt fcardID (A B : 'a fset) :
  card (A `&` B) + card (A `\` B) = card A.
proof. by rewrite -fcardUI_indep ?fsetID // fsetII. qed.

lemma nosmt fcardD (A B : 'a fset) :
  card (A `\` B) = card A - card (A `&` B).
proof. by rewrite -(fcardID A B) smt. qed.

(* -------------------------------------------------------------------- *)
lemma nosmt fcardD1 (A : 'a fset) (x : 'a) :
  card A = card (A `\` fset1 x) + (if mem A x then 1 else 0).
proof.
  case: (mem A x) => Ax //=; last first.
    congr; apply/fsetP=> y; rewrite !inE smt.
  rewrite -(fcard1 x) -fcardUI addzC eq_sym eq_fcards0 /=.
    by apply/fsetP=> y; rewrite !inE smt.
  by congr; apply/fsetP=> y; rewrite !inE; case: (y = x).
qed.

(* -------------------------------------------------------------------- *)
lemma subset_leq_fcard (A B : 'a fset) :
  A <= B => card A <= card B.
proof.
  move=> /subsetP le_AB; rewrite -(fcardID B A).
  have ->: B `&` A = A; 1: apply/fsetP=> x.
    by rewrite in_fsetI andb_idl //; apply/le_AB.
  by apply/ler_addl; apply/fcard_ge0.
qed.

(* -------------------------------------------------------------------- *)
lemma subset_cardP (A B : 'a fset) :
  card A = card B => (A = B <=> A <= B).
proof.                          (* FIXME: views *)
  move=> eqcAB; split=> [->// |]; rewrite eqEsubset.
  move=> le_AB; split=> // x Bx; case: (mem A x) => // Ax.
  rewrite -(ltrr (card A)) {2}eqcAB (fcardD1 B x) Bx /=.
  rewrite addzC -lez_add1r ler_add //; apply/subset_leq_fcard.
  apply/subsetP=> y Ay; rewrite !inE le_AB //=; move: Ax.
  by apply/absurd=> /= <-.
qed.

(* -------------------------------------------------------------------- *)
lemma nosmt eqEcard (A B : 'a fset) :
  (A = B) <=> (A <= B) /\ (card B <= card A).
proof.
  split=> [->// |]; case=> le_AB le_cAB; rewrite subset_cardP //.
  by rewrite eqr_le le_cAB /=; apply/subset_leq_fcard.
qed.

(* -------------------------------------------------------------------- *)
lemma fcard_eq0 (A : 'a fset) : (card A = 0) <=> (A = fset0).
proof.
  split=> [z_cA|]; last by move=> ->; apply/fcards0.
  rewrite eq_sym eqEcard z_cA fcards0 //=; apply/sub0set.
qed.

(* -------------------------------------------------------------------- *)
op image (f: 'a -> 'b) (A : 'a fset): 'b fset = oflist (map f (elems A))
  axiomatized by imageE.

lemma imageP (f : 'a -> 'b) (A : 'a fset) (b : 'b):
  mem (image f A) b <=> (exists a, mem A a /\ f a = b).
proof.
  rewrite imageE mem_oflist mapP; split.
    by move=> [a] [x_in_A ->]; exists a; rewrite memE.
  by move=> [a] [x_in_A <-]; exists a; rewrite -memE.
qed.

lemma nosmt image0 (f : 'a -> 'b): image f fset0 = fset0.
proof.
  by apply/fsetP=> b; rewrite imageP; split=> [[a]|]; rewrite in_fset0.
qed.

lemma nosmt image1 (f : 'a -> 'b) (a : 'a):
  image f (fset1 a) = fset1 (f a).
proof.
  apply/fsetP=> b; rewrite imageP in_fset1.
  by split=> [[a']|->]; [|exists a]; rewrite in_fset1.
qed.

lemma nosmt imageU (f : 'a -> 'b) (A B : 'a fset):
  image f (A `|` B) = image f A `|` image f B.
proof.
  apply/fsetP=> x; rewrite in_fsetU !imageP; split.
    by move=> [x']; rewrite in_fsetU=> [[x'_in_A|x'_in_B] <-];
       [left|right]; exists x'.
  by move=> [[x'] [x'_in_X] <-|[x'] [x'_in_X] <-];
     exists x'; rewrite in_fsetU x'_in_X.
qed.

(* -------------------------------------------------------------------- *)
op product (A : 'a fset) (B : 'b fset): ('a * 'b) fset =
  oflist (flatten (map (fun a => map (fun b => (a,b)) (elems B)) (elems A)))
  axiomatized by productE.

lemma productP (A : 'a fset) (B : 'b fset) (a : 'a) (b : 'b):
  mem (product A B) (a,b) <=> mem A a /\ mem B b.
proof.
  rewrite productE -{2}(elemsK A) -{2}(elemsK B) !mem_oflist /flatten.
  elim (elems A) (elems B) a b=> {A B} [//=|].
  move=> a' A ih B a b /=; rewrite mem_cat mapP ih /=.
  case (a = a')=> [->|] //=.
  split=> [[[b']|] //=|b_in_B].
  by left; exists b.
qed.

(* -------------------------------------------------------------------- *)
op fold (f : 'a -> 'b -> 'b) (z : 'b) (A : 'a fset) : 'b =
  foldr f z (elems A)
  axiomatized by foldE.

lemma fold0 (f : 'a -> 'b -> 'b) (z : 'b): fold f z fset0 = z.
proof. by rewrite foldE elems_fset0. qed.

lemma fold1 (f : 'a -> 'b -> 'b) (z : 'b) (a : 'a):
  fold f z (fset1 a) = f a z.
proof. by rewrite foldE elems_fset1. qed.

lemma foldC (a : 'a) (f : 'a -> 'b -> 'b) (z : 'b) (A : 'a fset):
  (forall a a' b, f a (f a' b) = f a' (f a b)) =>
  mem A a =>
  fold f z A = f a (fold f z (A `\` fset1 a)).
proof.
  move=> f_commutative a_in_A; rewrite !foldE (foldr_rem a)// 1:-memE//.
  congr; apply/foldr_perm=> //.
  rewrite setDE rem_filter 1:uniq_elems//.
  have ->: predC (mem (fset1 a)) = predC1 a (* FIXME: views *)
    by apply/fun_ext=> x; rewrite /predC /predC1 in_fset1.
  rewrite -{1}(undup_id (filter (predC1 a) (elems A))) 2:oflistK//.
  by apply/filter_uniq/uniq_elems.
qed.
