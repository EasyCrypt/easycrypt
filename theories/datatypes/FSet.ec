(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
require import Core Int List StdRing StdOrder.
(*---*) import IntOrder.

(* -------------------------------------------------------------------- *)
(* Finite sets are abstractly represented as the quotient by [perm_eq]  *)
(* of lists without duplicates - i.e. as the quotient of lists by the   *)
(* membership operation.                                                *)

type 'a fset.

op elems  : 'a fset -> 'a list.
op oflist : 'a list -> 'a fset.

axiom elemsK  (s : 'a fset): oflist (elems  s) = s.
axiom oflistK (s : 'a list): perm_eq (undup s) (elems (oflist s)).

axiom fset_eq (s1 s2 : 'a fset):
  (perm_eq (elems s1) (elems s2)) => (s1 = s2).

(* -------------------------------------------------------------------- *)
lemma oflist_uniq (s : 'a list) : uniq s =>
  perm_eq s (elems (oflist s)).
proof. by move/undup_id => {1}<-; apply/oflistK. qed.

(* -------------------------------------------------------------------- *)
lemma uniq_elems (s : 'a fset): uniq (elems s).
proof.
rewrite -(elemsK s); move: (elems s) => {s} s.
by rewrite -(perm_eq_uniq (undup s)) ?(undup_uniq, oflistK).
qed.

(* -------------------------------------------------------------------- *)
lemma perm_eq_oflist (s1 s2 : 'a list) :
  oflist s1 = oflist s2 => perm_eq (undup s1) (undup s2).
proof.
move=> oflist_eq; rewrite (perm_eq_trans _ _ _ (oflistK s1)) oflist_eq.
by rewrite perm_eq_sym oflistK.
qed.

lemma oflist_perm_eq (s1 s2 : 'a list):
  perm_eq s1 s2 => oflist s1 = oflist s2.
proof.
move=> peq_s1s2; apply/fset_eq/uniq_perm_eq; 1,2: exact/uniq_elems.
move=> x; rewrite -(perm_eq_mem _ _ (oflistK s1)).
rewrite -(perm_eq_mem _ _ (oflistK s2)).
by rewrite !mem_undup (perm_eq_mem _ _ peq_s1s2).
qed.

(* -------------------------------------------------------------------- *)
op card ['a] (s : 'a fset) = size (elems s) axiomatized by cardE.

(* -------------------------------------------------------------------- *)
op mem ['a] (s : 'a fset) (x : 'a) = mem (elems s) x
  axiomatized by memE.

abbrev (\in) (z : 'a) (s : 'a fset) = mem s z.

lemma mem_oflist (s : 'a list):
  forall x, mem (oflist s) x <=> mem s x.
proof.
move=> x; rewrite !memE (perm_eq_mem _ (undup s)) 2:mem_undup //.
by rewrite perm_eq_sym oflistK.
qed.

lemma fsetP (s1 s2 : 'a fset):
  (s1 = s2) <=> (forall x, mem s1 x <=> mem s2 x).
proof.
split=> // h; apply/fset_eq/uniq_perm_eq; 1,2: exact/uniq_elems.
by move=> x; rewrite -!memE h.
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

lemma in_eq_fset0 ['a] (X : 'a fset): (forall x, !x \in X) => X = fset0.
proof. by move=> mem_X; apply/fsetP=> x; rewrite mem_X in_fset0. qed.

lemma elems_fset0 ['a]: elems fset0 = [<:'a>].
proof.
rewrite set0E; apply/perm_eq_small/perm_eq_sym=> //=.
by rewrite -{1}(undup_id []) ?oflistK.
qed.

lemma elems_eq_fset0 ['a] (A : 'a fset): elems A = [<:'a>] => A = fset0.
proof.
by move=> elems_nil; apply/fsetP=> x; rewrite !memE elems_fset0 elems_nil.
qed.

lemma in_fset1 z: forall x, mem (fset1<:'a> z) x <=> x = z.
proof. by move=> x; rewrite set1E /= mem_oflist. qed.

lemma in_eq_fset1 ['a] (X : 'a fset) x0:
  (forall x, x \in X <=> x = x0) => X = fset1 x0.
proof. by move=> mem_X; apply/fsetP=> x; rewrite in_fset1 mem_X. qed.

lemma elems_fset1 (x : 'a) : elems (fset1 x) = [x].
proof.
rewrite set1E; apply/perm_eq_small/perm_eq_sym=> //=.
by rewrite -{1}(undup_id [x]) ?oflistK.
qed.

lemma elems_eq_fset1 (A : 'a fset) x : elems A = [x] => A = fset1 x.
proof.
by move=> elems_x; apply/fsetP=> x0; rewrite !memE elems_fset1 elems_x.
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

lemma setD1E (s : 'a fset) x :
  perm_eq (elems (s `\` fset1 x)) (rem x (elems s)).
proof.
rewrite setDE; pose s' := List.filter _ _; apply/(perm_eq_trans s').
  rewrite perm_eq_sym oflist_uniq ?filter_uniq ?uniq_elems.
rewrite /s' rem_filter ?uniq_elems; apply/uniq_perm_eq;
  rewrite ?filter_uniq ?uniq_elems // => y.
by rewrite !mem_filter /predC in_fset1.
qed.

lemma perm_to_rem (s:'a fset) x :
  mem s x => perm_eq (elems s) (x :: elems (s `\` fset1 x)).
proof.
rewrite memE => /perm_to_rem /perm_eqlP->; apply/perm_cons.
have /perm_eqlP <- := (setD1E s x); rewrite perm_eq_refl.
qed.

(* -------------------------------------------------------------------- *)
hint rewrite inE : in_fset0 in_fset1 in_fsetU in_fsetI in_fsetD.

lemma oflist_cons ['a] (x : 'a) s : oflist (x::s) = fset1 x `|` oflist s.
proof. by apply fsetP => z;rewrite mem_oflist !inE mem_oflist /=. qed.

lemma oflist_cat ['a] (s1 s2 : 'a list) : 
  oflist (s1 ++ s2) = oflist s1 `|` oflist s2.
proof. by apply fsetP => z; rewrite in_fsetU !mem_oflist mem_cat. qed.

(* -------------------------------------------------------------------- *)
lemma in_fsetU1 (s : 'a fset) x:
  forall x', mem (s `|` fset1 x) x' <=> mem s x' \/ x' = x.
proof. by move=> x'; rewrite in_fsetU in_fset1. qed.

lemma in_fsetI1 (s : 'a fset) x:
  forall x', mem (s `&` fset1 x) x' <=> mem s x /\ x' = x.
proof. by move=> x'; rewrite in_fsetI in_fset1. qed.

lemma in_fsetD1 (s : 'a fset) x:
  forall x', mem (s `\` fset1 x) x' <=> mem s x' /\ x' <> x.
proof. by move=> x'; rewrite in_fsetD in_fset1. qed.

(* -------------------------------------------------------------------- *)
op pick ['a] (A : 'a fset) = head witness (elems A)
axiomatized by pickE.

lemma pick0: pick<:'a> fset0 = witness.
proof. by rewrite pickE elems_fset0. qed.

lemma mem_pick (A : 'a fset): A <> fset0 => mem A (pick A).
proof.
move=> /(contra _ _ (elems_eq_fset0 A)); rewrite pickE memE.
by move=> /(mem_head_behead witness) <-.
qed.

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
proof. by apply/fsetP=> x; rewrite !(inE,in_filter) andb_orr. qed.

lemma filterI (p : 'a -> bool) (A B : 'a fset):
  filter p (A `&` B) = filter p A `&` filter p B.
proof. by apply/fsetP=> x; rewrite !(inE,in_filter) andbACA andbb. qed.

lemma filterD (p : 'a -> bool) (A B : 'a fset):
  filter p (A `\` B) = filter p A `\` filter p B.
proof.
apply/fsetP=> x; rewrite !(inE,in_filter) !negb_and andb_orr.
by rewrite andbAC andbN andbA.
qed.

lemma filter_pred0 (A : 'a fset): filter pred0 A = fset0.
proof. by apply/fsetP=> x; rewrite in_fset0 in_filter. qed.

lemma filter_pred1 (a : 'a) (A : 'a fset):
  filter (pred1 a) A = if mem A a then fset1 a else fset0.
proof.
apply/fsetP=> x; rewrite in_filter fun_if2 !inE.
by case (x = a)=> @/pred1 ->.
qed.

lemma filter_mem (A B : 'a fset): filter (mem A) B = A `&` B.
proof. by apply/fsetP=> x; rewrite in_fsetI in_filter. qed.

lemma filter_memC (A B : 'a fset): filter (predC (mem A)) B = B `\` A.
proof. by apply/fsetP=> x; rewrite in_fsetD in_filter andbC. qed.

(* -------------------------------------------------------------------- *)
op (\subset) (s1 s2 : 'a fset) = forall x, x \in s1 => x \in s2.
op (\proper) (s1 s2 : 'a fset) = s1 \subset s2 /\ s1 <> s2.

lemma nosmt subsetP (s1 s2 : 'a fset):
  (s1 \subset s2) <=> (mem s1 <= mem s2).
proof. by []. qed.

lemma nosmt subset_trans (s1 s2 s3 : 'a fset): 
  s1 \subset s2 => s2 \subset s3 => s1 \subset s3.
proof. by move=> le1 le2 ? le3; apply/le2/le1. qed.

lemma properP (X Y : 'a fset) :
  X \proper Y <=> X \subset Y /\ exists y, y \in Y /\ ! y \in X.
proof.
rewrite /(\proper) &(andb_id2l) fsetP negb_forall /= => le_XY.
apply/eqboolP/exists_eq => x /=; rewrite -negb_imply; congr.
by rewrite iffE eqboolP &(andb_idl) => _; apply/le_XY.
qed.

(* -------------------------------------------------------------------- *)
lemma nosmt eqEsubset (A B : 'a fset) : (A = B) <=> (A \subset B) /\ (B \subset A).
proof. by rewrite fsetP 2!subsetP subpred_eqP. qed.

(* -------------------------------------------------------------------- *)
lemma nosmt fset_ind (p : 'a fset -> bool):
  p fset0 =>
  (forall x s, !mem s x => p s => p (s `|` (fset1 x))) =>
  (forall s, p s).
proof.
move=> p0 pa s; rewrite -elemsK.
elim (elems s) (uniq_elems s)=> {s} [|x s ih /cons_uniq []].
+ by rewrite -set0E.
rewrite -mem_oflist=> ^x_notin_s /pa + ^uniq_s /ih - h /h. (* FIXME: => h /h? *)
rewrite setUE elems_fset1.
rewrite (oflist_perm_eq (elems (oflist s) ++ [x]) (x::s)) //.
apply/perm_catCl=> /=; apply/perm_cons/perm_eq_sym.
by rewrite -{1}(undup_id _ uniq_s) oflistK.
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
proof.
by apply/fsetP=> y; rewrite fun_if2 !inE; case: (mem D x); case: (y = x).
qed.

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
proof.
by apply/fsetP=> y; rewrite fun_if2 !inE; case: (mem D x); case: (y = x).
qed.

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
lemma subsetIl (A B : 'a fset) : (A `&` B) \subset A.
proof. by apply/subsetP=> x; rewrite inE; case. qed.

lemma subsetIr (A B : 'a fset) : (A `&` B) \subset B.
proof. by apply/subsetP=> x; rewrite inE; case. qed.

(* -------------------------------------------------------------------- *)
lemma subsetDl (A B : 'a fset) : A `\` B \subset A.
proof. by apply/subsetP=> x; rewrite !inE; case. qed.

(* -------------------------------------------------------------------- *)
lemma sub0set (A : 'a fset) : fset0 \subset A.
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
rewrite -(perm_eq_size _ _ (oflistK s)) undup_id /s 2:size_cat //.
rewrite cat_uniq ?uniq_elems /= -implybF => /hasP [x [Bx Ax]].
by have:= h x; rewrite in_fsetI in_fset0 !memE Bx Ax.
qed.

lemma fcardUI (A B : 'a fset) :
  card (A `|` B) + card (A `&` B) = card A + card B.
proof.
rewrite -(fsetID (A `|` B) A) fsetUK (fsetUC A B) fsetDK.
rewrite fcardUI_indep.
+ by rewrite fsetIDA fsetDIl fsetDv fset0I.
by rewrite addzAC fsetIC -addzA -fcardUI_indep ?fsetID ?fsetII.
qed.

(* -------------------------------------------------------------------- *)
lemma nosmt fcardU (A B : 'a fset) :
  card (A `|` B) = card A + card B - card (A `&` B).
proof. by rewrite -fcardUI Ring.IntID.addrK. qed.

lemma nosmt fcardI (A B : 'a fset) :
  card (A `&` B) = card A + card B - card (A `|` B).
proof. by rewrite -fcardUI addzAC subzz. qed.

(* -------------------------------------------------------------------- *)
lemma nosmt fcardID (A B : 'a fset) :
  card (A `&` B) + card (A `\` B) = card A.
proof. by rewrite -fcardUI_indep ?fsetID // fsetII. qed.

lemma nosmt fcardD (A B : 'a fset) :
  card (A `\` B) = card A - card (A `&` B).
proof. by rewrite -(fcardID A B) addzAC subzz. qed.

(* -------------------------------------------------------------------- *)
lemma nosmt fcardD1 (A : 'a fset) (x : 'a) :
  card A = card (A `\` fset1 x) + (if mem A x then 1 else 0).
proof.
(* FIXME: This feels like it wasn't thought about very deeply... *)
case: (mem A x) => Ax //=; last first.
+ congr; apply/fsetP=> y; rewrite !inE.
  by move: Ax; case: (mem A y); case: (y = x).
rewrite -(fcard1 x) -fcardUI addzC eq_sym eq_fcards0 /=.
+ by apply/fsetP=> y; rewrite !inE; case: (y = x).
by congr; apply/fsetP=> y; rewrite !inE; case: (y = x).
qed.

(* -------------------------------------------------------------------- *)
lemma subset_fsetU_id (A B : 'a fset) :
  A \subset B => A `|` B = B.
proof.
move=> A_le_B; apply/fsetP=> x; rewrite in_fsetU.
by split=> [[/A_le_B|->]|->].
qed.

lemma subset_fsetI_id (A B : 'a fset) :
  B \subset A => A `&` B = B.
proof.
move=> B_le_A; apply/fsetP=> x; rewrite in_fsetI.
by split=> [[_ ->]|^x_in_B /B_le_A].
qed.

lemma subset_leq_fcard (A B : 'a fset) :
  A \subset B => card A <= card B.
proof.
move=> /subsetP le_AB; rewrite -(fcardID B A).
have ->: B `&` A = A; 1: apply/fsetP=> x.
  by rewrite in_fsetI andb_idl //; apply/le_AB.
by apply/ler_addl; apply/fcard_ge0.
qed.

(* -------------------------------------------------------------------- *)
lemma subset_cardP (A B : 'a fset) :
  card A = card B => (A = B <=> A \subset B).
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
  (A = B) <=> (A \subset B) /\ (card B <= card A).
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

lemma mem_image (f:'a->'b) (s:'a fset) x:
  mem s x => mem (image f s) (f x).
proof. by rewrite imageP=> ?;exists x. qed.

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
    by move=> [x']; rewrite in_fsetU=> -[[x'_in_A|x'_in_B] <-];
       [left|right]; exists x'.
  by move=> [[x'] [x'_in_X] <-|[x'] [x'_in_X] <-];
     exists x'; rewrite in_fsetU x'_in_X.
qed.

lemma nosmt imageI (f : 'a -> 'b) (A B : 'a fset):
  image f (A `&` B) \subset image f A `&` image f B.
proof.
  move=> x; rewrite !inE !imageP=> -[a].
  rewrite !inE=> -[[a_in_A a_in_B] <-].
  by split; exists a.
qed.

lemma nosmt imageD (f : 'a -> 'b) (A B : 'a fset):
  image f A `\` image f B \subset image f (A `\` B).
proof.
  move=> x; rewrite !inE !imageP=> -[[a] [a_in_A <-]].
  move=> h; exists a; rewrite !inE a_in_A /= -negP=> a_in_B.
  by move: h=> /=; exists a.
qed.

(* -------------------------------------------------------------------- *)
lemma nosmt fcard_image_leq (f : 'a -> 'b) (A : 'a fset):
  card (image f A) <= card A.
proof.
  elim/fset_ind: A=> [|x A x_notin_A ih]; 1: by rewrite image0 !fcards0.
  rewrite imageU image1 (lez_trans (card (image f A) + 1)).
    by rewrite fcardU fcard1 ler_naddr 1:oppr_le0 1:fcard_ge0.
  rewrite fcardU fsetI1 x_notin_A fcards0 fcard1 oppz0 addz0.
  by rewrite ler_add2r.
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
