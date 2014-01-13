(* -------------------------------------------------------------------- *)
require import Pred.
require import NewList.

(* -------------------------------------------------------------------- *)
(* Finite sets are abstractely represented as the quotient by
 * [perm_eq] of lists without duplicates. *)

type 'a fset.

op elems  : 'a fset -> 'a list.
op oflist : 'a list -> 'a fset.

axiom elemsK  (s : 'a fset): oflist (elems  s) = s.
axiom oflistK (s : 'a list): perm_eq (undup s) (elems (oflist s)).

(* We are still missing some properties on lists *)
lemma uniq_elems (s : 'a fset): uniq (elems s).
proof. admit. qed.

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

lemma setP (s1 s2 : 'a fset):
  (s1 = s2) <=> (forall x, mem s1 x <=> mem s2 x).
proof. split => [-> // |]. admit. qed.

(* -------------------------------------------------------------------- *)
op set0 ['a] = oflist [<:'a>] axiomatized by set0E.
op set1 ['a] (z : 'a) = oflist [z] axiomatized by set1E.

op setU ['a] (s1 s2 : 'a fset) = oflist (elems s1 ++ elems s2)
  axiomatized by setUE.

op setI ['a] (s1 s2 : 'a fset) = oflist (filter (mem s2) (elems s1))
  axiomatized by setIE.

op setD ['a] (s1 s2 : 'a fset) = oflist (filter (predC (mem s2)) (elems s1))
  axiomatized by setDE.

(* -------------------------------------------------------------------- *)
lemma in_set0: forall x, mem set0<:'a> x <=> false.
proof. by move=> x; rewrite set0E mem_oflist. qed.

lemma in_set1 z: forall x, mem (set1<:'a> z) x <=> x = z.
proof. by move=> x; rewrite set1E /= mem_oflist. qed.

lemma in_setU (s1 s2 : 'a fset):
  forall x, mem (setU s1 s2) x <=> mem s1 x \/ mem s2 x.
proof. by move=> x; rewrite setUE /= mem_oflist mem_cat memE. qed.

lemma in_setI (s1 s2 : 'a fset):
  forall x, mem (setI s1 s2) x <=> mem s1 x /\ mem s2 x.
proof. by move=> x; rewrite setIE /= mem_oflist mem_filter memE. qed.

lemma in_setD (s1 s2 : 'a fset):
  forall x, mem (setD s1 s2) x <=> mem s1 x /\ !mem s2 x.
proof. by move=> x; rewrite setDE /= mem_oflist mem_filter memE. qed.

(* -------------------------------------------------------------------- *)
pred (<=) (s1 s2 : 'a fset) = mem s1 <= mem s2.
pred (< ) (s1 s2 : 'a fset) = mem s1 <  mem s2.

lemma nosmt subsetE (s1 s2 : 'a fset):
  (s1 <= s2) <=> (mem s1 <= mem s2).
proof. by []. qed.

(* -------------------------------------------------------------------- *)
lemma nosmt eqEsubset (A B : 'a fset) : (A = B) <=> (A <= B) /\ (B <= A).
proof.
  (* FIX: subpred_eqP => should from [(mem A) (mem B)] by matching *)
  by rewrite setP !subsetE; rewrite (subpred_eqP (mem A) (mem B)).
qed.
