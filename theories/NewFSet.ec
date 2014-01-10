(* -------------------------------------------------------------------- *)
require import NewList.

(* -------------------------------------------------------------------- *)
(* Finite sets are abstractely represented has the quotient by
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
op mem ['a] (s : 'a fset) (x : 'a) = mem (elems s) x
  axiomatized by memE.

lemma mem_oflist (s : 'a list):
  forall x, mem (oflist s) x <=> mem s x.
proof.
  intros=> x; rewrite !memE /= (perm_eq_mem _ (undup s)).
    by rewrite perm_eq_sym oflistK.
  by rewrite mem_undup.
qed.

(* -------------------------------------------------------------------- *)
op fset0 ['a] = oflist [<:'a>] axiomatized by fset0E.
op fset1 ['a] (z : 'a) = oflist [z] axiomatized by fset1E.

op fsetD ['a] (s1 s2 : 'a fset) = oflist (elems s1 ++ elems s2)
  axiomatized by fsetDE.

(* -------------------------------------------------------------------- *)
lemma mem_fset0: forall x, mem fset0<:'a> x <=> false.
proof. by intros=> x; rewrite fset0E mem_oflist. qed.

lemma mem_fset1 z: forall x, mem (fset1<:'a> z) x <=> x = z.
proof. by intros=> x; rewrite fset1E /= mem_oflist. qed.
