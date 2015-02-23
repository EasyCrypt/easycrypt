(* --------------------------------------------------------------------
 * Copyright (c) - 2012-2015 - IMDEA Software Institute and INRIA
 * Distributed under the terms of the CeCILL-C license
 * -------------------------------------------------------------------- *)

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

lemma uniq_elems (s : 'a fset): uniq (elems s).
proof.
  rewrite -(elemsK s); move: (elems s) => {s} s.
  by rewrite -(perm_eq_uniq (undup s)) ?(undup_uniq, oflistK).
qed.

axiom fset_eq (s1 s2 : 'a fset):
  (perm_eq (elems s1) (elems s2)) => (s1 = s2).

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
proof.
  by split=> [-> | h] //; apply/fset_eq; rewrite uniq_perm_eq;
    rewrite 1?uniq_elems // => x; move: (h x); rewrite !memE.
qed.

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
proof. by move=> x; rewrite setUE mem_oflist mem_cat !memE. qed.

lemma in_setI (s1 s2 : 'a fset):
  forall x, mem (setI s1 s2) x <=> mem s1 x /\ mem s2 x.
proof. by move=> x; rewrite setIE mem_oflist mem_filter !memE. qed.

lemma in_setD (s1 s2 : 'a fset):
  forall x, mem (setD s1 s2) x <=> mem s1 x /\ !mem s2 x.
proof. by move=> x; rewrite setDE mem_oflist mem_filter /predC !memE. qed.

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


(* -------------------------------------------------------------------- *)
(* All the following proofs should be translated automagically          *)
(* -------------------------------------------------------------------- *)

(*
Section setOps.

Variable T : finType.
Implicit Types (a x : T) (A B C D : {set T}) (pA pB pC : pred T).

Lemma eqEsubset A B : (A == B) = (A \subset B) && (B \subset A).
Proof. by apply/eqP/subset_eqP=> /setP. Qed.

Lemma subEproper A B : A \subset B = (A == B) || (A \proper B).
Proof. by rewrite eqEsubset -andb_orr orbN andbT. Qed.

Lemma eqVproper A B : A \subset B -> A = B \/ A \proper B.
Proof. by rewrite subEproper => /predU1P. Qed.

Lemma properEneq A B : A \proper B = (A != B) && (A \subset B).
Proof. by rewrite andbC eqEsubset negb_and andb_orr andbN. Qed.

Lemma proper_neq A B : A \proper B -> A != B.
Proof. by rewrite properEneq; case/andP. Qed.

Lemma eqEproper A B : (A == B) = (A \subset B) && ~~ (A \proper B).
Proof. by rewrite negb_and negbK andb_orr andbN eqEsubset. Qed.

Lemma eqEcard A B : (A == B) = (A \subset B) && (#|B| <= #|A|).
Proof.
rewrite eqEsubset; apply: andb_id2l => sAB.
by rewrite (geq_leqif (subset_leqif_card sAB)).
Qed.

Lemma properEcard A B : (A \proper B) = (A \subset B) && (#|A| < #|B|).
Proof. by rewrite properEneq ltnNge andbC eqEcard; case: (A \subset B). Qed.

Lemma subset_leqif_cards A B : A \subset B -> (#|A| <= #|B| ?= iff (A == B)).
Proof. by move=> sAB; rewrite eqEsubset sAB; exact: subset_leqif_card. Qed.

Lemma in_set0 x : x \in set0 = false.
Proof. by rewrite inE. Qed.

Lemma sub0set A : set0 \subset A.
Proof. by apply/subsetP=> x; rewrite inE. Qed.

Lemma subset0 A : (A \subset set0) = (A == set0).
Proof. by rewrite eqEsubset sub0set andbT. Qed.

Lemma proper0 A : (set0 \proper A) = (A != set0).
Proof. by rewrite properE sub0set subset0. Qed.

Lemma subset_neq0 A B : A \subset B -> A != set0 -> B != set0.
Proof. by rewrite -!proper0 => sAB /proper_sub_trans->. Qed.

Lemma set_0Vmem A : (A = set0) + {x : T | x \in A}.
Proof.
case: (pickP (mem A)) => [x Ax | A0]; [by right; exists x | left].
apply/setP=> x; rewrite inE; exact: A0.
Qed.

Lemma enum_set0 : enum set0 = [::] :> seq T.
Proof. by rewrite (eq_enum (in_set _)) enum0. Qed.

Lemma subsetT A : A \subset setT.
Proof. by apply/subsetP=> x; rewrite inE. Qed.

Lemma subsetT_hint mA : subset mA (mem [set: T]).
Proof. by rewrite unlock; apply/pred0P=> x; rewrite !inE. Qed.
Hint Resolve subsetT_hint.

Lemma subTset A : (setT \subset A) = (A == setT).
Proof. by rewrite eqEsubset subsetT. Qed.

Lemma properT A : (A \proper setT) = (A != setT).
Proof. by rewrite properEneq subsetT andbT. Qed.

Lemma set1P x a : reflect (x = a) (x \in [set a]).
Proof. by rewrite inE; exact: eqP. Qed.

Lemma enum_setT : enum [set: T] = Finite.enum T.
Proof. by rewrite (eq_enum (in_set _)) enumT. Qed.

Lemma in_set1 x a : (x \in [set a]) = (x == a).
Proof. exact: in_set. Qed.

Lemma set11 x : x \in [set x].
Proof. by rewrite inE. Qed.

Lemma set1_inj : injective (@set1 T).
Proof. by move=> a b eqsab; apply/set1P; rewrite -eqsab set11. Qed.

Lemma enum_set1 a : enum [set a] = [:: a].
Proof. by rewrite (eq_enum (in_set _)) enum1. Qed.

Lemma setU1P x a B : reflect (x = a \/ x \in B) (x \in a |: B).
Proof. by rewrite !inE; exact: predU1P. Qed.

Lemma in_setU1 x a B : (x \in a |: B) = (x == a) || (x \in B).
Proof. by rewrite !inE. Qed.

Lemma set_cons a s : [set x in a :: s] = a |: [set x in s].
Proof. by apply/setP=> x; rewrite !inE. Qed.

Lemma setU11 x B : x \in x |: B.
Proof. by rewrite !inE eqxx. Qed.

Lemma setU1r x a B : x \in B -> x \in a |: B.
Proof. by move=> Bx; rewrite !inE predU1r. Qed.

(* We need separate lemmas for the explicit enumerations since they *)
(* associate on the left.                                           *)
Lemma set1Ul x A b : x \in A -> x \in A :|: [set b].
Proof. by move=> Ax; rewrite !inE Ax. Qed.

Lemma set1Ur A b : b \in A :|: [set b].
Proof. by rewrite !inE eqxx orbT. Qed.

Lemma in_setC1 x a : (x \in [set~ a]) = (x != a).
Proof. by rewrite !inE. Qed.

Lemma setC11 x : (x \in [set~ x]) = false.
Proof. by rewrite !inE eqxx. Qed.

Lemma setD1P x A b : reflect (x != b /\ x \in A) (x \in A :\ b).
Proof. rewrite !inE; exact: andP. Qed.

Lemma in_setD1 x A b : (x \in A :\ b) = (x != b) && (x \in A) .
Proof. by rewrite !inE. Qed.

Lemma setD11 b A : (b \in A :\ b) = false.
Proof. by rewrite !inE eqxx. Qed.

Lemma setD1K a A : a \in A -> a |: (A :\ a) = A.
Proof. by move=> Aa; apply/setP=> x; rewrite !inE; case: eqP => // ->. Qed.

Lemma setU1K a B : a \notin B -> (a |: B) :\ a = B.
Proof.
by move/negPf=> nBa; apply/setP=> x; rewrite !inE; case: eqP => // ->.
Qed.

Lemma set2P x a b : reflect (x = a \/ x = b) (x \in [set a; b]).
Proof. rewrite !inE; exact: pred2P. Qed.

Lemma in_set2 x a b : (x \in [set a; b]) = (x == a) || (x == b).
Proof. by rewrite !inE. Qed.

Lemma set21 a b : a \in [set a; b].
Proof. by rewrite !inE eqxx. Qed.

Lemma set22 a b : b \in [set a; b].
Proof. by rewrite !inE eqxx orbT. Qed.

Lemma setUP x A B : reflect (x \in A \/ x \in B) (x \in A :|: B).
Proof. by rewrite !inE; exact: orP. Qed.

Lemma in_setU x A B : (x \in A :|: B) = (x \in A) || (x \in B).
Proof. exact: in_set. Qed.

Lemma setUC A B : A :|: B = B :|: A.
Proof. by apply/setP => x; rewrite !inE orbC. Qed.

Lemma setUS A B C : A \subset B -> C :|: A \subset C :|: B.
Proof.
move=> sAB; apply/subsetP=> x; rewrite !inE.
by case: (x \in C) => //; exact: (subsetP sAB).
Qed.

Lemma setSU A B C : A \subset B -> A :|: C \subset B :|: C.
Proof. by move=> sAB; rewrite -!(setUC C) setUS. Qed.

Lemma setUSS A B C D : A \subset C -> B \subset D -> A :|: B \subset C :|: D.
Proof. by move=> /(setSU B) /subset_trans sAC /(setUS C)/sAC. Qed.

Lemma set0U A : set0 :|: A = A.
Proof. by apply/setP => x; rewrite !inE orFb. Qed.

Lemma setU0 A : A :|: set0 = A.
Proof. by rewrite setUC set0U. Qed.

Lemma setUA A B C : A :|: (B :|: C) = A :|: B :|: C.
Proof. by apply/setP => x; rewrite !inE orbA. Qed.

Lemma setUCA A B C : A :|: (B :|: C) = B :|: (A :|: C).
Proof. by rewrite !setUA (setUC B). Qed.

Lemma setUAC A B C : A :|: B :|: C = A :|: C :|: B.
Proof. by rewrite -!setUA (setUC B). Qed.

Lemma setUACA A B C D : (A :|: B) :|: (C :|: D) = (A :|: C) :|: (B :|: D).
Proof. by rewrite -!setUA (setUCA B). Qed.

Lemma setTU A : setT :|: A = setT.
Proof. by apply/setP => x; rewrite !inE orTb. Qed.

Lemma setUT A : A :|: setT = setT.
Proof. by rewrite setUC setTU. Qed.

Lemma setUid A : A :|: A = A.
Proof. by apply/setP=> x; rewrite inE orbb. Qed.

Lemma setUUl A B C : A :|: B :|: C = (A :|: C) :|: (B :|: C).
Proof. by rewrite setUA !(setUAC _ C) -(setUA _ C) setUid. Qed.

Lemma setUUr A B C : A :|: (B :|: C) = (A :|: B) :|: (A :|: C).
Proof. by rewrite !(setUC A) setUUl. Qed.

(* intersection *)

(* setIdP is a generalisation of setIP that applies to comprehensions. *)
Lemma setIdP x pA pB : reflect (pA x /\ pB x) (x \in [set y | pA y & pB y]).
Proof. by rewrite !inE; exact: andP. Qed.

Lemma setId2P x pA pB pC :
  reflect [/\ pA x, pB x & pC x] (x \in [set y | pA y & pB y && pC y]).
Proof. by rewrite !inE; exact: and3P. Qed.

Lemma setIdE A pB : [set x in A | pB x] = A :&: [set x | pB x].
Proof. by apply/setP=> x; rewrite !inE. Qed.

Lemma setIP x A B : reflect (x \in A /\ x \in B) (x \in A :&: B).
Proof. exact: (iffP (@setIdP _ _ _)). Qed.

Lemma in_setI x A B : (x \in A :&: B) = (x \in A) && (x \in B).
Proof. exact: in_set. Qed.

Lemma setIC A B : A :&: B = B :&: A.
Proof. by apply/setP => x; rewrite !inE andbC. Qed.

Lemma setIS A B C : A \subset B -> C :&: A \subset C :&: B.
Proof.
move=> sAB; apply/subsetP=> x; rewrite !inE.
by case: (x \in C) => //; exact: (subsetP sAB).
Qed.

Lemma setSI A B C : A \subset B -> A :&: C \subset B :&: C.
Proof. by move=> sAB; rewrite -!(setIC C) setIS. Qed.

Lemma setISS A B C D : A \subset C -> B \subset D -> A :&: B \subset C :&: D.
Proof. by move=> /(setSI B) /subset_trans sAC /(setIS C) /sAC. Qed.

Lemma setTI A : setT :&: A = A.
Proof. by apply/setP => x; rewrite !inE andTb. Qed.

Lemma setIT A : A :&: setT = A.
Proof. by rewrite setIC setTI. Qed.

Lemma set0I A : set0 :&: A = set0.
Proof. by apply/setP => x; rewrite !inE andFb. Qed.

Lemma setI0 A : A :&: set0 = set0.

Proof. by rewrite setIC set0I. Qed.

Lemma setIA A B C : A :&: (B :&: C) = A :&: B :&: C.
Proof. by apply/setP=> x; rewrite !inE andbA. Qed.

Lemma setICA A B C : A :&: (B :&: C) = B :&: (A :&: C).
Proof. by rewrite !setIA (setIC A). Qed.

Lemma setIAC A B C : A :&: B :&: C = A :&: C :&: B.
Proof. by rewrite -!setIA (setIC B). Qed.

Lemma setIACA A B C D : (A :&: B) :&: (C :&: D) = (A :&: C) :&: (B :&: D).
Proof. by rewrite -!setIA (setICA B). Qed.

Lemma setIid A : A :&: A = A.
Proof. by apply/setP=> x; rewrite inE andbb. Qed.

Lemma setIIl A B C : A :&: B :&: C = (A :&: C) :&: (B :&: C).
Proof. by rewrite setIA !(setIAC _ C) -(setIA _ C) setIid. Qed.

Lemma setIIr A B C : A :&: (B :&: C) = (A :&: B) :&: (A :&: C).
Proof. by rewrite !(setIC A) setIIl. Qed.

(* distribute /cancel *)

Lemma setIUr A B C : A :&: (B :|: C) = (A :&: B) :|: (A :&: C).
Proof. by apply/setP=> x; rewrite !inE andb_orr. Qed.

Lemma setIUl A B C : (A :|: B) :&: C = (A :&: C) :|: (B :&: C).
Proof. by apply/setP=> x; rewrite !inE andb_orl. Qed.

Lemma setUIr A B C : A :|: (B :&: C) = (A :|: B) :&: (A :|: C).
Proof. by apply/setP=> x; rewrite !inE orb_andr. Qed.

Lemma setUIl A B C : (A :&: B) :|: C = (A :|: C) :&: (B :|: C).
Proof. by apply/setP=> x; rewrite !inE orb_andl. Qed.

Lemma setUK A B : (A :|: B) :&: A = A.
Proof. by apply/setP=> x; rewrite !inE orbK. Qed.

Lemma setKU A B : A :&: (B :|: A) = A.
Proof. by apply/setP=> x; rewrite !inE orKb. Qed.

Lemma setIK A B : (A :&: B) :|: A = A.
Proof. by apply/setP=> x; rewrite !inE andbK. Qed.

Lemma setKI A B : A :|: (B :&: A) = A.
Proof. by apply/setP=> x; rewrite !inE andKb. Qed.

(* complement *)

Lemma setCP x A : reflect (~ x \in A) (x \in ~: A).
Proof. by rewrite !inE; exact: negP. Qed.

Lemma in_setC x A : (x \in ~: A) = (x \notin A).
Proof. exact: in_set. Qed.

Lemma setCK : involutive (@setC T).
Proof. by move=> A; apply/setP=> x; rewrite !inE negbK. Qed.

Lemma setC_inj : injective (@setC T).
Proof. exact: can_inj setCK. Qed.

Lemma subsets_disjoint A B : (A \subset B) = [disjoint A & ~: B].
Proof. by rewrite subset_disjoint; apply: eq_disjoint_r => x; rewrite !inE. Qed.

Lemma disjoints_subset A B : [disjoint A & B] = (A \subset ~: B).
Proof. by rewrite subsets_disjoint setCK. Qed.

Lemma powersetCE A B : (A \in powerset (~: B)) = [disjoint A & B].
Proof. by rewrite inE disjoints_subset. Qed.

Lemma setCS A B : (~: A \subset ~: B) = (B \subset A).
Proof. by rewrite !subsets_disjoint setCK disjoint_sym. Qed.

Lemma setCU A B : ~: (A :|: B) = ~: A :&: ~: B.
Proof. by apply/setP=> x; rewrite !inE negb_or. Qed.

Lemma setCI A B : ~: (A :&: B) = ~: A :|: ~: B.
Proof. by apply/setP=> x; rewrite !inE negb_and. Qed.

Lemma setUCr A : A :|: ~: A = setT.
Proof. by apply/setP=> x; rewrite !inE orbN. Qed.

Lemma setICr A : A :&: ~: A = set0.
Proof. by apply/setP=> x; rewrite !inE andbN. Qed.

Lemma setC0 : ~: set0 = [set: T].
Proof. by apply/setP=> x; rewrite !inE. Qed.

Lemma setCT : ~: [set: T] = set0.
Proof. by rewrite -setC0 setCK. Qed.

(* difference *)

Lemma setDP A B x : reflect (x \in A /\ x \notin B) (x \in A :\: B).
Proof. by rewrite inE andbC; exact: andP. Qed.

Lemma in_setD A B x : (x \in A :\: B) = (x \notin B) && (x \in A).
Proof. exact: in_set. Qed.

Lemma setDE A B : A :\: B = A :&: ~: B.
Proof. by apply/setP => x; rewrite !inE andbC. Qed.

Lemma setSD A B C : A \subset B -> A :\: C \subset B :\: C.
Proof. by rewrite !setDE; exact: setSI. Qed.

Lemma setDS A B C : A \subset B -> C :\: B \subset C :\: A.
Proof. by rewrite !setDE -setCS; exact: setIS. Qed.

Lemma setDSS A B C D : A \subset C -> D \subset B -> A :\: B \subset C :\: D.
Proof. by move=> /(setSD B) /subset_trans sAC /(setDS C) /sAC. Qed.

Lemma setD0 A : A :\: set0 = A.
Proof. by apply/setP=> x; rewrite !inE. Qed.

Lemma set0D A : set0 :\: A = set0.
Proof. by apply/setP=> x; rewrite !inE andbF. Qed.

Lemma setDT A : A :\: setT = set0.
Proof. by apply/setP=> x; rewrite !inE. Qed.

Lemma setTD A : setT :\: A = ~: A.
Proof. by apply/setP=> x; rewrite !inE andbT. Qed.

Lemma setDv A : A :\: A = set0.
Proof. by apply/setP=> x; rewrite !inE andNb. Qed.

Lemma setCD A B : ~: (A :\: B) = ~: A :|: B.
Proof. by rewrite !setDE setCI setCK. Qed.

Lemma setID A B : A :&: B :|: A :\: B = A.
Proof. by rewrite setDE -setIUr setUCr setIT. Qed.

Lemma setDUl A B C : (A :|: B) :\: C = (A :\: C) :|: (B :\: C).
Proof. by rewrite !setDE setIUl. Qed.

Lemma setDUr A B C : A :\: (B :|: C) = (A :\: B) :&: (A :\: C).
Proof. by rewrite !setDE setCU setIIr. Qed.

Lemma setDIl A B C : (A :&: B) :\: C = (A :\: C) :&: (B :\: C).
Proof. by rewrite !setDE setIIl. Qed.

Lemma setIDA A B C : A :&: (B :\: C) = (A :&: B) :\: C.
Proof. by rewrite !setDE setIA. Qed.

Lemma setIDAC A B C : (A :\: B) :&: C = (A :&: C) :\: B.
Proof. by rewrite !setDE setIAC. Qed.

Lemma setDIr A B C : A :\: (B :&: C) = (A :\: B) :|: (A :\: C).
Proof. by rewrite !setDE setCI setIUr. Qed.

Lemma setDDl A B C : (A :\: B) :\: C = A :\: (B :|: C).
Proof. by rewrite !setDE setCU setIA. Qed.

Lemma setDDr A B C : A :\: (B :\: C) = (A :\: B) :|: (A :&: C).
Proof. by rewrite !setDE setCI setIUr setCK. Qed.

(* powerset *)

Lemma powersetE A B : (A \in powerset B) = (A \subset B).
Proof. by rewrite inE. Qed.

Lemma powersetS A B : (powerset A \subset powerset B) = (A \subset B).
Proof.
apply/subsetP/idP=> [sAB | sAB C]; last by rewrite !inE => /subset_trans ->.
by rewrite -powersetE sAB // inE.
Qed.

Lemma powerset0 : powerset set0 = [set set0] :> {set {set T}}.
Proof. by apply/setP=> A; rewrite !inE subset0. Qed.

Lemma powersetT : powerset [set: T] = [set: {set T}].
Proof. by apply/setP=> A; rewrite !inE subsetT. Qed.

Lemma setI_powerset P A : P :&: powerset A = P ::&: A.
Proof. by apply/setP=> B; rewrite !inE. Qed.

(* cardinal lemmas for sets *)

Lemma cardsE pA : #|[set x in pA]| = #|pA|.
Proof. by apply: eq_card; exact: in_set. Qed.

Lemma sum1dep_card pA : \sum_(x | pA x) 1 = #|[set x | pA x]|.
Proof. by rewrite sum1_card cardsE. Qed.

Lemma sum_nat_dep_const pA n : \sum_(x | pA x) n = #|[set x | pA x]| * n.
Proof. by rewrite sum_nat_const cardsE. Qed.

Lemma cards0 : #|@set0 T| = 0.
Proof. by rewrite cardsE card0. Qed.

Lemma cards_eq0 A : (#|A| == 0) = (A == set0).
Proof. by rewrite (eq_sym A) eqEcard sub0set cards0 leqn0. Qed.

Lemma set0Pn A : reflect (exists x, x \in A) (A != set0).
Proof. by rewrite -cards_eq0; exact: existsP. Qed.

Lemma card_gt0 A : (0 < #|A|) = (A != set0).
Proof. by rewrite lt0n cards_eq0. Qed.

Lemma cards0_eq A : #|A| = 0 -> A = set0.
Proof. by move=> A_0; apply/setP=> x; rewrite inE (card0_eq A_0). Qed.

Lemma cards1 x : #|[set x]| = 1.
Proof. by rewrite cardsE card1. Qed.

Lemma cardsUI A B : #|A :|: B| + #|A :&: B| = #|A| + #|B|.
Proof. by rewrite !cardsE cardUI. Qed.

Lemma cardsU A B : #|A :|: B| = (#|A| + #|B| - #|A :&: B|)%N.
Proof. by rewrite -cardsUI addnK. Qed.

Lemma cardsI A B : #|A :&: B| = (#|A| + #|B| - #|A :|: B|)%N.
Proof. by rewrite  -cardsUI addKn. Qed.

Lemma cardsT : #|[set: T]| = #|T|.
Proof. by rewrite cardsE. Qed.

Lemma cardsID B A : #|A :&: B| + #|A :\: B| = #|A|.
Proof. by rewrite !cardsE cardID. Qed.

Lemma cardsD A B : #|A :\: B| = (#|A| - #|A :&: B|)%N.
Proof. by rewrite -(cardsID B A) addKn. Qed.

Lemma cardsC A : #|A| + #|~: A| = #|T|.
Proof. by rewrite cardsE cardC. Qed.

Lemma cardsCs A : #|A| = #|T| - #|~: A|.
Proof. by rewrite -(cardsC A) addnK. Qed.

Lemma cardsU1 a A : #|a |: A| = (a \notin A) + #|A|.
Proof. by rewrite -cardU1; apply: eq_card=> x; rewrite !inE. Qed.

Lemma cards2 a b : #|[set a; b]| = (a != b).+1.
Proof. by rewrite -card2; apply: eq_card=> x; rewrite !inE. Qed.

Lemma cardsC1 a : #|[set~ a]| = #|T|.-1.
Proof. by rewrite -(cardC1 a); apply: eq_card=> x; rewrite !inE. Qed.

Lemma cardsD1 a A : #|A| = (a \in A) + #|A :\ a|.
Proof.
by rewrite (cardD1 a); congr (_ + _); apply: eq_card => x; rewrite !inE.
Qed.

(* other inclusions *)

Lemma subsetIl A B : A :&: B \subset A.
Proof. by apply/subsetP=> x; rewrite inE; case/andP. Qed.

Lemma subsetIr A B : A :&: B \subset B.
Proof. by apply/subsetP=> x; rewrite inE; case/andP. Qed.

Lemma subsetUl A B : A \subset A :|: B.
Proof. by apply/subsetP=> x; rewrite inE => ->. Qed.

Lemma subsetUr A B : B \subset A :|: B.
Proof. by apply/subsetP=> x; rewrite inE orbC => ->. Qed.

Lemma subsetU1 x A : A \subset x |: A.
Proof. exact: subsetUr. Qed.

Lemma subsetDl A B : A :\: B \subset A.
Proof. by rewrite setDE subsetIl. Qed.

Lemma subD1set A x : A :\ x \subset A.
Proof. by rewrite subsetDl. Qed.

Lemma subsetDr A B : A :\: B \subset ~: B.
Proof. by rewrite setDE subsetIr. Qed.

Lemma sub1set A x : ([set x] \subset A) = (x \in A).
Proof. by rewrite -subset_pred1; apply: eq_subset=> y; rewrite !inE. Qed.

Lemma cards1P A : reflect (exists x, A = [set x]) (#|A| == 1).
Proof.
apply: (iffP idP) => [|[x ->]]; last by rewrite cards1.
rewrite eq_sym eqn_leq card_gt0 => /andP[/set0Pn[x Ax] leA1].
by exists x; apply/eqP; rewrite eq_sym eqEcard sub1set Ax cards1 leA1.
Qed.

Lemma subset1 A x : (A \subset [set x]) = (A == [set x]) || (A == set0).
Proof.
rewrite eqEcard cards1 -cards_eq0 orbC andbC.
by case: posnP => // A0; rewrite (cards0_eq A0) sub0set.
Qed.

Lemma powerset1 x : powerset [set x] = [set set0; [set x]].
Proof. by apply/setP=> A; rewrite !inE subset1 orbC. Qed.

Lemma setIidPl A B : reflect (A :&: B = A) (A \subset B).
Proof.
apply: (iffP subsetP) => [sAB | <- x /setIP[] //].
by apply/setP=> x; rewrite inE; apply: andb_idr; exact: sAB.
Qed.
Implicit Arguments setIidPl [A B].

Lemma setIidPr A B : reflect (A :&: B = B) (B \subset A).
Proof. rewrite setIC; exact: setIidPl. Qed.

Lemma cardsDS A B : B \subset A -> #|A :\: B| = (#|A| - #|B|)%N.
Proof. by rewrite cardsD => /setIidPr->. Qed.

Lemma setUidPl A B : reflect (A :|: B = A) (B \subset A).
Proof.
by rewrite -setCS (sameP setIidPl eqP) -setCU (inj_eq setC_inj); exact: eqP.
Qed.

Lemma setUidPr A B : reflect (A :|: B = B) (A \subset B).
Proof. rewrite setUC; exact: setUidPl. Qed.

Lemma setDidPl A B : reflect (A :\: B = A) [disjoint A & B].
Proof. rewrite setDE disjoints_subset; exact: setIidPl. Qed.

Lemma subIset A B C : (B \subset A) || (C \subset A) -> (B :&: C \subset A).
Proof. by case/orP; apply: subset_trans; rewrite (subsetIl, subsetIr). Qed.

Lemma subsetI A B C : (A \subset B :&: C) = (A \subset B) && (A \subset C).
Proof.
rewrite !(sameP setIidPl eqP) setIA; have [-> //| ] := altP (A :&: B =P A).
by apply: contraNF => /eqP <-; rewrite -setIA -setIIl setIAC.
Qed.

Lemma subsetIP A B C : reflect (A \subset B /\ A \subset C) (A \subset B :&: C).
Proof. by rewrite subsetI; exact: andP. Qed.

Lemma subsetIidl A B : (A \subset A :&: B) = (A \subset B).
Proof. by rewrite subsetI subxx. Qed.

Lemma subsetIidr A B : (B \subset A :&: B) = (B \subset A).
Proof. by rewrite setIC subsetIidl. Qed.

Lemma powersetI A B : powerset (A :&: B) = powerset A :&: powerset B.
Proof. by apply/setP=> C; rewrite !inE subsetI. Qed.

Lemma subUset A B C : (B :|: C \subset A) = (B \subset A) && (C \subset A).
Proof. by rewrite -setCS setCU subsetI !setCS. Qed.

Lemma subsetU A B C : (A \subset B) || (A \subset C) -> A \subset B :|: C.
Proof. by rewrite -!(setCS _ A) setCU; exact: subIset. Qed.

Lemma subUsetP A B C : reflect (A \subset C /\ B \subset C) (A :|: B \subset C).
Proof. by rewrite subUset; exact: andP. Qed.

Lemma subsetC A B : (A \subset ~: B) = (B \subset ~: A).
Proof. by rewrite -setCS setCK. Qed.

Lemma subCset A B : (~: A \subset B) = (~: B \subset A).
Proof. by rewrite -setCS setCK. Qed.

Lemma subsetD A B C : (A \subset B :\: C) = (A \subset B) && [disjoint A & C].
Proof. by rewrite setDE subsetI -disjoints_subset. Qed.

Lemma subDset A B C : (A :\: B \subset C) = (A \subset B :|: C).
Proof.
apply/subsetP/subsetP=> sABC x; rewrite !inE.
  by case Bx: (x \in B) => // Ax; rewrite sABC ?inE ?Bx.
by case Bx: (x \in B) => //; move/sABC; rewrite inE Bx.
Qed.

Lemma subsetDP A B C :
  reflect (A \subset B /\ [disjoint A & C]) (A \subset B :\: C).
Proof. by rewrite subsetD; exact: andP. Qed.

Lemma setU_eq0 A B : (A :|: B == set0) = (A == set0) && (B == set0).
Proof. by rewrite -!subset0 subUset. Qed.

Lemma setD_eq0 A B : (A :\: B == set0) = (A \subset B).
Proof. by rewrite -subset0 subDset setU0. Qed.

Lemma setI_eq0 A B : (A :&: B == set0) = [disjoint A & B].
Proof. by rewrite disjoints_subset -setD_eq0 setDE setCK. Qed.

Lemma disjoint_setI0 A B : [disjoint A & B] -> A :&: B = set0.
Proof. by rewrite -setI_eq0; move/eqP. Qed.

Lemma subsetD1 A B x : (A \subset B :\ x) = (A \subset B) && (x \notin A).
Proof. by rewrite setDE subsetI subsetC sub1set inE. Qed.

Lemma subsetD1P A B x : reflect (A \subset B /\ x \notin A) (A \subset B :\ x).
Proof. by rewrite subsetD1; exact: andP. Qed.

Lemma properD1 A x : x \in A -> A :\ x \proper A.
Proof.
move=> Ax; rewrite properE subsetDl; apply/subsetPn; exists x=> //.
by rewrite in_setD1 Ax eqxx.
Qed.

Lemma properIr A B : ~~ (B \subset A) -> A :&: B \proper B.
Proof. by move=> nsAB; rewrite properE subsetIr subsetI negb_and nsAB. Qed.

Lemma properIl A B : ~~ (A \subset B) -> A :&: B \proper A.
Proof. by move=> nsBA; rewrite properE subsetIl subsetI negb_and nsBA orbT. Qed.

Lemma properUr A B : ~~ (A \subset B) ->  B \proper A :|: B.
Proof. by rewrite properE subsetUr subUset subxx /= andbT. Qed.

Lemma properUl A B : ~~ (B \subset A) ->  A \proper A :|: B.
Proof. by move=> not_sBA; rewrite setUC properUr. Qed.

Lemma proper1set A x : ([set x] \proper A) -> (x \in A).
Proof. by move/proper_sub; rewrite sub1set. Qed.

Lemma properIset A B C : (B \proper A) || (C \proper A) -> (B :&: C \proper A).
Proof. by case/orP; apply: sub_proper_trans; rewrite (subsetIl, subsetIr). Qed.

Lemma properI A B C : (A \proper B :&: C) -> (A \proper B) && (A \proper C).
Proof.
move=> pAI; apply/andP.
by split; apply: (proper_sub_trans pAI); rewrite (subsetIl, subsetIr).
Qed.

Lemma properU A B C : (B :|: C \proper A) -> (B \proper A) && (C \proper A).
Proof.
move=> pUA; apply/andP.
by split; apply: sub_proper_trans pUA; rewrite (subsetUr, subsetUl).
Qed.

Lemma properD A B C : (A \proper B :\: C) -> (A \proper B) && [disjoint A & C].
Proof. by rewrite setDE disjoints_subset => /properI/andP[-> /proper_sub]. Qed.

End setOps.
*)
