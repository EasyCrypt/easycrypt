(* --------------------------------------------------------------------
 * Copyright (c) - 2012-2015 - IMDEA Software Institute and INRIA
 * Distributed under the terms of the CeCILL-B licence.
 * -------------------------------------------------------------------- *)

(* This API has been mostly inspired from the [ssrbool] library of the
 * ssreflect Coq extension. *)

require import Fun.

pragma +implicits.

(* -------------------------------------------------------------------- *)
(* These should be declared as externals (SMT-LIB knows them)
   external (\x): bool -> bool -> bool.
   external ite : bool -> bool -> bool -> bool. *)

op (&&) b1 b2 = if b1 then b2 else false.
op (||) b1 b2 = if b1 then true else b2.
op (^) b1 b2  = if b1 then !b2 else b2.

(* -------------------------------------------------------------------- *)
(* Negation lemmas. *)
lemma negbT b  : b = false => !b by [].
lemma negbTE b : !b => b = false by [].
lemma negbF b  : b => !b = false by [].
lemma negbFE b : !b = false => b by [].
lemma negbK    : involutive [!]  by case. (* FIXME: by []: "Not a formula: x1" *)
lemma negbNE b : !!b => b        by [].

lemma negb_inj : injective [!]      by exact: (can_inj negbK).
lemma negbLR b c : b = !c => !b = c by [].
lemma negbRL b c : !b = c => b = !c by [].

lemma contra (c b : bool) : (c => b) => !b => !c   by [].

lemma contraL (c b : bool) : (c => !b) => b => !c  by [].

lemma contraR (c b : bool) : (!c => b) => !b => c  by [].

lemma contraLR (c b : bool) : (!c => !b) => b => c by [].

lemma contraT b : (!b => false) => b               by [].

lemma wlog_neg b : (!b => b) => b                  by [].

lemma contraFT (c b : bool) : (!c => b) => b = false => c
by [].

lemma contraFN (c b : bool) : (c => b) => b = false => !c
by [].

lemma contraTF (c b : bool) : (c => !b) => b => c = false
by [].

lemma contraNF (c b : bool) : (c => b) => !b => c = false
by [].

lemma contraFF (c b : bool) : (c => b) => b = false => c = false
by [].

(* -------------------------------------------------------------------- *)
(* Lemmas for ifs *)

lemma ifT b (vT vF : 'a) : b => (if b then vT else vF) = vT         by [].
lemma ifF b (vT vF : 'a) : b = false => (if b then vT else vF) = vF by [].
lemma ifN b (vT vF : 'a) : !b => (if b then vT else vF) = vF        by [].

lemma if_same b (vT : 'a) : (if b then vT else vT) = vT
by [].

lemma if_neg b (vT vF : 'a) :
  (if !b then vT else vF) = if b then vF else vT
by [].

lemma fun_if (f : 'a -> 'b) b vT vF:
  f (if b then vT else vF) = if b then f vT else f vF
by [].

lemma if_arg b x (fT fF : 'a -> 'b) :
  (if b then fT else fF) x = if b then fT x else fF x
by [].

(* -------------------------------------------------------------------- *)
(* Boolean connectives laws. *)

lemma andTb : left_id true (/\)       by case.
lemma andFb : left_zero false (/\)    by case.
lemma andbT : right_id true (/\)      by case.
lemma andbF : right_zero false (/\)   by case.
lemma andbb : idempotent (/\)         by case.
lemma andbC : commutative (/\)        by do 2!case.
lemma andbA : associative (/\)        by do 3!case.
lemma andbCA : left_commutative (/\)  by do 3!case.
lemma andbAC : right_commutative (/\) by do 3!case.
lemma andbACA : interchange (/\) (/\) by do 4!case.

lemma orTb : forall b, true \/ b     by case.
lemma orFb : left_id false (\/)      by case.
lemma orbT : forall b, b \/ true     by case.
lemma orbF : right_id false (\/)     by case.
lemma orbb : idempotent (\/)         by case.
lemma orbC : commutative (\/)        by do 2!case.
lemma orbA : associative (\/)        by do 3!case.
lemma orbCA : left_commutative (\/)  by do 3!case.
lemma orbAC : right_commutative (\/) by do 3!case.
lemma orbACA : interchange (\/) (\/) by do 4!case.

lemma andbN b : (b /\ !b) <=> false by case: b.
lemma andNb b : (!b /\ b) <=> false by case: b.
lemma orbN b  : (b \/ !b) <=> true  by case: b.
lemma orNb b  : (!b \/ b) <=> true  by case: b.

lemma andb_orl : left_distributive (/\) (\/)  by do 3!case.
lemma andb_orr : right_distributive (/\) (\/) by do 3!case.
lemma orb_andl : left_distributive (\/) (/\)  by do 3!case.
lemma orb_andr : right_distributive (\/) (/\) by do 3!case.

lemma andb_idl (a b : bool) : (b => a) => a /\ b <=> b
by [].

lemma andb_idr (a b : bool) : (a => b) => a /\ b <=> a
by [].

lemma andb_id2l (a b c : bool) : (a => b = c) => a /\ b <=> a /\ c
by [].

lemma andb_id2r (a b c : bool) : (b => a = c) => a /\ b <=> c /\ b
by [].

lemma orb_idl (a b : bool) : (a => b) => a \/ b <=> b
by [].

lemma orb_idr (a b : bool) : (b => a) => a \/ b <=> a
by [].

lemma orb_id2l (a b c : bool) : (!a => b = c) => a \/ b <=> a \/ c
by [].

lemma orb_id2r (a b c : bool) : (!b => a = c) => a \/ b <=> c \/ b
by [].

lemma negb_and (a b : bool) : !(a /\ b) <=> !a \/ !b
by [].

lemma negb_or (a b : bool) : !(a \/ b) <=> !a /\ !b
by [].

(* -------------------------------------------------------------------- *)
(* Absorption *)

lemma andbK a b : a /\ b \/ a <=> a  by [].
lemma andKb a b : a \/ b /\ a <=> a  by [].
lemma orbK a b : (a \/ b) /\ a <=> a by [].
lemma orKb a b : a /\ (b \/ a) <=> a by [].

(* -------------------------------------------------------------------- *)
(* Imply *)

lemma implybT b : b => true         by [].
lemma implybF b : (b => false) = !b by [].
lemma implyFb b : false => b        by [].
lemma implyTb b : (true => b) = b   by [].
lemma implybb b : b => b            by [].

lemma negb_imply a b : !(a => b) <=> a /\ !b
by [].

lemma implybE a b : (a => b) <=> !a \/ b
by [].

lemma implyNb a b : (!a => b) <=> a \/ b
by [].

lemma implybN a b : (a => !b) <=> (b => !a)
by [].

lemma implybNN a b : (!a => !b) <=> b => a
by [].

lemma implyb_idl (a b : bool) : (!a => b) => (a => b) <=> b
by [].

lemma implyb_idr (a b : bool) : (b => !a) => (a => b) <=> !a
by [].

lemma implyb_id2l (a b c : bool) :
  (a => b <=> c) => (a => b) <=> (a => c)
by [].

(* -------------------------------------------------------------------- *)
(* Addition (xor) *)

lemma addFb : left_id false (^)               by case.
lemma addbF : right_id false (^)              by case.
lemma addbb : self_inverse false (^)          by case.
lemma addbC : commutative (^)                 by do 2!case.
lemma addbA : associative (^)                 by do 3!case.
lemma addbCA : left_commutative (^)           by do 3!case.
lemma addbAC : right_commutative (^)          by do 3!case.
lemma addbACA : interchange (^) (^)           by do 4!case.
lemma andb_addl : left_distributive (/\) (^)  by do 3!case.
lemma andb_addr : right_distributive (/\) (^) by do 3!case.
lemma addKb : left_loop idfun (^)             by do 2!case.
lemma addbK : right_loop idfun (^)            by do 2!case.
lemma addIb : left_injective (^)              by do 3!case.
lemma addbI : right_injective (^)             by do 3!case.

lemma addTb b : true ^ b <=> !b by case: b.
lemma addbT b : b ^ true <=> !b by case: b.

lemma addbN a b : a ^ !b <=> !(a ^ b) by case: a b.
lemma addNb a b : !a ^ b <=> !(a ^ b) by case: a b.

lemma addbP a b : (!a <=> b) <=> (a ^ b) by case: a b.

(* -------------------------------------------------------------------- *)
(* Short-circuiting *)

lemma andabP b1 b2 : b1 && b2 <=> b1 /\ b2 by [].
lemma orabP  b1 b2 : b1 || b2 <=> b1 \/ b2 by [].

lemma andab_andb : (&&) = (/\).
proof. by apply/ExtEq.rel_ext=> x y; rewrite andabP. qed.

lemma orab_orb : (||) = (\/).
proof. by apply/ExtEq.rel_ext=> x y; rewrite orabP. qed.

(* -------------------------------------------------------------------- *)
(* Pred? *)
(* Rel?  *)

(* -------------------------------------------------------------------- *)
(* Some things that may be needed in addition to ssrbool,
   but maybe better structured than currently *)
(*
lemma bool_case p: p true => p false => (forall b, p b) by [].

(* views on iff: eq_iff, iffLR, iffRL ... *)
(* congruence and rewriting               *)
(* ...                                    *)
*)
