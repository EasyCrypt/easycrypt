(* This theory should make use of theories for groups.
   It is currently mostly being developed towards getting
   fixed-length bitstrings formalized as boolean rings,
   automatically yielding many useful lemmas from a
   small number of simple core axioms. *)
theory Ring.
  type ring.

  (** Ring addition *)
  const zero: ring.
  op ( + ) : ring -> ring -> ring.
  op [ - ] : ring -> ring.

  axiom addrA (r1 r2 r3 : ring):
    (r1 + r2) + r3 = r1 + (r2 + r3).

  axiom addrC (r1 r2 : ring):
    r1 + r2 = r2 + r1.

  axiom add0r (r : ring):
    zero + r = r.

  axiom addNr (r : ring):
    r + -r = zero.

  (** Ring multiplication *)
  const one: ring.
  op ( * ): ring -> ring -> ring.

  axiom mulrA (r1 r2 r3 : ring):
    (r1 * r2) * r3 = r1 * (r2 * r3).

  axiom mul1r (r : ring):
    one * r = r.

  (** Distributivity of addition over multiplication *)
  axiom mulrDadd (r1 r2 r3 : ring):
    r1 * (r2 + r3)= (r1 * r2) + (r1 * r3).

  axiom mulDradd (r1 r2 r3 : ring):
    (r1 + r2) * r3 = (r1 * r3) + (r2 * r3).
end Ring.

theory RingT.
  clone import Ring.
  abbrev ( - ) (r1 r2 : ring) = r1 + -r2.

  (** Lemmas *)
  lemma addr0 (r : ring):
    r + zero = r.
  proof strict.
  by rewrite addrC add0r.
  qed.

  lemma addrN (r : ring):
    -r + r = zero.
  proof strict.
  by rewrite addrC addNr.
  qed.

  lemma addIr (r r1 r2 : ring):
    (r1 + r = r2 + r) =>
    r1 = r2.
  proof strict.
  by intros=> r1_r2;
     rewrite -addr0 -(addr0 r2) -(addNr r) -2!addrA -r1_r2.
  qed.

  lemma addrI (r r1 r2 : ring):
    (r + r1 = r + r2) =>
    r1 = r2.
  proof strict.
  by rewrite 2!(addrC r)=> r1_r2; rewrite (addIr r r1 r2).
  qed.
end RingT.

theory CRing.
  clone import Ring.

  axiom mulrC (r1 r2 : ring):
    r1 * r2 = r2 * r1.
end CRing.

theory CRingT.
  clone        Ring.
  clone        CRing with
    theory Ring <- Ring.
  clone        RingT with
    theory Ring <- Ring.

  import Ring.
  import CRing.
  import RingT.

  lemma mulrC (r1 r2 : ring):
    r1 * r2 = r2 * r1.
  proof strict.
  by rewrite mulrC.
  qed.

  lemma mulrCA (r1 r2 r3 : ring):
    r1 * (r2 * r3) = r2 * (r1 * r3).
  proof strict.
  by rewrite -2!mulrA (mulrC r1).
  qed.

  lemma mulrAC (r1 r2 r3 : ring):
    (r1 * r2) * r3 = (r1 * r3) * r2.
  proof strict.
  by rewrite 2!mulrA (mulrC r2).
  qed.

  lemma mulrACA (r1 r2 r3 r4 : ring):
    (r1 * r2) * (r3 * r4) = (r1 * r3) * (r2 * r4).
  proof strict.
  by rewrite mulrA (mulrCA r2) -mulrA.
  qed.
end CRingT.

theory BRing.
  clone import Ring.

  axiom mulrK (r : ring):
    r * r = r.
end BRing.

theory BRingT.
  clone        Ring.
  clone        RingT with
    theory Ring <- Ring.
  clone        BRing with
    theory Ring <- Ring.

  import Ring.
  import RingT.
  import BRing.

  lemma neg_is_id (r : ring):
    r + r = zero.
  proof strict.
  by rewrite -(addIr (r + r) (r + r) zero) //
             (add0r (r + r)) -(mulrK r) -{1 2}mulrDadd -mulDradd 2!mulrK.
  qed.

  lemma mulrC (r1 r2 : ring):
    r1 * r2 = r2 * r1.
  proof strict.
  by rewrite -(addIr (r2 * r1) (r1 * r2) (r2 * r1)) // (neg_is_id (r2 * r1))
             -(addIr r2 (r1 * r2 + r2 * r1) zero) // (add0r r2) addrA
             -{4}(addrI r1 (r1 * r2 + (r2 * r1 + r2)) r2) // -addrA
             -{1}(mulrK r1) -{3}(mulrK r2) -2!mulrDadd -mulDradd mulrK.
  qed.
end BRingT.


(*
(* Example: Ring structures on bool *)
theory BoolRing.
require import Bool.
op id (b:bool) = b.
clone Ring as RBool with
  type ring = bool,
  op zero = false,
  op ( + ) = (^^),
  op [ - ] = id,
  op one = true,
  op ( * ) = (/\)
  proof * by (delta; smt).

clone BRing as BRBool with
  theory Ring = RBool
  proof * by (intros=> r; delta; smt).

clone BRingT as BRBoolT with
  theory Ring = RBool.

print theory BRBoolT.
*)