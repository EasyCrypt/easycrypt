(* This theory should make use of theories for groups.
   It is currently mostly being developed towards getting
   fixed-length bitstrings formalized as boolean rings,
   automatically yielding many useful lemmas from a
   small number of simple core axioms. *)
theory Ring.
  type ring.

  (** Ring addition *)
  const zero: ring.
  op ( + ): ring -> ring -> ring.
  op (-- ): ring -> ring.
  op ( - ) r1 r2 = r1 + --r2.

  axiom addrA: forall r1 r2 r3,
    (r1 + r2) + r3 = r1 + (r2 + r3).

  axiom addrC: forall r1 r2,
    r1 + r2 = r2 + r1.

  axiom add0r: forall r,
    zero + r = r.

  axiom addNr: forall r,
    r + --r = zero.

  (** Ring multiplication *)
  const one: ring.
  op ( * ): ring -> ring -> ring.

  axiom mulrA: forall r1 r2 r3,
    (r1 * r2) * r3 = r1 * (r2 * r3).

  axiom mul1r: forall r,
    one * r = r.

  (** Distributivity of addition over multiplication *)
  axiom mulrDadd: forall r1 r2 r3,
    r1 * (r2 + r3)= (r1 * r2) + (r1 * r3).

  axiom mulDradd: forall r1 r2 r3,
    (r1 + r2) * r3 = (r1 * r3) + (r2 * r3).


  (** Lemmas *)
  lemma addr0: forall r,
    r + zero = r
  by (intros=> r; rewrite addrC; apply add0r).

  lemma addrN: forall r,
    --r + r = zero
  by (intros=> r; rewrite addrC; apply addNr).

  lemma addIr: forall r r1 r2,
    (r1 + r = r2 + r) <=>
    r1 = r2.
  proof strict.
  intros=> r r1 r2; split=> r1_r2; last by congr=> //.
  cut subr: (((r1 + r) = (r2 + r)) <=> ((r1 + r) + --r = (r2 + r) + --r));
    last by generalize r1_r2; rewrite subr 2!addrA addNr 2!addr0.
    by split=> args_eq //; congr=> //.
  qed.

  lemma addrI: forall r r1 r2,
    (r + r1 = r + r2) <=>
    r1 = r2.
  proof strict.
  by intros=> r r1 r2; rewrite 2!(addrC r); apply addIr.
  qed.
end Ring.

theory CRing.
  clone Ring. import Ring.

  axiom mulrC: forall r1 r2,
    r1 * r2 = r2 * r1.
end CRing.

theory BooleanRing.
  clone Ring. import Ring.

  axiom mulK: forall r,
    r * r = r.

  lemma neg_is_id: forall r,
    r + r = zero.
  proof strict.
  intros=> r.
  rewrite -(addIr (r + r)) add0r. rewrite -4!(mulK r).
  cut addN_r_r: ((r + r) * (r + r) = r + r); first by apply mulK=> //.
  by generalize addN_r_r; rewrite mulDradd mulrDadd mulK -{3}(add0r (r + r)) addIr.
  qed.

  lemma mulrC: forall r1 r2,
    r1 * r2 = r2 * r1.
  proof strict.
  intros=> r1 r2;
  cut mulK_r1_r2 : ((r1 + r2) * (r1 + r2) = (r1 + r2)); first by apply mulK.
  by generalize mulK_r1_r2; rewrite mulDradd 2!mulrDadd 2!mulK addrA addrI -addrA
                                    -{4}(add0r r2) addIr -(neg_is_id (r2 * r1)) addIr.
  qed.
end BooleanRing.