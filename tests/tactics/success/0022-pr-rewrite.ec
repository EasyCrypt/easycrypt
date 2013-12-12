require import Real.

module M = { 
  proc f () : bool = { return true;}
}.

lemma t1 &m : Pr[M.f() @ &m : !res] = Pr[M.f() @ &m : true] - Pr[M.f() @ &m : res].
proof -strict.
 rewrite Pr[mu_not].
 trivial.
qed.

lemma t2 &m : Pr[M.f() @ &m : res \/ false] = Pr[M.f() @ &m : res].
  smt.
qed.

lemma t3 &m : Pr[M.f() @ &m : res \/ false] = Pr[M.f() @ &m : res].
  rewrite Pr[mu_eq].
    trivial.
  trivial.
qed.

lemma t4 &m : Pr[M.f() @ &m : res \/ false] = Pr[M.f() @ &m : res].
  rewrite Pr[mu_or].
  rewrite (_ : Pr[M.f() @ &m : res /\ false] = Pr[M.f() @ &m : false]).
    rewrite Pr[mu_eq].
      trivial.
    trivial.
  rewrite Pr[mu_false].
  smt.
qed.

lemma t5 &m : Pr[M.f() @ &m : res \/ false] = Pr[M.f() @ &m : res].
  rewrite Pr[mu_disjoint].
    trivial.
  rewrite Pr[mu_false].
  smt.
qed.

lemma t6 &m :  Pr[M.f() @ &m : res /\ false ] <= Pr[M.f() @ &m : res ].
  rewrite Pr[mu_sub].
    trivial.
  trivial.
qed.

lemma t7 &m :  Pr[M.f() @ &m : res /\ false ] <= Pr[M.f() @ &m : res ] /\ true.
  rewrite Pr[mu_sub].
    trivial.
  trivial.
qed.

