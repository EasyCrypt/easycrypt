require import Real.

module M = { 
  fun f () : bool = { return true;}
}.

lemma t1 &m : Pr[M.f() @ &m : !res] = Pr[M.f() @ &m : true] - Pr[M.f() @ &m : res].
proof.
 rewrite Pr mu_not.
 trivial.
save.

lemma t2 &m : Pr[M.f() @ &m : res \/ false] = Pr[M.f() @ &m : res].
  smt.
save.

lemma t3 &m : Pr[M.f() @ &m : res \/ false] = Pr[M.f() @ &m : res].
  rewrite Pr mu_eq.
    trivial.
  trivial.
save.

lemma t4 &m : Pr[M.f() @ &m : res \/ false] = Pr[M.f() @ &m : res].
  rewrite Pr mu_or.
  rewrite (_ : Pr[M.f() @ &m : res /\ false] = Pr[M.f() @ &m : false]).
    rewrite Pr mu_eq.
      trivial.
    trivial.
  rewrite Pr mu_false.
  smt.
save.

lemma t5 &m : Pr[M.f() @ &m : res \/ false] = Pr[M.f() @ &m : res].
  rewrite Pr mu_disjoint.
    trivial.
  rewrite Pr mu_false.
  smt.
save.

lemma t6 &m :  Pr[M.f() @ &m : res /\ false ] <= Pr[M.f() @ &m : res ].
  rewrite Pr mu_sub.
    trivial.
  trivial.
save.

lemma t7 &m :  Pr[M.f() @ &m : res /\ false ] <= Pr[M.f() @ &m : res ] /\ true.
  rewrite Pr mu_sub.
    trivial.
  trivial.
save.

