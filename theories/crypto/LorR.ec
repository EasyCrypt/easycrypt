require import AllCore Distr DBool.

module type A = {
  proc main() : bool
}.

module RandomLR(L:A) (R:A) = {
  proc main () = { 
    var b,r : bool;
    b <${0,1};
    if (b)  r <@ L.main();
    else r <@ R.main ();
    return (b = r);
  }
}.

section.

  declare module L <: A.
  declare module R <: A.

  local module Aux = {
    var b,r : bool
    proc main () = { 
      b <${0,1};
      if (b)  r <@ L.main();
      else r <@ R.main ();
      return (b = r);
    }
  }.

  lemma pr_AdvLR_AdvRndLR &m: 
     Pr[R.main() @ &m : true] = 1%r =>
     `| Pr[L.main () @ &m : res] - Pr[R.main () @ &m : res] | =
     2%r * `| Pr[RandomLR(L, R).main() @ &m : res] - 1%r/2%r |.
  proof.
    move => Hll.
    have -> : Pr[RandomLR(L, R).main() @ &m : res] = Pr[Aux.main() @ &m : res].
    + by byequiv => //; proc; sim=> /#.
    have -> : Pr[Aux.main() @ &m : res] = 
              Pr[Aux.main() @ &m : res /\ Aux.b] +  
              Pr[Aux.main() @ &m : res /\ !Aux.b].
    + by rewrite Pr [mu_split Aux.b].
    have -> : Pr[Aux.main() @ &m : res /\ Aux.b] = 1%r/2%r * Pr[L.main () @ &m : res].
    + byphoare (_: (glob L) = (glob L){m} ==> res /\ Aux.b) => //.
      proc; pose p := Pr[L.main() @ &m : res]. (* FIXME assert false without the pose *)
      seq 1 : (Aux.b = true) (1%r/2%r) p  _ 0%r (glob L = (glob L){m}); 1:by auto.
      + by rnd (pred1 true); skip => />; rewrite dbool1E.
      + if; last by (conseq (_: false ==> _); 1:by smt()); auto.
        conseq (_ : _ ==> Aux.r) => //; 1:by smt().
        call (_: glob L = (glob L){m} ==> res); last by auto.
        by bypr=> &m0 hm0; rewrite /p; byequiv=> //; proc (true).
      + by (conseq (_: _ ==> false); 1:smt()); auto.
      smt().
    have -> : Pr[Aux.main() @ &m : res /\ !Aux.b] = 1%r/2%r * Pr[R.main () @ &m : !res].
    + byphoare (_: (glob R) = (glob R){m} ==> res /\ !Aux.b) => //.
      proc; pose p := Pr[R.main() @ &m : !res]. 
      seq 1 : (Aux.b = false) (1%r/2%r) p  _ 0%r (glob R = (glob R){m}); 1:by auto.
      + by rnd (pred1 false); skip => />; rewrite dbool1E.
      + if; first by (conseq (_: false ==> _); 1:by smt()); auto.
        conseq (_ : _ ==> !Aux.r) => //; 1:by smt().
        call (_: glob R = (glob R){m} ==> !res); last by auto.
        by bypr=> &m0 hm0; rewrite /p; byequiv=> //; proc (true).
      + by (conseq (_: _ ==> false); 1:smt()); auto.
      smt().
    rewrite Pr [mu_not] Hll /#.
  qed.

end section.

