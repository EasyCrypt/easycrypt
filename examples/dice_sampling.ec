require import Distr.
require import Int.
require import Real.

module D4 = {
  fun sample () : int = {
    var r : int;
    r = $[1..4];
    return r;
  }
}.

module D6 = {
  fun sample () : int = {
    var r : int;
    r = 5;
    while (5 <= r) {
      r = $[1..6];
    }
    return r;
  }
}.

lemma prD4 : forall k &m, Pr[D4.sample() @ &m : res = k] = if 1 <= k && k <= 4 then 1%r/4%r else 0%r.
proof.
  intros k &m. 
  bdhoare_deno (_: true ==> k = res) => //.
  fun;rnd;skip;progress => //.
  rewrite (_:mu [1..4] (lambda (x : int), k = x) = mu_x [1..4] k).
   rewrite /mu_x;apply mu_eq => //.
  case (1 <= k && k <= 4) => Hk; [rewrite Dinter.mu_x_def_in // | rewrite Dinter.mu_x_def_notin //];
   rewrite Dinter.supp_def => //.
save.

lemma prD6 : forall k &m, (if 1 <= k && k <= 4 then 1%r/4%r else 0%r) <= Pr[D6.sample() @ &m : res = k].
proof.
  intros k &m. 
  bdhoare_deno (_: true ==> k = res) => //.
  fun; case (1 <= k && k <= 4).
    seq 1 : true 1%r (1%r/4%r) 0%r 1%r (1 <= k <= 4 /\ r = 5) => //;first 2 wp => //.
    while (1 <= k <= 4) (if r <= 4 then 0 else 1) 1 (4%r/6%r) => //.
    intros r; case (r <= 4) => /=. admit. admit. (* Bug in <= *)
    intros Hw.
      seq 1 : (r=k) (4%r/6%r) 1%r (2%r/6%r) (1%r/4%r) (1<=k <= 4) => //.
      rnd => //.
      rnd;skip;progress => //.
        admit.
      rcondf 1 => //. skip;smt.
      rnd;skip;progress.           
        admit.
     conseq Hw => //.
     smt.         
    conseq * (_: _ ==> true) => //.
    rnd;skip;progress => //;smt.
    intros z;rnd;skip;progress.
      admit.
  hoare; last smt.
   while (! (1<=k<=4) /\ 1 <= r).
     rnd;skip;progress => //; smt.
   wp;skip;progress => //;smt.
save.

equiv D4_D6 : D4.sample ~ D6.sample : true ==> ={res}.
proof.
 bypr (res{1}) (res{2}) => //.      
 intros k &m1 &m2 _.
 rewrite (_ : Pr[D4.sample() @ &m1 : k = res] = Pr[D4.sample() @ &m1 : res = k]).
   equiv_deno (_: true ==> ={res}) => //. fun;eqobs_in.
 rewrite (_ : Pr[D6.sample() @ &m2 : k = res] = Pr[D6.sample() @ &m2 : res = k]).
   equiv_deno (_: true ==> ={res}) => //. fun;eqobs_in.
 rewrite (prD4 k &m1) (* (prD6 k &m2) *).
admit.
save.
