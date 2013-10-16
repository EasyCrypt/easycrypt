require import Distr.
require import Real.
type t.
op sample : t distr.
axiom lossless : weight sample = 1%r.
op test : t -> bool.

module Sample = { 
  fun sample () : t = { 
    var r : t;
    r = $sample;
    while (test r) {
      r = $sample;
    }
    return r;
  }
}.

axiom pr_ntest : 0%r < (mu sample (cpNot test)).

lemma Sample_lossless : islossless Sample.sample.
proof.
 fun.
 seq 1 : true => //.
  rnd;skip;smt.
 while true (if test r then 1 else 0) 1 (mu sample (cpNot test)) => //;first smt.
  intros Hrec.
  seq 1 : true => //.
  by rnd;skip;smt.
  by rnd;skip;smt. 
  split;[apply pr_ntest |  intros z].
  conseq * (_ : true ==> (cpNot test) r);first smt.
 rnd;skip;progress;apply mu_sub => x //.
save.
