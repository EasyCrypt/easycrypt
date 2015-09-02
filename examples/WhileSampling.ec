require import Real Distr.

type t.
op sample : t distr.
axiom lossless : weight sample = 1%r.
op test : t -> bool.

module Sample = { 
  proc sample () : t = { 
    var r : t;
    r = $sample;
    while (test r) {
      r = $sample;
    }
    return r;
  }
}.

axiom pr_ntest : 0%r < (mu sample (predC test)).

lemma Sample_lossless : islossless Sample.sample.
proof.
 proc.
 seq 1 : true => //.
  rnd;skip;smt.
 while true (if test r then 1 else 0) 1 (mu sample (predC test)) => //;first smt.
  intros Hrec.
  seq 1 : true => //.
  by rnd;skip;smt.
  by rnd;skip;smt. 
  split;[apply pr_ntest |  intros z].
  conseq (_ : true ==> (predC test) r);first smt.
 rnd;skip;progress;apply mu_sub => x //.
qed.
