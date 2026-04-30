require import Real Distr.

type t.

op sample: t distr.
axiom sample_ll: is_lossless sample.

op test: t -> bool.
axiom pr_ntest: 0%r < mu sample (predC test).

module Sample = {
  proc sample () : bool = {
     var r : t;
     var ret : bool;

     ret <- true;
     r <$ sample;

     while (test r) {
        r <$ sample;
     }
     return ret;
   }
    proc idle () : bool = {
      var ret : bool;

      ret <- true;

      return ret;
  }
}.

lemma Sample_lossless:
  equiv[Sample.sample ~ Sample.idle : true ==> ={res}].
proof.
proc; seq  2 1: (={ret});auto.
split.
 + by exact /sample_ll.
 by auto.
while {1} (={ret}).
 + by auto; rewrite sample_ll.
 + auto.
   seq 0 : true => //=.
   while true (if test r then 1 else 0) 1 (mu sample (predC test)) => //.
    + by move => _ r; case: (test r).
    + move => ih; seq  1: true => //.
      by auto; rewrite sample_ll.
    + by auto; rewrite sample_ll.
    rewrite pr_ntest=> /= z; conseq (: true ==> !test r).
     + by smt().
     by rnd; auto.
 by auto.
qed.

lemma Sample_lossless2:
  equiv[Sample.idle ~ Sample.sample : true ==> ={res}].
proof.
proc; seq  1 2: (={ret});auto.
split.
 + by exact /sample_ll.
 by auto.
while {2} (={ret}).
 + by auto; rewrite sample_ll.
 + auto.
   seq 0 : true => //=.
   while true (if test r then 1 else 0) 1 (mu sample (predC test)) => //.
    + by move => _ r; case: (test r).
    + move => ih; seq  1: true => //.
      by auto; rewrite sample_ll.
    + by auto; rewrite sample_ll.
    rewrite pr_ntest=> /= z; conseq (: true ==> !test r).
     + by smt().
     by rnd; auto.
 by auto.
qed.
