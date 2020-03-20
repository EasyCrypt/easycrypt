require import Real Distr.

type t.

op sample: t distr.
axiom sample_ll: is_lossless sample.

op test: t -> bool.
axiom pr_ntest: 0%r < mu sample (predC test).

module Sample = {
  proc sample () : t = {
    var r : t;

    r <$ sample;
    while (test r) {
      r <$ sample;
    }
    return r;
  }
}.

lemma Sample_lossless: islossless Sample.sample.
proof.
proc; seq  1: true=> //.
+ by auto=> />; exact/sample_ll.
while true (if test r then 1 else 0) 1 (mu sample (predC test))=> //.
+ by move=> _ r; case: (test r).
+ move=> ih; seq  1: true=> //.
  by auto; rewrite sample_ll.
+ by auto; rewrite sample_ll.
rewrite pr_ntest=> /= z; conseq (: true ==> !test r).
+ smt().
by rnd; auto=> />.
qed.
