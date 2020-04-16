(* -------------------------------------------------------------------- *)
require import AllCore List Distr.

pragma +implicits.
pragma -oldip.

(* -------------------------------------------------------------------- *)
abstract theory DMapSampling.
type t1, t2.

module S = {
  proc sample(d : t1 distr, f : t1->t2) : t2 = {
    var r;

    r <$ dmap d f;
    return r;
  }

  proc map(d: t1 distr, f: t1->t2) : t2 = {
    var r1;

    r1 <$ d;
    return f r1;
  }
}.

lemma sample_r &m d0 f0 a :
  Pr[S.sample(d0, f0) @ &m : res = a] = mu1 (dmap d0 f0) a.
proof.
byphoare (_: d = d0 /\ f = f0 ==> res = a) => //=.
by proc; rnd; auto.
qed.

equiv sample: S.sample ~ S.map : ={d, f} ==> ={res}.
proof.
bypr (res{1}) (res{2}) => // &m1 &m2 a [-> ->].
rewrite (@sample_r &m1 d{m2} f{m2} a) dmap1E eq_sym.
byphoare (_: d = d{m2} && f = f{m2} ==> res = a) => //=.
by proc; rnd; auto.
qed.
end DMapSampling.
