(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
require import AllCore List StdOrder Distr StdOrder.
(*---*) import RealOrder RealSeries StdBigop.Bigreal BRA.

pragma +implicits.
pragma -oldip.

(* -------------------------------------------------------------------- *)
(* TODO : generalize this to parametric distribution *)
abstract theory ProdSampling.
type t1, t2.

op d1 : t1 distr.
op d2 : t2 distr.

module S = {
  proc sample () : t1 * t2 = {
    var r;

    r <$ d1 `*` d2;
    return r;
  }

  proc sample2 () : t1 * t2 = {
    var r1, r2;

    r1 = $ d1;
    r2 = $ d2;
    return (r1,r2);
  }
}.

equiv sample_sample2 : S.sample ~ S.sample2 : true ==> ={res}.
proof.
bypr (res{1}) (res{2}) => // &m1 &m2 a.
have ->: Pr[S.sample() @ &m1 : res = a] = mu1 (d1 `*` d2) a.
+ by byphoare=> //=; proc; rnd; skip. 
elim: a=> a1 a2; have -> := dprod1E d1 d2 a1 a2.
byphoare=> //=.
proc; seq  1: (r1 = a1) (mu1 d1 a1) (mu1 d2 a2) _ 0%r true=> //=.
+ by rnd.  
+ by rnd.
by hoare; auto=> /> ? ->.
qed.
end ProdSampling.
