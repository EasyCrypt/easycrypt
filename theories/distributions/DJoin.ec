(* -------------------------------------------------------------------- *)
require import AllCore List Distr Ring StdBigop StdRing StdOrder.
(*---*) import IntID Bigreal Bigreal.BRM.

pragma +implicits.

(* ==================================================================== *)
abstract theory JoinSampling.
type ta.

module S = {
  proc sample(ds : ta distr list): ta list = {
    var rs;

    rs <$ djoin ds;
    return rs;
  }

  proc loop(ds : ta distr list): ta list = {
    var i, r, l;

    i <- size ds - 1;
    l <- [];
    while (0 <= i) {
      r <$ (nth witness ds i);
      l <- r :: l;
      i <- i - 1;
    }
    return l;
  }
}.

(* -------------------------------------------------------------------- *)
lemma pr_sample ds0 &m xs:
  Pr[S.sample(ds0) @ &m: res = xs] = mu (djoin ds0) (pred1 xs).
proof. by byphoare (_: ds = ds0 ==> res = xs)=> //=; proc; rnd. qed.

end JoinSampling.

(* ==================================================================== *)
abstract theory JoinMapSampling.

type ta, tb.

module S = {
  proc sample(d: ta -> tb distr, xs: ta list): tb list = {
    var r;
  
    r <$ djoinmap d xs;
    return r;
  }

  proc loop(d: ta -> tb distr, xs: ta list): tb list = {
    var i, r, l;

    i <- size xs - 1;
    l <- [];
    while (0 <= i) {
      r <$ d (nth witness xs i);
      l <- r :: l;
      i <- i - 1;
    }
    return l;
  }
}.

equiv Sample_Loop_eq: S.sample ~ S.loop: ={d, xs} ==> ={res}.
proof. admitted.

end JoinMapSampling.
