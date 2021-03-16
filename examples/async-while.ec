require import AllCore IntDiv Ring StdRing StdOrder.
(*---*) import IntID IntOrder RealOrder.

type value.

op n : { int | 0 <= n} as ge0_n.
op k : { int | 0 <  k} as gt0_k.

lemma ge0_k : 0 <= k.
proof. by rewrite ltrW ?gt0_k. qed.

module type I = {
  proc step(i : int, x : value) : value
}.

module M(A : I) = {
  proc f(x : value) = {
    var i <- 0;

    while (i < n * k) {
      x <@ A.step(i, x);
      i <- i + 1;
    }

    return x;
  }

  proc g(x : value) = {
    var i <- 0;
    var j;

    while (i < n) {
      j <- 0;
      while (j < k) {
        x <@ A.step(k * i + j, x);
        j <- j + 1;
      }
      i <- i + 1;
    }

    return x;
  }
}.

lemma M_equiv (A <: I) : islossless A.step =>
  equiv[M(A).f ~ M(A).g : ={glob A, x} ==> ={res}].
proof. move=> llA; proc.
seq 1 1 : (i{1} = 0 /\ ={glob A, x, i}) => //.
+ by auto => &1 &2 />.
async while
  [ (fun r => i%r < k%r * r), (i{2} + 1)%r ]
  [ (fun r => i%r < r), (i{2} + 1)%r ]
    (i{1} < n * k /\ i{2} < n) (!(i{2} < n))
  :
    (={glob A, x} /\ i{1} = k * i{2} /\ (0 <= i{1})) => //=.
+ by move=> &1 &2 />; smt(gt0_k).
+ by move=> &1 &2 />; smt(gt0_k).
+ by move=> &2; exfalso=> &1; smt(gt0_k).
+ by move=> &2; exfalso=> &1; smt(gt0_k).
+ move=> v1 v2.
  rcondt {2} 1; 1: by auto => /> /#.
  rcondf{2} 4; 1: by auto; conseq (_: true);auto.
  wp;while (   ={glob A, x} 
         /\ i{1} = k * i{2} + j{2}
         /\ v1 = (i{2} + 1)%r
         /\ 0 <= i{2} <  n
         /\ 0 <= j{2} <= k) => /=; last by auto; smt(gt0_k ge0_n).
  wp; call (_ : true); skip => &1 &2 /= />.
  rewrite -fromintM !lt_fromint => *. 
  by have := StdOrder.IntOrder.ler_wpmul2l k{2} _ i{2} (n - 1); smt().
+ by while true (n * k - i) => //; auto;1: call llA; auto => /#.
+ while true (n - i);2: by auto=>/#.
  move=> z;wp; while (true) (k - j);auto;1:call llA;auto => /#.
qed.

