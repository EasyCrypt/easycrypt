require import AllCore StdOrder IntDiv.

abbrev [-printing] floor (n k:int) = (n %/ k) * k.

lemma lt_floorE (k i n:int) : 0 < k =>  k %| i => i < floor n k <=> i + k <= floor n k.
proof.
  move => hk /dvdzP [q] ->.
  by rewrite (IntOrder.ltr_pmul2r k hk) ltzE -(IntOrder.ler_pmul2r k hk) /#. 
qed.

lemma floor_le n k : 0 < k => floor n k <= n.
proof. rewrite {2}(divz_eq n k) /#. qed.

lemma le_floor (k i n:int) : 0 < k => k %| i => i <= n => i <= floor n k.
proof.
  rewrite {1}(divz_eq n k)=> hk /dvdzP [q] ->.
  case (q * k <= floor n k) => // /ltzNge; rewrite IntOrder.ltr_pmul2r // => /ltzE.
  rewrite -(IntOrder.ler_pmul2r k hk) /#.
qed.

lemma le_floorE (k i n:int) : 0 < k => k %| i => i <= n <=> i <= floor n k.
proof. move => hk kd; smt (divz_eq le_floor). qed.

abstract theory ExactIter.
type t.

op c : int.
axiom c_gt0 : 0 < c.
op step : int.
axiom step_gt0 : 0 < step. 

module type AdvLoop = {
  proc body(t:t, i:int) : t
}.

module Loop(B:AdvLoop) = {
  proc loop1 (t:t, n:int) = {
    var i;
    i <- 0;
    while (i < n) {
      t <@ B.body(t,i);
      i <- i + 1;
    }
    return t;
  }

  proc loopk (t:t, n:int, k:int) = {
    var i, j;
    i <- 0;
    while (i < n) {
      j <- 0;
      while (j < k) {
        t <@ B.body(t, k * i + j);
        j <- j + 1;
      }
      i <- i + 1;
    }
    return t;
  }

  proc loopc (t:t, n:int) = {
    var i, j;
    i <- 0;
    while (i < n) {
      j <- 0;
      while (j < c) {
        t <@ B.body(t, c * i + j);
        j <- j + 1;
      }
      i <- i + 1;
    }
    return t;
  }
  
}.

module ILoop(B:AdvLoop) = {
  proc loop1 (t:t, n:int) = {
    var i;
    i <- 0;
    while (i < n) {
      t <@ B.body(t,i);
      i <- i + step;
    }
    return t;
  }

  proc loopk (t:t, n:int, k:int) = {
    var i, j;
    i <- 0;
    while (i + step * k <= n) {
      j <- 0;
      while (j < k) {
        t <@ B.body(t, i);
        i <- i + step;
        j <- j + 1;
      }
    }
    while (i < n) {
      t <@ B.body(t,i);
      i <- i + step;
    }
    return t;
  }

  proc loopc (t:t, n:int) = {
    var i, j;
    i <- 0;
    while (i + step * c <= n) {
      j <- 0;
      while (j < c) {
        t <@ B.body(t, i);
        i <- i + step;
        j <- j + 1;
      }
    }
    while (i < n) {
      t <@ B.body(t,i);
      i <- i + step;
    }
    return t;
  }
  
}.

section.

declare module B <:AdvLoop.

equiv loop1_loopk : Loop(B).loop1 ~ Loop(B).loopk : 
  ={t, glob B} /\ n{1} = (k * n){2} /\ 0 < k{2} ==> ={res, glob B}.
proof.
  proc.
  async while [ (fun r => i%r < r), (i{1}+k{2})%r ] 
              [ (fun r => i%r < r), (i{2} + 1)%r ]
              ( (i < n){1}) 
              (true) : 
              (={t, glob B} /\ (0 <= i <= n){2} /\ 0 < k{2} /\ n{1} = (k * n){2} /\ i{1} = k{2} * i{2}).
  + smt(). + smt (). + done. 
  + move=> &m2; exfalso; smt().
  + move=> &m1; exfalso; smt().
  + move=> v1 v2.
    rcondt{2} 1; 1: by auto => /> /#.
    rcondf{2} 4; 1: by auto; conseq (_: true);auto.
    exlim i{2} => i2.
    wp;while (={t,glob B} /\ i{1} = k{2}*i{2} + j{2} /\ 0 <= i{2} < n{2} /\ 
              0 <= j{2} <= k{2} /\ v1 = (k{2} * i2 + k{2})%r /\ i{2} = i2 /\ n{1} = (k * n){2}).
    + wp;call (_: true);skip => /> &2 h0i hin h0j hjk.
      rewrite !lt_fromint => h1 h2 h3.
      have := IntOrder.ler_wpmul2l k{2} _ i{2} (n{2} - 1); smt().
    by wp;skip => /> /#.
  + rcondf 1; skip => /#. 
  + rcondf 1; skip => /#. 
  by auto.
qed.

equiv loopk_loopc : Loop(B).loopk ~ Loop(B).loopc : ={n,t, glob B} /\ k{1} = c ==> ={res, glob B}.
proof.
  proc => /=.
  while (={glob B, i, t, n} /\ k{1} = c);2: by auto.
  wp;while (={glob B, i, j, t, n} /\ k{1} = c);2: by auto.
  by wp;call (_:true);skip.
qed.

equiv loop1_loopc : 
  Loop(B).loop1 ~ Loop(B).loopc : 
    ={t, glob B} /\ n{1} = (c * n){2} ==> ={res, glob B}.
proof.
  transitivity Loop(B).loopk
    (={t, glob B} /\ n{1} = c * n{2} /\ k{2} = c ==> ={res, glob B})
    (={n,t, glob B} /\ k{1} = c ==> ={res, glob B}).
  + by move=> &1 &2 /> 2!->; exists (glob B){2} (t{2}, n{2}, c).
  + done.
  + conseq loop1_loopk; smt (c_gt0).
  apply loopk_loopc.
qed.

equiv Iloop1_loopk : ILoop(B).loop1 ~ ILoop(B).loopk : ={t, glob B, n} /\ 0 < k{2}==> ={res, glob B}.
proof.
  proc => /=; exlim k{2} => k0.
  case: (n{2} < 0).
  + rcondf{2} 2; 1: by move=> &m1; wp; skip => &m2 />; smt (step_gt0).
    by sim; wp; skip.
  splitwhile{1} 2 : (i < floor n (step * k0)). 
  seq 2 2: (={glob B, t, n, i}); last by sim;wp;skip.
  async while [ (fun r => i%r < r), (i{1} + step * k{2})%r ] 
              [ (fun r => i%r < r), (i{2} + step * k{2})%r ]
              ( (i < floor n (step * k0)){1}) 
              (true) : 
              (={t, glob B, i, n} /\ k{2} = k0 /\ 0 < k{2} /\ (step * k0) %| i{1}).
  + move=> />;smt (lt_floorE floor_le step_gt0). 
  + move=> /> &2 h1 h2 [[]// | h3].
    have h4 := le_floorE (step * k0) (i{2} + step * k0) n{2} _ _.
    + smt (step_gt0). + by apply dvdzD => //; apply dvdzz.
    smt (step_gt0).
  + done.
  + by move=> &m2; exfalso => /#.
  + by move=> &m1; exfalso => /#.
  + move=> v1 v2.
    rcondt{2} 1. 
    + move=> &1;skip => /> *; smt (step_gt0 lt_floorE floor_le).
    rcondf{2} 3. 
    + move=> &1. 
      while (j <= k /\ i = i{1} + step * j).
      + by wp; call (_:true); skip => /#.
      by wp; skip => />; smt (step_gt0).
    exlim i{1} => i0. 
    while (={t, i, glob B, n} /\ i{1} = i0 + step * j{2} /\ v1 = (i0 + step * k{2})%r /\
            k{2} = k0 /\ (step * k0) %| i0 /\ 0 < k{2} /\ 0 <= j{2} <= k{2} /\ 
            v1 <= (floor n{1} (step * k{2}))%r).
    + wp; call (_: true); skip => &1 &2 [#] 7!->> h2 h3 h4 h1.
      rewrite le_fromint /= !lt_fromint=> h5 h6 h7 h8 h9 ???? [#] 2!->> /=.
      split. smt(). 
      have <- := IntOrder.ltr_pmul2l step step_gt0 (j{2} + 1) k0.
      smt (floor_le step_gt0).
    wp; skip => &1 &2 [#] 6!->> h1 h2 h3 h4 2!->> /=.
    rewrite le_fromint lt_fromint h2 h1 -lt_floorE /= 2://; 1:smt (step_gt0).
    split; 1: smt(step_gt0).
    by move=> /> j_R *; rewrite dvdzD 1:/# (_ : j_R = k0) 1:/# dvdzz.
  + rcondf 1; skip => /#.
  + rcondf 1; skip => /#.
  by auto.
qed.  

equiv Iloopk_loopc : ILoop(B).loopk ~ ILoop(B).loopc : ={n,t, glob B} /\ k{1} = c ==> ={res, glob B}.
proof.
  proc => /=; sim.
  while (={glob B, i, t, n} /\ k{1} = c);2: by auto.
  wp;while (={glob B, i, j, t, n} /\ k{1} = c);2: by auto.
  by wp;call (_:true);skip.
qed.

equiv Iloop1_loopc : 
  ILoop(B).loop1 ~ ILoop(B).loopc : 
    ={t, glob B, n} ==> ={res, glob B}.
proof.
  transitivity ILoop(B).loopk
    (={t, glob B} /\ n{1} = n{2} /\ k{2} = c ==> ={res, glob B})
    (={n,t, glob B} /\ k{1} = c ==> ={res, glob B}).
  + by move=> &1 &2 /> 2!->; exists (glob B){2} (t{2}, n{2}, c).
  + done.
  + conseq Iloop1_loopk; smt (c_gt0).
  apply Iloopk_loopc.
qed.

end section.

end ExactIter.
