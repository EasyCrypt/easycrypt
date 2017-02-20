(* -------------------------------------------------------------------- *)
require import Option Int IntExtra Real RealExtra RealExp Ring.
require import Distr List Aprhl StdRing StdOrder StdBigop RealFun.
(*---*) import IntID IntOrder RField RealOrder.

pragma -oldip.
lemma bound_e : 271%r/100%r < e < 272%r/100%r.
proof.
  admit.
qed.

(* -------------------------------------------------------------------- *)
lemma ge_ln2 : inv 2%r <= ln 2%r.
proof. by rewrite -(mul1r (inv _)) ltrW (le_ln_dw 2%r). qed.

lemma footnote5 lam sigma:
   0%r < lam < 1%r/2%r =>
   (6%r/lam) * ln(4%r/lam) <= sigma =>
   RealExp.exp(2%r * lam / 3%r) / (1%r - RealExp.exp (-sigma * lam / 6%r))
     <= RealExp.exp lam.
proof.
  move=> Hlam Hsigma.
  have ln_lam: 0%r < ln(4%r/lam).
  + by rewrite ln_gt0 /#.
  have Hgt0: 0%r < 1%r - RealExp.exp (- sigma * lam / 6%r).
  + rewrite subr_gt0 -exp0 exp_mono_ltr. 
    (have : 0%r < sigma)=>/#.
  apply (ler_trans (RealExp.exp(2%r * lam / 3%r) / (1%r - lam /4%r))).
  + apply ler_pmul=> //;1,2:smt(exp_gt0).
    apply lef_pinv=> // [/# | ].
    apply ler_sub => //.
    rewrite -(expK (lam/4%r)) 1:/#; apply exp_mono. 
    apply (ler_trans (- (6%r / lam * ln (4%r / lam)) * lam / 6%r)).
    + rewrite ler_opp2 ler_pmul // 1,2:/# ler_pmul // 1,2:/#.
    apply lerr_eq;fieldeq=> //. smt().
    rewrite !lnM // 1,2,3:/# !lnV // 1:/#;ringeq.
  rewrite ler_pdivr_mulr 1:/# (mulrC (RealExp.exp lam)) -ler_pdivr_mulr ?exp_gt0.
  rewrite -expN -expD -subr_le0.
  have ->: (2%r * lam / 3%r - lam) = -lam/3%r by fieldeq.
  rewrite opprB (mulrC _ (inv 4%r)).
  pose f := fun lam => RealExp.exp(- lam / 3%r) + (inv 4%r * lam - 1%r).
  have := convexe_le f 0%r (1%r/2%r) lam _ _.
  + apply convexeD. 
    + by move=> d Hd;have /# := convexe_exp (- 0%r / 3%r) (- (1%r/2%r) / 3%r) d Hd.
    apply convexeD => /=.
    + apply (convexeZ (inv 4%r) (fun x => x));1:smt().
      by apply convexe_id.
    by apply convexeC.
  + smt().
  move=> H;apply (ler_trans _ _ _ H)=> {H}.
  rewrite /f exp0 /=.
  rewrite /maxr (_: (exp (- inv 6%r))%RealExp + (-7)%r / 8%r <= 0%r) //.
  rewrite -ler_subr_addr /= -(rpow_mono _ _ 6%r) // ?exp_gt0 1:/#.
  rewrite rpowE ?exp_gt0 lnK /= (_: 6%r * - inv 6%r = -1%r). by fieldeq.
  rewrite expN -/e (_:6%r = 1%r + 1%r + 1%r + 1%r + 1%r + 1%r) //.
  have H78: 0%r < 7%r / 8%r by smt().
  rewrite !rpowD // !rpow1 //; smt (bound_e). 
qed.

lemma ln_invw w:  0%r < w < 1%r/2%r => 1%r/ 2%r < ln (inv w).
proof.
  move=> Hw;apply (ler_lt_trans _ _ _ ge_ln2).
  apply ln_mono_ltr => //;2:smt(); by apply invr_gt0;elim Hw. 
qed.

lemma gt1_2Mln M w : 0%r < w < 1%r/2%r => 0 < M => 1%r < 2%r * M%r * ln (inv w).
proof. smt (ln_invw le_fromint). qed.

lemma gt1_sqrt M w : 0%r < w < 1%r/2%r => 0 < M => 1%r < sqrt (2%r * M%r * ln (inv w)).
proof.
  move=> Hw HM.
  rewrite -(rpow1r (inv 2%r)) /(^) /=.
  have Hgt:= gt1_2Mln M w Hw HM.
  rewrite lerNgt; have H : (0%r <2%r * M%r * ln (inv w)) by smt().
  rewrite H /=exp_mono_ltr ltr_pmul2r 1:/# ln_mono_ltr //.
qed.

lemma footnote2 M eps w: 
  0%r < w < 1%r/2%r =>
  0%r <= eps <= 1%r => 
  0 < M => 
  let eps' = eps / (2%r * sqrt(2%r * M%r * ln(inv w))) in 
  eps' * sqrt(2%r * M%r * ln(inv w)) + M%r * eps' * ((RealExp.exp (eps'/2%r)) - 1%r) <= eps.
proof.
  move=> Hw Heps HM eps'.
  rewrite {1 2}/eps';pose sq:= sqrt (2%r * M%r * ln (inv w)). 
  have Hsq := gt1_sqrt M w Hw HM.
  have -> : eps / (2%r * sq) * sq = eps/2%r by fieldeq; smt().
  have Heps': RealExp.exp (eps'/2%r) - 1%r <= 2%r * eps'.
  + pose f := fun eps' => RealExp.exp (eps'/2%r) - 1%r - 2%r * eps'.
    have := convexe_le f 0%r 1%r eps' _ _;2:smt().
    + rewrite !convexeD ?convexeC 2:/#.
      apply (convexe_exp (0%r/2%r) (1%r/2%r)).
    have : RealExp.exp (inv 2%r) <= e by apply exp_mono=> /#.
    rewrite /f /= exp0 /=;smt(bound_e).
  apply (ler_trans (eps / 2%r + M%r * (eps / (2%r * sq)) * (2%r * eps'))).
  rewrite ler_add2l; apply ler_wpmul2l=>//;smt (le_fromint).
  rewrite /eps'.
  have -> : M%r * (eps / (2%r * sq)) * (2%r * (eps / (2%r * sqrt (2%r * M%r * ln (inv w))))) = 
           (eps/2%r) * ((M%r/sq^2%r) * eps).
  + rewrite -/sq rpow_int 1:/#;fieldeq=> //;1:smt(). 
    rewrite -rpow_int 1:/# (_:2%r = 1%r + 1%r) // rpowD 1:/# rpow1 /#.
  apply (ler_trans (eps / 2%r + eps / 2%r));2:smt().
  apply ler_add => //;apply ler_pimulr;1:smt().
  have -> : M%r / sq ^ 2%r = 1%r / (2%r * ln (inv w)).
  + rewrite /sq -rpowM 1:[smt (gt1_2Mln)] /= rpow1;1:smt(gt1_2Mln).
    fieldeq => /=; smt (ln_invw).
  smt (ln_invw).
qed.

(* -------------------------------------------------------------------- *)
op N : { int | 0 <= N } as ge0_N.
op M : { int | 0 < M } as gt0_M.

lemma ge0_M : 0 <= M.
proof. smt (gt0_M). qed.

(* -------------------------------------------------------------------- *)
type query, db.

op evalQ: query -> db -> int.
op nullQ: query.

(* -------------------------------------------------------------------- *)
pred adj: db & db.

axiom one_sens d1 d2 q: adj d1 d2 => `|evalQ  q d1 - evalQ q d2| <= 1.

(* -------------------------------------------------------------------- *)
module type Adv = {
  proc adv  (log : int list) : query
}.

hint exact : ge0_N ge0_M.

(* -------------------------------------------------------------------- *)

theory AbstractBetween.

op eps       : { real | 0%r <  eps } as gt0_eps.
op eps'      : { real | 0%r < eps' } as gt0_eps'.
op delt      : { real | 0%r <  delt < 1%r} as bound_delt.
op w         : { real | 0%r < w <= 1%r }  as bound_w.

lemma gt0_delt : 0%r < delt.
proof. smt (bound_delt). qed.

lemma ge0_eps : 0%r <= eps.
proof. smt (gt0_eps). qed.

lemma ge0_eps' : 0%r <= eps'.
proof. smt (gt0_eps'). qed.

lemma ge0_delt : 0%r <= delt.
proof. smt (gt0_delt). qed.

lemma gt0_w : 0%r < w.
proof. smt (bound_w). qed.

lemma ge0_w : 0%r <= w.
proof. smt (gt0_w). qed.

hint exact : gt0_eps ge0_eps gt0_eps' ge0_eps' gt0_delt ge0_delt gt0_w gt0_w ge0_w.

(* -------------------------------------------------------------------- *)
op t : int.
op u : int.
axiom tu : 2%r * ln (1%r / delt) / eps + 2%r < (t - u)%r.

(* -------------------------------------------------------------------- *)
op bound_t0u0 = (t - u)%r - 2%r * ln (1%r/delt) / eps.

op eps_i =
 ln (RealExp.exp (2%r * eps') /
      (1%r - RealExp.exp ((- bound_t0u0 * eps') / 2%r))).
    
lemma gt0_eps_i_aux: 
  1%r < (exp (2%r * eps'))%RealExp / (1%r - (exp ((- bound_t0u0 * eps') / 2%r))%RealExp).
proof.
  have Ht0u0 : bound_t0u0 * eps'> 0%r.
  + rewrite pmulr_lgt0.
    + by apply gt0_eps'.
    rewrite /bound_t0u0 ltr_subr_addr add0r;smt (tu). 
  apply ltr_pdivl_mulr=> /=.
  + rewrite ltr_subr_addr add0r -exp0 exp_mono_ltr /#.
  apply (ltr_trans 1%r _ _)=> />.
  + rewrite ltr_subl_addr -ltr_subl_addl;smt (exp_gt0).
  rewrite -exp0 exp_mono_ltr;smt (gt0_eps').
qed.

lemma gt0_eps_i : 0%r < eps_i.
proof. rewrite /eps_i ln_gt0 gt0_eps_i_aux. qed.

lemma ge0_eps_i : 0%r <= eps_i.
proof. smt(gt0_eps_i). qed.

hint exact : ge0_eps_i.

module BT(A : Adv) = {
  proc main(d : db) : int list = {
    var l  : int list;
    var i  : int;
    var q  : query;
    var x  : int;
    var t0 : int;
    var u0 : int;
    var n  : int;

    n  <$ lap eps 0;
    i  <- 0;
    l  <- [];
    t0 <- t - n;
    u0 <- u + n;   
    while (i < N /\ size l < M) {
      q <@ A.adv(l);
      x <$ lap eps' (evalQ q d);
      if (u0 <= x <= t0) l <- i :: l;
      i <- i + 1;
    }

    return l;
  }
}.

module BT_aux(A : Adv) = {
  proc main(d : db) : int list = {
    var l  : int list;
    var i, i', hd: int;
    var count : int;
    var q  : query;
    var x  : int;
    var t0 : int;
    var u0 : int;
    var n  : int;

    n  <$ lap eps 0;
    i  <- 0;
    l  <- [];
    t0 <- t - n;
    u0 <- u + n;   
    while (i < N /\ size l < M) {
      i' = i;
      hd  = -1; 
      while (i' < N) {
        if (hd = -1) { 
          q <@ A.adv(l);
          x <$ lap eps' (evalQ q d);
          if (u0 <= x <= t0) {hd = i;} 
          i <- i + 1;
        } 
        i' <- i' + 1;   
      }
      if (hd <> -1) l <- hd::l;
    }

    return l;
  }
}.

lemma equiv_BT_BT_aux (A<:Adv) : 
  islossless A.adv => 
  equiv [BT(A).main ~ BT_aux(A).main : ={glob A, d} ==> ={glob A, res}].
proof.
  move=> A_ll; proc.
  seq 5 5 : (={glob A, d, i, l, t0, u0} /\ 0 <= i{1});1:auto.
  async while [fun s0 => size l = s0, size l{1}]
              [fun s0 => size l = s0, size l{2}]
              true false : (={glob A, i, l, d, t0, u0} /\ 0 <= i{1})=> //=;1: smt ().
  + move=> s1 s2. unroll{2} 1. rcondt{2} 1;1:by auto=>/#.
    rcondf{2} 5.
    + move=> &m;wp.
      while (i' <= N /\ (hd = -1 => i = i'));2: auto=> /#.
      if;auto;2:smt ().
      call (_:true);auto=> /#.
    wp. 
    splitwhile{2} 3 : (hd = -1).
    while{2} (={glob A, i} /\ 
              l{1} = (if hd{2} <> -1 then hd{2}::l{2} else l{2}) /\
              !(i'{2} < N /\ hd{2} = -1)) (N-i'{2}).
    + by move=> &m z;rcondf 1; auto=> /#.
    while ( ={glob A, d, i, t0, u0} /\ 0 <= i{2} /\
            (hd{2} = -1 => (i=i'){2} /\ ={l}) /\
            (hd{2} <> -1 => l{1} = hd{2}::l{2} )).
    + rcondt{2} 1;auto;call (_:true);auto=> /#.
    auto=> /#.
  + by rcondf 1;auto.
  by rcondf 1;auto.
qed.

(* -------------------------------------------------------------------- *)
section Ex.

declare module A : Adv.

axiom adv_ll : islossless A.adv.

lemma L : aequiv [ [ (sqrt (2%r * M%r * ln (inv w)) * eps_i +
                              M%r * eps_i * ((exp eps_i)%RealExp - 1%r) + eps)
                            & (delt + w) ]
  BT_aux(A).main ~ BT_aux(A).main : adj d{1} d{2} /\ ={glob A} ==> ={res, glob A}
].
proof.
  proc=> /=.
  utb ((l, glob A), (l, glob A)) : [ (`|n%r| > ln(1%r/delt)/eps), delt]=> //.
  + while true (N - i).
    + move=> z1;unroll 3;wp.
      while (N - i < z1) (N-i').
      + move=> z2;auto;if;auto;2:smt().
        by call adv_ll;skip=> /> &1 ???;rewrite lap_ll /= /#.
      rcondt 3;1:by auto.
      rcondt 3;auto;call adv_ll;auto=>/> &1 ???;rewrite lap_ll /= /#.
    by auto=> />;rewrite lap_ll /#.
  + while true (N - i).
    + move=> z1;unroll 3;wp.
      while (N - i < z1) (N-i').
      + move=> z2;auto;if;auto;2:smt().
        by call adv_ll;skip=> /> &1 ???;rewrite lap_ll /= /#.
      rcondt 3;1:by auto.
      rcondt 3;auto;call adv_ll;auto=>/> &1 ???;rewrite lap_ll /= /#.
    by auto=> />;rewrite lap_ll /#.
  + move=> &2.  
    seq 1 : ( ln (1%r / delt) / eps < `|n%r|) delt 1%r _ 0%r true  => //.
    + rnd;auto;progress.  
      apply (lap_bound_lt eps delt gt0_eps gt0_delt).
    by conseq (_ : _ ==> false).
  
  seq 1 1 : (adj d{1} d{2} /\ ={glob A} /\ n{1} = n{2} - 1) <[ eps & 0%r ]>.
  + by lap (1) 1=> /#.
  conseq <[((2%r * M%r * ln (inv w)) ^ inv 2%r * eps_i +
             M%r * eps_i * ((exp eps_i)%RealExp - 1%r)) & w]>;1:smt().

  case (! ln (1%r / delt)/eps < `|n{1}%r|);first last.
  + toequiv=>//.
    + have hM: 0%r <= M%r by rewrite le_fromint.
      apply addr_ge0.
      + by apply mulr_ge0=> //;apply ge0_sqrt.
      rewrite !mulr_ge0 // subr_ge0.
      have := le1Dx_exp eps_i ge0_eps_i; smt (ge0_eps_i).
    conseq (_: _ ==> true);1: smt().
    while{1} true (N - i{1}).
    + move=> _ z1;unroll 3;wp.
      while (N - i < z1) (N-i').
      + move=> z2;auto;if;auto;2:smt().
        by call adv_ll;skip=> /> &1 ???;rewrite lap_ll /= /#.
      rcondt 3;1:by auto.
      rcondt 3;auto;call adv_ll;auto=>/> &1 ???;rewrite lap_ll /= /#.
    while{2} true (N - i{2});2: by auto=> /#.
    move=> _ z1;unroll 3;wp.
    while (N - i < z1) (N-i').
    + move=> z2;auto;if;auto;2:smt().
      by call adv_ll;skip=> /> &1 ???;rewrite lap_ll /= /#.
    rcondt 3;1:by auto.
    rcondt 3;auto;call adv_ll;auto=>/> &1 ???;rewrite lap_ll /= /#.

  seq << 4 4 : (adj d{1} d{2} /\ ={i,l,glob A} 
                /\ i{1} = 0 /\ l{1} = []
                /\ t0{1} = t0{2} + 1
                /\ u0{1} = u0{2} - 1 
                /\ bound_t0u0 <= (t0{1} - u0{1})%r).
  + toequiv;auto=> /#.

  awhile ac  w [eps_i & (0%r)]
              [(if i = N then 0 else M - size l) & M]
              (adj d{1} d{2} /\ ={i,l,glob A} /\ 0 <= i{1} /\
              t0{1} = t0{2} + 1 /\ u0{1} = u0{2} - 1 /\ bound_t0u0 <= (t0{1} - u0{1})%r)=> />.
  + smt (ge0_M).
  + smt ().
  + smt (ge0_eps_i gt0_w ge0_M).
  move=> k.
  conseq (_: _ ==> ={i, l, glob A}) 
         (_ : (if i = N then 0 else Top.M - size l) = k /\
              0 <= i < N /\ size l < M ==>
              (if i = N then 0 else Top.M - size l) < k /\ 0 <= i)=> //.
  + wp;while (0 <= i <= N /\ (hd = -1 => i' = i));auto;2:smt ().
    wp;if;auto;2:smt (); by call (_:true);skip=> /#.

  seq 2 2 : (adj d{1} d{2} /\
             ={i, l, glob A, i', hd} /\ 0 <= i{1} /\
             t0{1} = t0{2} + 1 /\ u0{1} = u0{2} - 1 /\ bound_t0u0 <= (t0{1} - u0{1})%r /\
             (i{1} < N /\ size l{1} < Top.M) /\ 
             hd{1} = -1 /\ i'{1} = i{1});1:by toequiv;auto.
  wp;conseq (_: _ ==> ={i,hd,glob A})=> //.
  pweq ((i, hd, glob A), (i, hd, glob A)).
  + while true (N - i');auto;2:smt ().
    if;auto;2:smt().
    by call adv_ll;skip=> /> &1 ??;rewrite lap_ll /= /#.
  + while true (N - i');auto;2:smt ().
    if;auto;2:smt().
    by call adv_ll;skip=> /> &1 ??;rewrite lap_ll /= /#.
  + by move=> &1 &2 /(_ (i,hd,glob A){1}).
  move=> [i1 HD globA]. 
  conseq <[ (bigi predT (fun (k0 : int) => if k0 = N - HD then eps_i else 0%r) 0 (N + 1)) & 0%r ]>.
  + progress.
    rewrite (bigD1_cond_if _ _ _ (N - HD)) ?range_uniq big1 /=;1:by move=> i [] _ ->.
    smt (ge0_eps_i).
  awhile [(fun k => if k = N - HD then eps_i else 0%r) & (fun _ => 0%r)] (N+1) [N-i'] 
         ( adj d{1} d{2} /\ ={l, i'} /\ 0 <= i{1} /\
           t0{1} = t0{2} + 1 /\
           u0{1} = u0{2} - 1 /\
           (hd = -1 => i = i'){1} /\ 
           (hd <> -1 => i = hd+1){1} /\
           (hd = -1 => i = i'){2} /\ 
           (hd <> -1 => i = hd+1){2} /\ bound_t0u0 <= (t0{1} - u0{1})%r /\
           ((hd{1} = -1 \/ hd{1} = HD) => ={i, hd, glob A}))=> //;1..5:smt (ge0_N ge0_eps_i).
  + by rewrite big1_eq.

  move=> k0;wp.
  if{1}.
  + rcondt{2} 1;1:by auto=> /#.
    seq 1 1:
      (adj d{1} d{2} /\ ={q,l, i',i, hd, glob A} /\
       0 <= i{1} /\ t0{1} = t0{2} + 1 /\ u0{1} = u0{2} - 1 /\
       i{1} = i'{1} /\ bound_t0u0 <= (t0{1} - u0{1})%r /\
       i'{1} < N /\ k0 = N - i'{1} /\ N - i'{1} <= N + 1 /\ hd{1} = -1).
    + by toequiv;call (_:true);auto=> /#.
    case @[ambient] (k0 = N - HD)=> Hk0;wp.
    + exists * u0{1}, t0{1}, u0{2}, t0{2}  ;elim * => p q r s.
      conseq (_ : _ ==> (p <= x <= q){1} = (r <= x <= s){2});1: smt ().
      int lap [p, q] [r,s] 2 & bound_t0u0 & 1 => //; smt (one_sens tu).
    exists* (evalQ q d){1}, (evalQ q d){2}; elim* => e1 e2.
    lap  (e2 - e1) 0;smt (one_sens).
  toequiv.
  + smt (ge0_eps_i). 
  case (hd{1} = HD).
  + rcondf{2} 1;auto => /#.
  if{2};auto;2:smt().
  call{2} adv_ll;auto=> /= &1 &2 [#] 3-> ? 2-> ??????? _ -> ? ??? ??. 
  by rewrite lap_ll /= /#. 
qed.

end section Ex.

end AbstractBetween.

op eps : real.
op delt : real.

axiom bound_eps : 0%r < eps < 1%r. (* 32%r * sqrt (2%r*M%r*ln(2%r/delt)). *)
axiom bound_delt : 0%r < delt < 1%r.
 
op eps' = eps/(4%r * sqrt (2%r*M%r*ln(2%r/delt))).

op t : int.
op u : int.

axiom tu : 2%r + 4%r  * ln (2%r/delt) / eps + 12%r/eps' * ln(8%r/eps') < (t-u)%r.

lemma gt0_ln_delt : 0%r < ln (2%r / delt).
proof.
  rewrite -ln1 ln_mono_ltr //;smt(bound_delt). 
qed.

lemma gt0_sqrt : 0%r < sqrt (2%r * M%r * ln (2%r / delt)).
proof.
  rewrite /( ^ ).
  have -> /= : !(2%r * M%r * ln (2%r / delt) <= 0%r).
  + smt (gt0_ln_delt gt0_M).
  apply exp_gt0.
qed.

lemma gt0_eps' : 0%r < eps'.
proof. smt (gt0_sqrt bound_eps). qed.


clone import AbstractBetween as Between with 
   op eps  <- eps/2%r,
   op eps' <- eps'/3%r,
   op delt <- delt/2%r,
   op w    <- delt/2%r,
   op t    <- t,
   op u    <- u
   proof *.
realize gt0_eps. 
proof. smt (bound_eps). qed.

realize gt0_eps'. 
proof. smt (gt0_eps').  qed.

realize bound_delt.
proof. smt(bound_delt). qed.

realize bound_w.
proof. smt(bound_delt). qed.

realize tu.
proof. 
  have H : 0%r <= ln(8%r/eps').
  + apply ln_ge0.
    rewrite ler_pdivl_mulr ?gt0_eps' /eps' /=. 
    rewrite ler_pdivr_mulr. smt (gt0_sqrt).
    have : 1%r <= (2%r * M%r * ln (2%r / delt)) ^ inv 2%r.
    + rewrite -(div1r 2%r) ge1_sqrt.
      have : inv 2%r <= ln ( 2%r / delt).
      + rewrite (ler_trans (ln (2%r)) _ _) ?ge_ln2 ln_mono //;smt (Top.bound_delt).
        (* PY: Top.... bizarre *)
      smt (gt0_M). 
    smt (bound_eps).
  rewrite (invf_div delt 2%r).
  have {H}: 0%r <= 12%r / eps' * ln (8%r / eps').
  + apply mulr_ge0;smt (gt0_eps').
  smt (tu).  
qed.

(* -------------------------------------------------------------------- *)

lemma concl (A<:Adv) : islossless A.adv => aequiv [ [ eps & delt] 
   BT_aux(A).main ~ BT_aux(A).main : adj d{1} d{2} /\ ={glob A} ==> ={res, glob A}
]. 
proof.
  move=> A_ll.
  conseq <[
      ((2%r * M%r * ln (inv (delt / 2%r))) ^ inv 2%r * eps_i +
            M%r * eps_i * ((exp eps_i)%RealExp - 1%r) + eps / 2%r) & (delt /
                                                                    2%r +
                                                                    delt /
                                                                    2%r)]>;
  2:apply (L A A_ll). 
  progress;2:smt().
  have := gt1_sqrt M (delt/2%r) _ gt0_M => //;1:smt(Top.bound_delt).
  rewrite invf_div => Hsqrt.
  have Heps_i: eps_i <= eps'.
  + rewrite -exp_mono /eps_i expK;1:smt (gt0_eps_i_aux).
    have /# := footnote5 eps' bound_t0u0 _ _.
    + rewrite gt0_eps' /= /eps' ;smt (bound_eps).
    rewrite /bound_t0u0.
    apply (ler_trans (2%r + 12%r / eps' * ln (8%r / eps')));2: smt(Top.tu). 
    (* Warning Top.tu seems stronger than what we need *)
    apply ler_paddl => //;apply ler_pmul.
    + apply divr_ge0 => //; smt (Top.gt0_eps').
    + apply ln_ge0;rewrite /eps';smt (bound_eps).
    + smt (Top.gt0_eps').
    apply ln_mono; smt (Top.gt0_eps').  
  pose eps'' := 2%r * eps'.
  apply (ler_trans ((sqrt (2%r * M%r * ln (2%r / delt)) * eps'' +
                     M%r * eps'' * ((exp (eps''/2%r))%RealExp - 1%r))/2%r + eps / 2%r)).
  + have HM : 0%r < M%r by smt (lt_fromint gt0_M).
    rewrite ler_add // mulrDl ler_add.
    + rewrite -(mulrA _ eps'') ler_wpmul2l /#.
    have -> : M%r * eps'' * ((exp (eps''/2%r))%RealExp - 1%r) / 2%r =
              M%r * eps' * ((exp (eps''/2%r))%RealExp - 1%r).
    + rewrite /eps'';fieldeq=> //.
    apply ler_pmul;1: smt (gt0_eps_i).  
    + have := le1Dx_exp eps_i;smt (gt0_eps_i).
    + apply ler_pmul;smt (gt0_eps_i).
    rewrite ler_add // exp_mono /eps'' /#.
  have := footnote2 M eps (delt/2%r) _ _ gt0_M.
  + smt (Top.bound_delt).
  + smt (bound_eps).
  rewrite (invf_div delt).
  have -> /# : eps / (2%r * sqrt (2%r * M%r * ln (2%r / delt))) = eps''.
  rewrite /eps'' /eps';smt().
qed.
