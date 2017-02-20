(* -------------------------------------------------------------------- *)
require import Option Int IntExtra Real RealExtra RealExp Ring.
require import Distr List Aprhl StdRing StdOrder StdBigop.
(*---*) import IntID IntOrder RField RealOrder.

pragma -oldip.

abbrev sqrt (x:real) = x ^ (1%r/2%r).

(* -------------------------------------------------------------------- *)
op N : { int | 0 <= N } as ge0_N.
op M : { int | 0 <= M } as ge0_M.

hint exact : ge0_N ge0_M.

(* -------------------------------------------------------------------- *)
op eps: { real | 0%r <= eps } as ge0_eps.
op delt : {real | 0%r < delt} as gt0_delt.

hint exact : ge0_eps gt0_delt.


(* -------------------------------------------------------------------- *)
op t : int.
op u : int.
axiom tu : 12%r/eps * ln(8%r/eps) + 4%r/eps * ln(1%r/delt)< (t - u)%r.

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


module M(A : Adv) = {
  proc main(d : db) : int list = {
    var l  : int list = [];
    var i  : int;
    var count : int;
    var q  : query;
    var x  : int;
    var t0 : int;
    var u0 : int;
    var n  : int;

    i  <- 0;
    n <$ lap (eps/2%r) 0;
    t0 <- t - n;
    u0 <- u + n;   
    while (i < N) {
        q <@ A.adv(l);
        x <$ lap (eps/6%r) (evalQ q d);
        if (size l < M /\ u0 <= x <= t0) {l <- i :: l;}
        i <- i + 1;   
    }

    return l;
  }
}.

(* -------------------------------------------------------------------- *)
lemma drop_add ['a] (s : 'a list) (i j : int) :
  0 <= i => 0 <= j => drop (i + j) s = drop i (drop j s).
proof. by elim: s i j => /#. qed.

pred suffix ['a] (p s : 'a list) =
  exists n, (0 <= n /\ drop n s = p).

lemma suffixI ['a] (p1 p2 s : 'a list) :
  suffix p1 s => suffix p2 s => size p1 = size p2 => p1 = p2.
proof. by case=> [n1 [ge0_n1 <-]] [n2 [ge0_n2 <-]] eq_sz; smt. qed.

lemma suffix_refl ['a] (s : 'a list) : suffix s s.
proof. by exists 0; rewrite drop0. qed.

lemma suffix_cons ['a] (p s: 'a list) (x : 'a) :
  suffix (x :: p) s => suffix p s /\ mem s x.
proof.
case=> n [ge0_n eq]; split; last first.
  by apply/(mem_drop n); rewrite eq.
exists (n+1); rewrite addr_ge0 //=.
by rewrite addzC drop_add // eq /= drop0.
qed.

(* -------------------------------------------------------------------- *)
section Ex.
declare module A : Adv.

local module E = M(A).

axiom adv_ll : islossless A.adv.

op w : {real | 0%r < w} as gt0_w.
hint exact : gt0_w.

local lemma L : aequiv [ [ (M%r * eps/2%r + eps/2%r) & delt ]
  E.main ~ E.main : adj d{1} d{2} /\ ={glob A} ==> ={res, glob A}
].
proof.
proc=> /=.
pweq ((l,glob A),(l,glob A)):  (`|n%r| > 2%r/eps*ln(1%r/delt))=> //.
+ while true (N - i).
  auto; call adv_ll; skip; progress; first by (apply lap_ll); smt.
  smt.
  auto; smt.
+ while true (N - i).
  auto; call adv_ll; skip; progress; first by (apply lap_ll); smt.
  smt.
  auto; smt.
+ move=> &m2.
  seq 3 : (2%r / eps * ln (1%r / delt) < `|n%r|) delt 1%r _ 0%r true  => //.
  + rnd;auto;progress.
  admit.
  by conseq (_ : _ ==> false).
  
move => [L GA].
seq 3 3 :
  (   adj d{1} d{2} /\ ={l, i, glob A}
   /\ i{1} = 0 /\ l{1} = []
   /\ n{1} = n{2} - 1)
  <[ (eps/2%r) & 0%r ]>.
+ seq 2 2 : (adj d{1} d{2} /\ ={l, i, glob A}
   /\ i{1} = 0 /\ l{1} = []).
  + by toequiv;auto.
  by lap (1) 1=> /#.
case (`|n{1}%r| <= 2%r / eps * ln (1%r / delt)); last first.
+ toequiv. smt (ge0_M ge0_eps).
  conseq (_ : _ ==> true). smt ml=0.
  while (={i});wp;last by auto.
  rnd{1};rnd{2}. call{1} adv_ll. call{2} adv_ll; auto.
  by smt (lap_ll).

seq 2 2:
  (   adj d{1} d{2} /\ ={l, i, glob A}
   /\ i{1} = 0 /\ l{1} = []
   /\ t0{1} = t0{2} + 1
   /\ u0{1} = u0{2} - 1
   /\ 12%r/eps * ln(8%r/eps) < (t0{2} - u0{2})%r).
+ toequiv; auto => />;progress;try ringeq.
  move: tu H0. admit.

case @[ambient] (size L <= M) => LM.
+ conseq <[ (bigi predT (fun (x : int) => 
              if mem L (N - 1 - x) then eps/2%r else 0%r) 0 N) & 0%r ]>.
  + move=> &1 &2 /> _ _; rewrite addrK -big_mkcond.
    rewrite (partition_big (fun i => N - 1 - i) _ predT _ _ (undup L)) /=.
    + by rewrite undup_uniq.
    + by move=> /> y _; rewrite mem_undup.
    apply/(ler_trans (big predT (fun _ => eps/2%r) (undup L))); last first.
    + rewrite Bigreal.sumr_const -mulrA. 
      rewrite ler_wpmul2r. smt (ge0_eps).
      rewrite count_predT le_fromint.
      by apply/(IntOrder.ler_trans _ _ _ (size_undup _)).
    apply/Bigreal.ler_sum=> i _ /=; rewrite big_mkcond /=.
    case: (0 <= N - 1 - i < N) => h; last first.
    + rewrite -big_mkcond big_seq_cond big_pred0 //= 2:[smt (ge0_eps)].   
      by move=> j; rewrite mem_range /#.
    rewrite (bigD1 _ _ (N - 1 - i)) ?mem_range ?range_uniq //=.
    by rewrite big1 1:/# /=; case: (_ /\ _) => //=; smt (ge0_eps).
  awhile [ (fun x => if (mem L (N - 1 - x)) then eps/2%r else 0%r) 
           & (fun _ => 0%r) ] N [N - i - 1] (
           adj d{1} d{2} /\ ={i} /\ t0{1} = t0{2} + 1 /\ u0{1} = u0{2} - 1 /\  
           12%r/eps * ln(8%r/eps) < (t0{2} - u0{2})%r /\
           (suffix l{1} L => ={l, glob A})) => //; first 4 by smt(ge0_eps).
  + by rewrite sumr_const intmulr.
  move => v; case (suffix (i{1}::l{1}) L).
  + conseq  <[ (eps/2%r) & 0%r ]>;1:smt(suffix_cons).
    seq 1 1:
     (adj d{1} d{2} /\
      ={i, l, q, glob A} /\
      t0{1} = t0{2} + 1 /\ u0{1} = u0{2} - 1 /\ suffix (i{1}::l{1}) L /\ v = N - i{1} - 1 /\
      12%r/eps * ln(8%r/eps) < (t0{2} - u0{2})%r).
    + toequiv.
      by call ( _ : true); skip; smt(suffixI suffix_cons).
    seq >> 1 1: 
      (adj d{1} d{2} /\
       ={i, l, q, glob A} /\
       t0{1} = t0{2} + 1 /\ 
       u0{1} = u0{2} - 1 /\ suffix (i{1} :: l{1}) L /\ v = N - i{1} - 1 /\
       (u0{2} <= x{2} <= t0{2} <=> u0{1} <= x{1} <= t0{1}) /\
       12%r / eps * ln (8%r / eps) < (t0{2} - u0{2})%r).
    + exists * u0{1}, t0{1}, u0{2}, t0{2}  ;elim * => p q r s.

      conseq (_ : _ ==> (p <= x{1} <= q) = (r <= x{2} <= s));1: smt ().
      conseq <[(ln
                ((exp (2%r * (eps / 6%r)))%RealExp /
                (1%r - (exp ((- 12%r / eps * ln (8%r / eps) * (eps / 6%r)) / 2%r))%RealExp))) & 0%r]> => />.
      + have -> : ((- 12%r / eps * ln (8%r / eps) * (eps / 6%r)) / 2%r) = (- 1%r) * ln (8%r / eps). 
        fieldeq=> //. admit(* need 0 < eps *).
        admit.
      int lap [p, q] [r,s] 2 & (12%r / eps * ln(8%r / eps)) & 1.
      + admit. 
      + progress. 
        + smt (one_sens). 
        + smt(). 
        + admit. 
        + smt (). 
        + smt(). 
        + admit. 
        smt(). 
      by smt ().
    toequiv;wp 1 1;if;auto;smt ml=0.
  case (suffix l{1} L).
  + conseq (_: _ ==>  
      ( ={i} /\ ((suffix l{1} L => ={l, glob A})) /\ i{1} < N = i{2} < N /\ N - i{1} - 1 < v)) => //.
    seq << 1 1: 
     (adj d{1} d{2} /\ ={i, q } /\
     t0{1} = t0{2} + 1 /\ u0{1} = u0{2} - 1 /\ 
     12%r * ln (8%r / eps) / eps < (t0{2} - u0{2})%r /\
     suffix l{1} L /\ ={l, glob A} /\ 
     i{1} < N /\ v = N - i{1} - 1 /\
     ! suffix (i{1} :: l{1}) L).
    + toequiv;call ( _ : true); skip; smt(suffixI suffix_cons).
    exists* (evalQ q d){1}, (evalQ q d){2}; elim* => e1 e2.
    seq >> 1 1 : 
      (adj d{1} d{2} /\  (e1 = evalQ q{1} d{1} /\ e2 = evalQ q{2} d{2}) /\
        ={i, q, l, glob A} /\ x{1} = x{2} + e1 - e2 /\
         suffix l{1} L /\  t0{1} = t0{2} + 1 /\ u0{1} = u0{2} - 1 /\ 
         i{1} < N /\ v = N - i{1} - 1 /\
         12%r / eps * ln (8%r / eps) < (t0{2} - u0{2})%r /\
         ! suffix (i{1} :: l{1}) L).
    lap (e2 - e1) 0=> />. smt (ge0_eps). smt (). smt().
    toequiv. auto=> |>. 
    move=> &1 &2. have -> /= : N - (i{2} + 1) - 1 < N - i{2} - 1 by smt().
    progress. smt (one_sens).

  toequiv;1:smt(ge0_eps).
  by wp;rnd{1};rnd{2};call{1} adv_ll; call{2} adv_ll;skip;smt (lap_ll).

toequiv;1: smt(ge0_eps ge0_M).
while (size l{1} <= M /\ ={i}).
+ wp; rnd{1};rnd{2}; call{1} adv_ll; call{2} adv_ll;skip;smt (lap_ll).
auto;smt.
qed.























lap (e2 - e1) 0=> />. smt (ge0_eps). smt.
move=> &1 &2 /one_sens /(_ q{2});rewrite distrC ler_norml. smt ml=0.
search "`|_|" (&&).

smt ml=0.
print one_sens.
smt(one_sens).

lap 
 

ofequiv;   
wp.
rnd{1}; rnd{2}.
(call{1} (_ : true ==> true); first by apply/adv_ll). 
(call{2} (_ : true ==> true); first by apply/adv_ll). 
skip; smt(lap_ll).

toequiv.
smt(ge0_eps ge0_M).
while (size l{2} <= M /\ ={i}).
wp; rnd{1};rnd{2}.
(call{1} (_ : true ==> true); first by apply/adv_ll). 
(call{2} (_ : true ==> true); first by apply/adv_ll). 
skip; smt(lap_ll).
skip; smt(ge0_M). 
qed.


awhile [ (fun x => if (mem L (N - 1 - x)) then eps/2%r else 0%r) 
& (fun _ => 0%r) ] N [N - i - 1] (
  adj d{1} d{2} /\ ={i} /\ t0{1} = t0{2} + 1 /\ 
(suffix l{2} L => ={l, glob A})) => //.
+ smt(ge0_eps). smt ml=0. smt ml=0.
 first 4 by smt(ge0_eps).
by rewrite sumr_const intmulr.
move => v.
case (suffix (i{2}::l{2}) L).
conseq  <[ (2%r * eps) & 0%r ]>.
smt(suffix_cons).
seq 1 1: (adj d{1} d{2} /\
  ={i, l, q, glob A} /\
  t0{1} = t0{2} + 1 /\ suffix (i{2}::l{2}) L /\ v = N - i{1} - 1).
toequiv.
call ( _ : true); skip; smt(suffixI suffix_cons).
seq 1 1: (adj d{1} d{2} /\
   ={i, l, q, glob A} /\
   t0{1} = t0{2} + 1 /\ suffix (i{2}::l{2}) L /\ v = N - i{1} - 1 /\
  suffix (i{2} :: l{2}) L /\ x{1}=x{2}+1) <[ (2%r * eps) & 0%r ]>.
lap (-1) 2 => />; smt(one_sens).
toequiv; auto.
smt.
toequiv.
smt(ge0_eps).
case (suffix l{2} L).
seq >> 1 1: (adj d{1} d{2} /\
     ={i, q } /\
     t0{1} = t0{2} + 1 /\
     suffix l{2} L /\ ={l, glob A} /\ 
    i{1} < N /\ v = N - i{1} - 1 /\
   ! suffix (i{2} :: l{2}) L).
call ( _ : true); skip; smt(suffixI suffix_cons).
wp.
 exists* (evalQ q d){1}; elim* => e1;
 exists* (evalQ q d){2}; elim* => e2.

ofequiv;   by lap (e2 - e1) 0 => />; smt(one_sens).
wp.
rnd{1}; rnd{2}.
(call{1} (_ : true ==> true); first by apply/adv_ll). 
(call{2} (_ : true ==> true); first by apply/adv_ll). 
skip; smt(lap_ll).

toequiv.
smt(ge0_eps ge0_M).
while (size l{2} <= M /\ ={i}).
wp; rnd{1};rnd{2}.
(call{1} (_ : true ==> true); first by apply/adv_ll). 
(call{2} (_ : true ==> true); first by apply/adv_ll). 
skip; smt(lap_ll).
skip; smt(ge0_M). 









rewrite count_predT. le_fromint.

mulrAC (mulrC (count _ _)%r).
    rewrite ler_wpmul2l ?mulr_ge0 // count_predT le_fromint.
    by apply/(IntOrder.ler_trans _ _ _ (size_undup _)).
  apply/Bigreal.ler_sum=> i _ /=; rewrite big_mkcond /=.
  case: (0 <= N - 1 - i < N) => h; last first.
    rewrite -big_mkcond big_seq_cond big_pred0 ?mulr_ge0 //=.
    by move=> j; rewrite mem_range /#.
  rewrite (bigD1 _ _ (N - 1 - i)) ?mem_range ?range_uniq //=.
  by rewrite big1 1:/# /=; case: (_ /\ _) => //=; rewrite mulr_ge0.
awhile [ (fun x => if (mem L (N - 1 - x)) then 2%r * eps else 0%r) 
& (fun _ => 0%r) ] N [N - i - 1] (
  adj d{1} d{2} /\ ={i} /\ t0{1} = t0{2} + 1 /\ 
(suffix l{2} L => ={l, glob A})) => //.


+ awhile ac w [ (eps'/3%r) & (0%r) ] [L & M] [(N - i) & N]
       ( `|n{1}%r| <= 2%r / eps * ln (2%r / delt) /\
          adj d{1} d{2} /\ ={i} /\ t0{1} = t0{2} + 1 /\ u0{1} = u0{2} - 1 /\
          (suffix l{2} L => ={l, glob A})). (* => //. *)
  + admit.
  + smt ml=0.
  + admit.
  + admit.
  + smt ml=0.
  + admit.
  + admit.
  
  move=> k Hmem.




+ smt ml=0. + smt ml=0.
+ progress. 
  case (suffix l{2} l{1}). smt ml=0.

 + smt ml=0.

 first 4 by smt(ge0_eps).
by rewrite sumr_const intmulr.
move => v.
case (suffix (i{2}::l{2}) L).
conseq  <[ (2%r * eps) & 0%r ]>.
smt(suffix_cons).
seq 1 1: (adj d{1} d{2} /\
  ={i, l, q, glob A} /\
  t0{1} = t0{2} + 1 /\ u0{1} = u0{2} - 1 /\suffix (i{2}::l{2}) L /\ v = N - i{1} - 1).
toequiv.
call ( _ : true); skip; smt(suffixI suffix_cons).
seq  >> 1 1: (adj d{1} d{2} /\
  ={i, l, q, glob A} /\
  t0{1} = t0{2} + 1 /\
  u0{1} = u0{2} - 1 /\ suffix (i{2} :: l{2}) L /\ v = N - i{1} - 1 /\
  (t0{2} <= x{2} <= u0{2} <=> t0{1} <= x{1} <= u0{1})). 
admit. (* critical iteration. Note that we need iff *)
toequiv; wp; skip; progress; first 6 by smt.
case (suffix l{2} L).
seq 1 1: (adj d{1} d{2} /\
     t0{1} = t0{2} + 1 /\
     u0{1} = u0{2} - 1 /\ ={l, q, glob A,i} /\
    i{1} < N /\ v = N - i{1} - 1 /\ 
   ! suffix (i{2} :: l{2}) L /\ 
  suffix l{2} L).
toequiv; call ( _ : true); skip; smt(suffixI suffix_cons).
toequiv.
smt(ge0_eps ge0_M).
wp.
exists* (evalQ q d){1}; elim* => e1;
exists* (evalQ q d){2}; elim* => e2.
ofequiv.  lap (e2 - e1) 0; smt(one_sens suffixI suffix_cons).
toequiv.
smt(ge0_eps ge0_M).
wp; rnd{1}; rnd{2};
(call{1} (_ : true ==> true); first by apply/adv_ll). 
(call{2} (_ : true ==> true); first by apply/adv_ll). 
skip; progress; smt(lap_ll).
toequiv.
smt(ge0_eps ge0_M).
while (size l{2} <= M /\ ={i}).
wp; rnd{1};rnd{2}.
(call{1} (_ : true ==> true); first by apply/adv_ll). 
(call{2} (_ : true ==> true); first by apply/adv_ll). 
skip; smt(lap_ll).
skip; smt(ge0_M). 
qed.
end section Ex.
