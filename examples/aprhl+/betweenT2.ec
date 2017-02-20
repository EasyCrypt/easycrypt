(* -------------------------------------------------------------------- *)
require import Option Int IntExtra Real RealExtra RealExp Ring.
require import Distr List Aprhl StdRing StdOrder StdBigop.
(*---*) import IntID IntOrder RField RealOrder.

pragma -oldip.

(* -------------------------------------------------------------------- *)
(* Move this: it should be in the standard lib *)
axiom lap_bound_le eps delt:
     0%r < eps => 0%r < delt => 
     1%r - delt <=
     mu (lap (eps / 2%r) 0) (fun (x : int) => `|x%r| <= 2%r * ln (inv delt) / eps).

lemma lap_bound_lt eps delt:
     0%r < eps => 0%r < delt => 
     mu (lap (eps / 2%r) 0) (fun (x : int) => 2%r * ln (inv delt) / eps < `|x%r|) <= delt.
proof.
  move=> Heps Hdelt.
  rewrite -(mu_eq _ (predC (fun (x : int) => (`|x%r| <= 2%r * ln (inv delt) / eps)))).
  + move=> ? /#.
  rewrite mu_not lap_ll.
  have /# := lap_bound_le _ _ Heps Hdelt.
qed.

abbrev sqrt (x:real) = x ^ (1%r/2%r).

(* -------------------------------------------------------------------- *)
op N : { int | 0 <= N } as ge0_N.
op M : { int | 0 <= M } as ge0_M.

hint exact : ge0_N ge0_M.

(* -------------------------------------------------------------------- *)
op eps: { real | 0%r < eps } as gt0_eps.
op delt : {real | 0%r < delt} as gt0_delt.

lemma ge0_eps : 0%r <= eps.
proof. smt (gt0_eps). qed.

lemma gt0_delt2 : 0%r < delt/2%r.
proof. smt (gt0_delt). qed.

hint exact : gt0_eps ge0_eps gt0_delt gt0_delt2.
op eps' : real = eps/4%r * sqrt (2%r*M%r*ln(2%r/delt)).

(* -------------------------------------------------------------------- *)
op t : int.
op u : int.
axiom tu : 2%r + 4%r * ln (2%r/delt) / eps + 6%r/eps' * ln(4%r/eps') < (t-u)%r.

(* Should probably be:

axiom tu : 4%r * ln (2%r/delt) / eps + 6%r/eps' * ln(4%r/eps') < (t-u)%r.

*)



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

(*
module Minit(A : Adv) = {
  proc main(d : db) : int list = {
    var l  : int list;
    var i  : int;
    var q  : query;
    var x  : int;
    var t0 : int;
    var u0 : int;
    var n  : int;

    n  <$ lap (eps/2%r) 0;
    i  <- 0;
    l  <- [];
    t0 <- t - n;
    u0 <- u + n;   
    while (i < N /\ size l < M) {
      q <@ A.adv(l);
      x <$ lap (eps'/3%r) (evalQ q d);
      if (u0 <= x <= t0) l = i::l;
    }

    return l;
  }
}.
*)

module M(A : Adv) = {
  proc main(d : db) : int list = {
    var l  : int list;
    var i, i', hd: int;
    var count : int;
    var q  : query;
    var x  : int;
    var t0 : int;
    var u0 : int;
    var n  : int;

    n  <$ lap (eps/2%r) 0;
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
          x <$ lap (eps'/3%r) (evalQ q d);
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

(* -------------------------------------------------------------------- *)
section Ex.
declare module A : Adv.

local module E = M(A).

axiom adv_ll : islossless A.adv.

op w = delt/2%r.

lemma gt0_w : 0%r < w.
proof. smt (gt0_delt). qed.
hint exact : gt0_w. 

op bound_bad : real = delt/2%r.

(* This is the lower bound for t0<1> - u0<1> . *)

op bound_t0u0: real = (t - u)%r - 4%r * ln (2%r/delt) / eps.

(* Should probably be lower bound for t0<2> - u0<2>:

op bound_t0u0' : real = (t - u)%r - 4%r * ln (2%r/delt) / eps - 2.

*)

op eps_i : real = 
  ln
    ((exp (2%r * (eps' / 3%r)))%RealExp /
    (1%r - (exp ((- (bound_t0u0 - 2%r) * (eps' / 3%r)) / 2%r))%RealExp)).

(* Should probably be:

op eps_i : real = 
  ln
    ((exp (2%r * (eps' / 3%r)))%RealExp /
    (1%r - (exp ((- (bound_t0u0) * (eps' / 3%r)) / 2%r))%RealExp)).

OR

op eps_i : real = 
  ln
    ((exp (2%r * (eps' / 3%r)))%RealExp /
    (1%r - (exp ((- (bound_t0u0' + 2%r) * (eps' / 3%r)) / 2%r))%RealExp)).

These are the same. *)


lemma ge0_eps_i : 0%r <= eps_i.
proof.
  rewrite /eps_i.
  admit.
qed.


local lemma L : aequiv [ [ (* ((2%r * N%r * ln (inv w)) ^ inv 2%r * eps_i +
N%r * eps_i * ((exp eps_i)%RealExp - 1%r) + eps/2%r) *)
                           eps & delt ]
  E.main ~ E.main : adj d{1} d{2} /\ ={glob A} ==> ={res, glob A}
].
proof.
  proc=> /=.
  utb ((l, glob A), (l, glob A)) : [ (`|n%r| > 2%r/eps*ln(2%r/delt)), bound_bad]=> //.
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
    seq 1 : (2%r / eps * ln (2%r / delt) < `|n%r|) bound_bad 1%r _ 0%r true  => //.
    + rnd;auto;progress.  
      have := lap_bound_lt eps (delt/2%r) gt0_eps gt0_delt2.
      by rewrite invf_div.
    by conseq (_ : _ ==> false).
  
  seq 1 1 : (adj d{1} d{2} /\ ={glob A} /\ n{1} = n{2} - 1) <[ (eps/2%r) & 0%r ]>.
  + by lap (1) 1=> /#.
  conseq <[((2%r * M%r * ln (inv w)) ^ inv 2%r * eps_i +
             M%r * eps_i * ((exp eps_i)%RealExp - 1%r)) & w]>.

(* Should probably be:

  conseq <[((2%r * M%r * ln (inv w)) ^ inv 2%r * eps_i +
             M%r * eps_i * ((exp eps_i)%RealExp - 1%r)) & w]>.

*)

  + progress;2:smt().
    admit. (* Justin, PY *)

(* Proceed in two steps:

(i) Show if bound_t0u0' > (12%r / eps') * ln (8%r/eps') - 2, then eps_i < (exp eps')

(See footnote 5, with lambda := eps', note eps' < 1%r/2%r.)

(ii) Show that if eps' = eps/2%r / (2%r * sqrt(2%r * M * ln(inv w))) and w < 1%r/2%r, then

eps' * sqrt(2%r * M * ln(inv w)) + M * eps' * ((exp eps') - 1) < eps/2%r

(See footnote 2, with w = delt/2%r.)

Combine to show that if

(a) bound_t0u0' > (12%r / eps') * ln (8 %r/eps') - 2, and
(b) eps' = eps/2%r / (2%r * sqrt(2%r * M * ln(inv w))), and
(c) w < 1%r/2%r, then

eps_i * sqrt(2%r * M * ln(inv w)) + M * eps_i * ((exp eps_i) - 1) < eps/2%r.

*)
  case (! 2%r / eps * ln (2%r / delt) < `|n{1}%r|);first last.
  + toequiv. 
     admit. (* PY *)
     smt (gt0_w).
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
  + toequiv;auto => /#.
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
             (i{1} < N /\ size l{1} < Top.M) /\ bound_t0u0 <= (t0{1} - u0{1})%r /\
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
           ((hd{1} = -1 \/ hd{1} = HD) => ={i, hd, glob A}))=> //.
  + smt (ge0_N).
  + smt (ge0_eps_i).
  + smt ().          
  + smt ().
  + smt ().
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
      have Hpos : 0%r <= 6%r/eps' * ln(4%r/eps').
      + admit.
      int lap [p, q] [r,s] 2 & (bound_t0u0 - 2%r) & 1.
(* Should be

bound_t0u0' + 2%r

OR

bound_t0u0

They are the same. *)

      + by apply ge0_eps_i.
      + progress. 
        + smt (one_sens). 
        + smt(). 
        + smt (tu). 
        + smt ().
        + smt ().
        + smt (tu).
        smt ().
      smt().
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
