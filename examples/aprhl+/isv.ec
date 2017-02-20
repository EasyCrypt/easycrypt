(* -------------------------------------------------------------------- *)
require import Option Int IntExtra Real RealExtra Ring.
require import Distr List Aprhl StdRing StdOrder StdBigop.
(*---*) import IntID IntOrder RField RealOrder.

pragma -oldip.

(* -------------------------------------------------------------------- *)
op eps: { real | 0%r <= eps } as ge0_eps.

hint exact : ge0_eps.

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

(* -------------------------------------------------------------------- *)
op N : { int | 0 <= N } as ge0_N.
op M : { int | 0 <= M } as ge0_M.

hint exact : ge0_N ge0_M.

module M(A : Adv) = {
  proc main(d : db, t : int) : int list = {
    var l  : int list = [];
    var i  : int;
    var count : int;
    var q  : query;
    var x  : int;
    var t0 : int;

    i  <- 0;
    t0 <$ lap eps t;
    while (i < N) {
        q <@ A.adv(l);
        x <$ lap eps (evalQ q d);
        if (size l < M /\ t0 <= x) {l <- i :: l;}
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

local lemma L : aequiv [ [ (2%r    * M%r * eps + eps) & 0%r ]
  E.main ~ E.main : adj d{1} d{2} /\ ={t, glob A} ==> ={res, glob A}
].
proof.
proc=> /=; seq 2 2:
  (adj d{1} d{2} /\ ={t, l, i, glob A} /\ i{1} = 0 /\ l{1} = []).
+ by toequiv; auto.
seq 1 1 :
  (   adj d{1} d{2} /\ ={l, i, glob A}
   /\ i{1} = 0 /\ l{1} = []
   /\ t0{1} = t0{2} + 1)
  <[ eps & 0%r ]>.
+ by lap (-1) 1 => /#.
pweq ((l,glob A),(l,glob A)). 
 + while true (N - i); last by auto => /#.
 move=> z; wp; rnd predT; call adv_ll; auto; smt(lap_ll).
+ while true (N - i); last by auto => /#.
  move=> z; wp; rnd predT; call adv_ll; auto; smt(lap_ll).
+ by move=> /#.
move => [L GA] => /=. 
case (size L <= M). 
conseq <[ (bigi predT (fun (x : int) => 
if mem L (N - 1 - x) then 2%r * eps else 0%r) 0 N) & 0%r ]>.
  move=> &1 &2 /> _ lt_LM; rewrite addrK -big_mkcond.
  rewrite (partition_big (fun i => N - 1 - i) _ predT _ _ (undup L)) /=.
  + by rewrite undup_uniq.
  + by move=> /> y _; rewrite mem_undup.
  apply/(ler_trans (big predT (fun _ => 2%r * eps) (undup L))); last first.
    rewrite Bigreal.sumr_const mulrAC (mulrC (count _ _)%r).
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
(suffix l{2} L => ={l, glob A})) => //; first 4 by smt(ge0_eps).
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
qed.
end section Ex.
