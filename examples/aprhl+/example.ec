(* -------------------------------------------------------------------- *)
require import Int IntExtra Real RealExtra Ring.
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
  proc pre(i : int, log : int list) : unit
  proc adv(i : int, k : int, log : int list) : query
}.

(* -------------------------------------------------------------------- *)
op N : { int | 0 <= N } as ge0_N.
op M : { int | 0 <= M } as ge0_M.

hint exact : ge0_N ge0_M.

module M(A : Adv) = {
  proc main(d : db, t : int) : int list = {
    var l  : int list = [];
    var i  : int;
    var j  : int;
    var k  : int;
    var q  : query;
    var x  : int;
    var t0 : int;

    i  <- 0;
    t0 <$ lap eps t;
    while (i < N) {
      j <- 0;
      k <- M;
      A.pre(i, l);
      while (j < M) {
        q <@ A.adv(j, k, l);
        x <$ lap eps (evalQ q d);
        k <- (k = M /\ t0 <= x) ? j : k;
        j <- j + 1;
      }

      i <- i + 1;
      l <- k :: l;
    }

    return l;
  }
}.

(* -------------------------------------------------------------------- *)
section Ex.
declare module A : Adv.

local module E = M(A).

axiom adv_pure (m : glob A): hoare [A.adv : glob A = m ==> glob A = m].
axiom adv_ll : islossless A.adv.

local lemma L : aequiv [ [ (2%r    * N%r * eps + eps) & 0%r ]
  E.main ~ E.main : adj d{1} d{2} /\ ={t, glob A} ==> ={res}
].
proof.
proc=> /=; seq 2 2 :
  (adj d{1} d{2} /\ ={t, l, i, glob A} /\ i{1} = 0 /\ l{1} = []).
+ by toequiv; auto.
seq 1 1 :
  (   adj d{1} d{2} /\ ={l, i, glob A}
   /\ i{1} = 0 /\ l{1} = []
   /\ t0{1} = t0{2} + 1)
  <[ eps & 0%r ]>.
+ by lap (-1) 1 => /#.
awhile [ (fun _ => 2%r * eps) & (fun _ => 0%r) ] N [N - i - 1] (
  adj d{1} d{2} /\ ={l, i, glob A} /\ t0{1} = t0{2} + 1
) => //.
+ by rewrite mulr_ge0. by move=> /#. by move=> /#.
+ rewrite addrK sumr_const count_predT size_range max_ler //.
  by rewrite intmulr mulrAC.
+ by rewrite sumr_const intmulr.
move=> v. seq >> 4 4 : (
  adj d{1} d{2} /\ ={l, i, k, glob A} /\ t0{1} = t0{2} + 1 /\ v = N - i{1} - 1
); last first.
+ by toequiv; auto => /#.
seq 3 3 : (
  adj d{1} d{2} /\ ={l, i, j, k, glob A} /\ t0{1} = t0{2} + 1 /\
  j{1} = 0 /\ k{1} = M /\ i{1} < N /\ i{2} < N /\ v = N - i{1} - 1 /\
  N - i{1} - 1 <= N
); first by toequiv; sp; call(_ : true); auto => /#.
conseq (_ :
 adj d{1} d{2} /\ ={l, j, k, glob A} /\ t0{1} = t0{2} + 1 /\ j{1} = 0 /\ k{1} = M
 ==> ={k, glob A}); first 2 by move=> /#.
pweq ((k, glob A), (k, glob A)).
+ while true (Top.M - j); last by auto => /#.
  move=> z; wp; rnd predT; call adv_ll; auto; smt(lap_ll).
+ while true (Top.M - j); last by auto => /#.
  move=> z; wp; rnd predT; call adv_ll; auto; smt(lap_ll).
+ by move=> /#.
case=> {v} I gA; case: @[ambient] (I < 0) => [lt0_I|];
  first toequiv; first smt(ge0_eps).
  conseq (_ : ={j} /\ 0 <= k{2} /\ 0 <= j{1} ==> 0 <= k{2}); first 2 smt.
  while (0 <= k{2} /\ 0 <= j{2} /\ ={j}); last by auto=> /#.
  wp; sp; conseq (_ : 0 <= j{2} /\ 0 <= k{2} ==> 0 <= k{2});
    first 2 by move=> /#.
  rnd {1}; rnd{2};
    (call{1} (_ : true ==> true); first by apply/adv_ll); (* LL *)
    (call{2} (_ : true ==> true); first by apply/adv_ll); (* LL *)
    skip; smt(lap_ll).
rewrite ltrNge /= => ge0_I; case: @[ambient] (M < I) => [le|].
  toequiv; first smt(ge0_eps).
  conseq (_ : ={j} /\ j{2} = 0 /\ k{2} = M ==> k{2} <= M);
    first 2 by move=> /#.
  while (={j} /\ j{2} <= M /\ k{2} <= M); last by auto.
  wp; rnd{1}; rnd{2};
    (call{1} (_ : true ==> true); first apply adv_ll);
    (call{2} (_ : true ==> true); first apply adv_ll);
    skip; smt(lap_ll).
rewrite ltrNge /= => le_IM.
splitwhile {1} 1: (j < I); splitwhile {2} 1: (j < I).
seq 1 1 :
  (   adj d{1} d{2} /\ ={l, j, glob A}
   /\ t0{1} = t0{2} + 1
   /\ j{1} = I
   /\ 0 <= k{2}
   /\ ((={k} /\ k{1} = M) \/ k{2} < I)).
+ toequiv. while
  (   adj d{1} d{2} /\ ={l, j, glob A}
   /\ t0{1} = t0{2} + 1
   /\ 0 <= j{1} <= I
   /\ 0 <= k{2} <= M
   /\ ((={k} /\ k{1} = M) \/ k{2} < I)); last by auto; move=> /> /#.
  case (k{2} < I).
  + wp; rnd{1}; rnd{2};
      exists* (glob A){1}, (glob A){2}; elim* => AL AR.
      call {1} (_ : glob A = AL ==> glob A = AL);
        first by conseq adv_ll (adv_pure AL).
      call {2} (_ : glob A = AL ==> glob A = AL);
        first by conseq adv_ll (adv_pure AL).
      auto; smt(lap_ll).
  seq 1 1 :
  (   adj d{1} d{2} /\ ={l, j, k, q, glob A}
   /\ t0{1} = t0{2} + 1
   /\ 0 <= j{1} < I
   /\ 0 <= k{2} <= M
   /\ k{1} = M).
  + by call (_ : true); auto=> /#.
  seq 1 1 :
  (   adj d{1} d{2} /\ ={l, j, k, q, glob A}
   /\ t0{1} = t0{2} + 1
   /\ 0 <= j{1} < I
   /\ 0 <= k{2} <= M
   /\ x{1} <= x{2} + 1
   /\ k{1} = M).
  + conseq (_ : adj d{1} d{2} /\ ={q} ==> x{1} <= x{2} + 1);
      first 2 by move=> /#.
    ofequiv;
      exists* (evalQ q d){1}; elim* => e1;
      exists* (evalQ q d){2}; elim* => e2.
    by lap (e2 - e1) 0 => />; smt(one_sens).
  by auto=> /> /#.
move: le_IM; rewrite ler_eqVlt => -[eq_IM|lt_IM].
  (rcondf {1} 1; last rcondf {2} 1); first 2 auto=> /#.
  toequiv; first smt(ge0_eps). by auto=> /#.
(rcondt {1} 1; last rcondt {2} 1); first 2 auto=> /#.
seq 4 4 : (
  ={l, j} /\ j{1} = I+1 /\
    (I = k{2} /\ gA = (glob A){2} =>
     I = k{1} /\ gA = (glob A){1})
) <[ (2%r * eps) & 0%r ]>.
+ exists* k{2}; elim* => kR; case: @[ambient] (kR < I) => [lt|].
  + conseq (_ : ={l, j, glob A} /\ j{1} = I /\ k{2} < I ==>
      ={l, j, glob A} /\ j{1} = I+1 /\ k{2} < I); first 2 by auto=> /#.
    toequiv; first smt(ge0_eps).
    wp; conseq (_ : ={glob A} ==> ={glob A});
      first 2 by move=> /#.
    rnd{1}; rnd{2}; conseq (_ : ={glob A} ==> ={glob A}).
    + smt(lap_ll).
    exists* (glob A){1}, (glob A){2}; elim* => AL AR.
    call {1} (_ : glob A = AL ==> glob A = AL);
      first by conseq adv_ll (adv_pure AL).
    call {2} (_ : glob A = AR ==> glob A = AR);
      first by conseq adv_ll (adv_pure AR).
    by auto=> /#.
      move=> le_IkR. seq 1 1 : (
       adj d{1} d{2} /\ ={l, j, q, k, glob A} /\ j{1} = I
    /\ t0{1} = t0{2} + 1 /\ k{1} = M).
  + toequiv; conseq (_ : ={j, k, l, glob A} ==> ={q, glob A});
      first 2 by auto=> /#.
    call (_ : true); first by auto.
  seq 1 1 : (
        adj d{1} d{2} /\ ={l, j, q, k, glob A}
     /\ x{1}  = x{2} + 1
     /\ t0{1} = t0{2} + 1
     /\ k{1}  = Top.M
     /\ j{1}  = I
  ) <[ (2%r * eps) & 0%r ]>.
  + by lap (-1) 2; smt(one_sens).
  by toequiv; auto=> /#.
toequiv; while (={j, l} /\ I < j{1} /\
  (I = k{2} && gA = (glob A){2} => I = k{1} && gA = (glob A){1}));
  last by auto=> /#.
wp; rnd{1}; rnd{2}.
conseq
  (_ : ={j, l} /\ (I = k{2} && gA = (glob A){2} =>
    I = k{1} && gA = (glob A){1}));
  first by smt(lap_ll).
exists* (glob A){1}, (glob A){2}; elim* => AL AR.
call {1} (_ : glob A = AL ==> glob A = AL);
  first by conseq adv_ll (adv_pure AL).
call {2} (_ : glob A = AR ==> glob A = AR);
  first by conseq adv_ll (adv_pure AR).
by skip; smt().
qed.
end section Ex.
