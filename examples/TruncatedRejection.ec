require import AllCore Real Distr.

require FelTactic.

type t.
op [lossless full] dt: t distr.

op P: t -> bool.
axiom negbP_witness: !P witness.
axiom neq0_dt_P: mu dt P <> 0%r.

module Rejection = {
  proc sample() = {
    var r;

    r <- witness;
    while (!P r) {
      r <$ dt;
    }
    return r;
  }
}.

module TruncatedRejection = {
  proc sample(k0) = {
    var k, r;

    r  <- witness;
    k  <- 0;
    while (!P r /\ k < k0) {
      r <$ dt;
      k <- k + 1;
    }
    return r;
  }
}.

section.

local equiv eq_upto k0:
  Rejection.sample ~ TruncatedRejection.sample:
    k0{!2} = k0
    ==> (P res{2} => ={res}).
proof.
proc.
proc change {1} 2: [ k: int ]
{
  k <- 0;
  while (!P r) {
    r <$ dt;
    k <- k + 1;
  }
}.
+ by while (={r}); auto.
splitwhile {1} ^while: (k < k0).
seq 3 3: (={k, r}).
+ by while (={k, r} /\ k0{!2} = k0); auto.
exlim r{2}=> r0; case @[ambient]: (P r0).
+ by move=> P_r0; rcondf {1} ^while; auto.
move=> negb_P_r0; conseq _ (: true ==> true: =1%r)=> //.
while (true) (if !P r then 1 else 0) 1 (mu dt P)=> //=.
+ by move=> r /#.
+ move=> ih; seq 2: true 1%r 1%r 0%r _; auto.
  by rewrite dt_ll.
+ by auto; rewrite dt_ll.
split.
+ smt(ge0_mu neq0_dt_P).
move=> z; wp; rnd; auto=> |> &0 negbP_r.
rewrite StdOrder.RealOrder.ler_eqVlt; left.
by apply: mu_eq=> x; case: (P x).
qed.

local lemma pr_trunc_sample k &m:
  Pr[TruncatedRejection.sample(k) @ &m: !P res] = (mu dt (predC P))^max 0 k.
proof.
case: (0 < k); last first.
+ move=> @/max ^ + -> //= - /lezNgt le0_k; rewrite RField.expr0.
  byphoare (: k = k0 ==> _)=> //; proc; rcondf ^while; auto.
  + by rewrite negbP_witness /#.
  by rewrite negbP_witness.
move=> /ltzW; elim: k.
+ rewrite /max /= RField.expr0.
  byphoare (: 0 = k0 ==> _)=> //; proc; rcondf ^while; auto.
  by rewrite negbP_witness /#.
move=> k' ge0_k' ih.
byphoare (: k' + 1 = k0 ==> _)=> //; proc.
splitwhile ^while: (k < k').
seq 3: (!P r) (mu dt (predC P) ^ max 0 k') (mu dt (predC P)) _ 0%r
       (!P r => k = k0 - 1).
+ while (k <= k').
  + by auto=> |> /#.
  by auto=> |> /#.
+ proc change [1..3]: { r <@ TruncatedRejection.sample(k'); }.
  + inline *; wp.
    while (k{1} = k1{2} /\ r{1} = r0{2} /\ k00{2} = k' /\ k0{1} = k' + 1).
    + by auto=> |> &1 &2 /#.
    by auto=> |> /#.
  call (: k0 = k' ==> !P res)=> //; bypr=> |> &0.
  have ->: Pr[TruncatedRejection.sample(k') @ &0: !P res]
         = Pr[TruncatedRejection.sample(k') @ &m: !P res].
  + by byequiv=> //; sim.
  by rewrite ih.
+ rcondt ^while; 1:by auto=> |> /#.
  rcondf ^while; 1:by auto=> |> /#.
  by wp; rnd; auto=> |>.
+ rcondf ^while; 1:by auto=> |> /#.
  by hoare; auto.
move=> _ _.
have ->: max 0 k' = k' by smt().
have ->: max 0 (k' + 1) = k' + 1 by smt().
by rewrite RField.exprS // RField.mulrC.
qed.

lemma upto_truncation r k &m:
    Pr[Rejection.sample() @ &m: res = r]
  <=   Pr[TruncatedRejection.sample(k) @ &m: res = r]
     + (mu dt (predC P))^max 0 k.
proof.
rewrite -(pr_trunc_sample k &m).
by byequiv (eq_upto k)=> //#.
qed.

end section.
