require import AllCore List Int Real IntDiv.
require import Distr DInterval.
require (*--*) Plug_and_Pray.

const q : { int | 0 < q } as gt0_q.

module type Orcl = {
  proc query(n : int) : int
}.

module type Adv (O : Orcl) = {
  proc run() : bool
}.

module G0 (AF : Adv) = {
  var b : bool
  var k : int

  module O = {
    proc query(n : int) : int = {
      k <- n;
      return k;
    }
  }

  module A = AF(O)

  proc main(x : unit) : unit = {
    k <- 0;
    b <@ A.run();
    k <- k %% q;
  }
}.

module G1(AF : Adv) = {
  var b : bool
  var k : int
  var i : int

  module O = {
    proc query(n : int) : int = {
      k <- n;
      return k;
    }
  }

  module A = AF(O)

  proc main(x : unit) : unit = {
    i <$ [0..q - 1];
    k <- 0;
    b <@ A.run();
    k <- k %% q;
  }
}.

clone import Plug_and_Pray as PnP with
  type tres    <- unit,
  type tval    <- int,
  type tin     <- unit,
  op   indices <- range 0 q
proof indices_not_nil by smt(size_range gt0_q).

(*
   We first apply the general Lemma that yields
     1 / q * Pr[ G0 : Ev] = Pr[ G0; i=$[0..q-1] : Ev /\ i = G0.k]
   where ``G0; i=$[0..q-1]'' is expressed as an application of the
   ``Guess'' functor and we use an if-then-else to ensure that
   G0.k is in [0..q-1].
*)
lemma Bound_aux &m (A <: Adv {-G0}):
  (1%r/q%r) * Pr[ G0(A).main() @ &m : G0.b ]
  = Pr[ Guess(G0(A)).main() @ &m :  G0.b /\ res.`1 = G0.k ].
proof.
pose phi:= fun (g : (glob G0(A))) (_ : unit)=> g.`2.
pose psi:= fun (g : (glob G0(A))) (_ : unit)=> if 0 <= g.`3 < q then g.`3 else 0.
have:= PBound (G0(A)) phi psi tt &m _.
+ by move=> @/psi gG o /=; rewrite mem_range; case: (0 <= gG.`3 < q)=> //= _; exact/gt0_q.
have ->: card = q by rewrite undup_id 1:range_uniq size_range #smt:(gt0_q).
have -> //=: Pr[Guess(G0(A)).main() @ &m: phi (glob G0(A)) res.`2 /\ res.`1 = psi (glob G0(A)) res.`2]
             = Pr[Guess(G0(A)).main() @ &m: G0.b /\ res.`1 = G0.k].
byequiv (: ={glob G0(A)} ==> _)=> //=.
conseq (: _ ==> ={glob G0, res} /\ 0 <= G0.k{1} < q); first by smt().
proc; rnd; inline *; wp.
conseq (: ={glob G0})=> //=.
+ move=> &1 &2 _ bL kL bR kR [#] ->> ->> iL -> /=.
  by rewrite modz_ge0 2:ltz_pmod; smt(gt0_q).
call (: ={G0.k}).
+ by sim.
by auto.
qed.

(*
  We now transfer the previous lemma to G0 and G1 by relating
  Guess(G0) with G1.
*)
lemma Bound &m (A <: Adv{-G1,-G0}):
    (1%r/q%r) * Pr[ G0(A).main() @ &m : G0.b ]
  = Pr[ G1(A).main() @ &m :  G1.b /\ G1.k = G1.i].
proof.
rewrite (Bound_aux &m A).
byequiv (: ={glob A} ==> ={b,k}(G0,G1) /\ res.`1{1} = G1.i{2} /\ 0 <= G1.k{2} < q)=> //=.
proc; inline G0(A).main.
swap{2} 1 3; auto.
call (: ={k}(G0,G1)).
+ by sim.
auto=> /> k _ i h1 h2; split => [|_].
+ by rewrite modz_ge0 #smt:(gt0_q).
+ by rewrite ltz_pmod gt0_q.
qed.
