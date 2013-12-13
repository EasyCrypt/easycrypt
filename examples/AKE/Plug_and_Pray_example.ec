require import Distr.
require import Real.
require import Int.
  import EuclDiv.
require import Pair.
require Plug_and_Pray.

const q : int.
axiom q_pos : q > 0.

module type Orcl = {
  fun query(n : int) : int
}.

module type Adv(O : Orcl) = {
  fun run() : bool {*}
}.

module G0(AF : Adv) = {
  var b : bool
  var k : int
  
  module O = {
    fun query(n : int) : int = {
      var k_ : int;
      k = n;
      return k_;
    }
  }
  
  module A = AF(O)
  
  fun main(x : unit) : unit = {
    k = 0;
    b = A.run();
    (* This is an artificial way to ensure that 0 <= k < q.
       Usually, this would be enforced in the oracle, e.g., 
       by stopping to answer (and increasing the counter)
       after q queries. *)
    k = `|k %% q|;
  }
}.

module G1(AF : Adv) = {
  var b : bool
  var k : int
  var i : int

  module O = {
    fun query(n : int) : int = {
      var k_ : int;
      k = n;
      return k_;
    }
  }
  
  module A = AF(O)
  
  fun main(x : unit) : unit = {
    i = $(Distr.Dinter.dinter 0 (q -1));
    k = 0;
    b = A.run();
    k = `|k %% q|;
  }
}.

clone import Plug_and_Pray as PnP with
  type tres <- unit, type tin <- unit, op bound <- q.

(*
   We first apply the general Lemma that yields
     1 / q * Pr[ G0 : Ev] = Pr[ G0; i=$[0..q-1] : Ev /\ i = G0.k]
   where ``G0; i=$[0..q-1]'' is expressed as an application of the
   ``Guess'' functor and we use an if-then-else to ensure that
   G0.k is in [0..q-1].
*)
lemma Bound_aux &m (A <: Adv):
    (1%r/q%r) * Pr[ G0(A).main(()) @ &m : G0.b ]
  = Pr[ Guess(G0(A)).main(()) @ &m :  G0.b /\ (fst res) = if G0.k >= 0 && G0.k < q then G0.k else 0 ].
proof.
  print axiom PBound.
  cut := PBound &m (G0(A)) 
           (lambda g u, let (b,k_,g_a_) = g in b)
           (lambda g u, let (b_,k,g_a_) = g in 1)
           tt.
  trivial.
qed.

(*
  We now transfer the previous lemma to G0 and G1 by relating
  Guess(G0) with G1.
*)
lemma Bound &m (A <: Adv{G1,G0}):
    (1%r/q%r) * Pr[ G0(A).main(tt) @ &m : G0.b ]
  = Pr[ G1(A).main(tt) @ &m :  G1.b /\ G1.k = G1.i].
proof.
   rewrite (Bound_aux &m A).
   (* we also prove the postcondition 0 <= G1.k < q *)
   equiv_deno (_ : true ==> G0.b{1} = G1.b{2} /\ fst(res){1} = G1.i{2} /\ G0.k{1} = G1.k{2} /\
                            G1.k{2} >= 0 /\ G1.k{2} < q) => //.
   fun.
   swap {2} 1 3.
   inline G0(A).main.
   rnd.
   sp; wp.
   call (_:true); skip; smt.
   by smt.
qed.
