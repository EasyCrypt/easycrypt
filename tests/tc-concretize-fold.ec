(* -------------------------------------------------------------------- *)
(* Tests for the "concrete iff reducible" rule applied at every          *)
(* concretization site — apply / exact / rewrite / SMT — when a TC class *)
(* op is instantiated at a [tci_reducible] carrier (here: int).          *)
(* -------------------------------------------------------------------- *)

require import Core Int.
require import TcMonoid TcRing TcInt.

(* -------------------------------------------------------------------- *)
(* Apply a TC class lemma at a concrete reducible carrier (int). The
   proof-term type returned by [LowApply.check] is folded by Phase A,
   so the residual goal after [apply] reduces to reflexivity / a
   concrete-int identity that [done] discharges. *)
lemma test_apply_addrC (x y : int) : x + y = y + x.
proof. apply addrC. qed.

lemma test_apply_addr0 (x : int) : x + 0 = x.
proof. apply addr0. qed.

lemma test_apply_opprK (x : int) : - - x = x.
proof. apply opprK. qed.


(* -------------------------------------------------------------------- *)
(* Rewriting with a TC class lemma at int. Post-rewrite goal carries
   folded core ops thanks to Phase A's [LowApply.check] hook (and the
   [t_rewrite] machinery). *)
lemma test_rewrite_addrC (x y : int) : x + y = y + x.
proof. by rewrite addrC. qed.

lemma test_rewrite_addr0 (x : int) : x + 0 = x.
proof. by rewrite addr0. qed.

lemma test_rewrite_chain (x y z : int) : x + y + z = z + (x + y).
proof. by rewrite addrC. qed.


(* -------------------------------------------------------------------- *)
(* SMT bridges: a polymorphic TC lemma instantiated at [int] in the
   hint list now has a Why3 axiom relating its abstract heads to the
   concrete int realisations. Without bridges these fail with [cannot
   prove goal (strict)] — see TcInt.ec:60 and TcBigalg.ec:289 for the
   full-blown form. *)
lemma test_smt_bridge_mulr2z (x : int) :
  intmul x 2 = x + x.
proof. smt(mulr2z). qed.

lemma test_smt_bridge_mulrNz (x : int) (n : int) :
  intmul x (-n) = -(intmul x n).
proof. smt(mulrNz). qed.

lemma test_smt_bridge_chained (z c : int) :
  intmul z c = Int.( * ) z c.
proof.
have h: forall cp, 0 <= cp => intmul z cp = Int.( * ) z cp.
  elim=> /= [|cp ge0_cp ih]; first by rewrite mulr0z.
  by rewrite mulrS // ih /#.
smt(opprK mulrNz opprK).
qed.


(* -------------------------------------------------------------------- *)
(* Negative side: at an abstract carrier the abstract TC heads must be
   preserved (the rule says "concrete iff reducible", and an abstract
   carrier has no reducible instance to fold through). The proof must
   still go through using the algebraic lemmas only — no concrete
   realisation is available. *)
section.
declare type c <: comring.

lemma test_abstract_addrC (x y : c) : x + y = y + x.
proof. apply addrC. qed.

lemma test_abstract_addr0 (x : c) : x + zero = x.
proof. apply addr0. qed.

lemma test_abstract_opprK (x : c) : - - x = x.
proof. apply opprK. qed.

end section.
