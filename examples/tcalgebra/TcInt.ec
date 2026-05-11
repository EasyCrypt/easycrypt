pragma +implicits.

(* -------------------------------------------------------------------- *)
require import Core.
require import TcMonoid TcRing.
require import Int.
require CoreInt.

(* ==================================================================== *)
(* Canonical [int] instance for the [TcMonoid] / [TcRing] hierarchy.
   Mirrors [theories/algebra/Ring.ec:IntID].                            *)
(* ==================================================================== *)

(* Named wrappers for [int]'s [unit] / [invr]: the TC instance form
   requires an op-name on the rhs of [op X = …], not an inline lambda. *)
op int_unit (z : int) : bool = z = 1 \/ z = -1.
op int_invr (z : int) : int  = z.

(* -------------------------------------------------------------------- *)
(* Declaring [idomain] synthesises [comring] (and the rest of the
   chain) along the way, so we don't need a separate [instance comring
   with int] — declaring both would create duplicate comring witnesses
   for [int] and break op-name resolution downstream.                  *)
instance idomain with int reducible
  op idm   = 0
  op (+)   = CoreInt.add
  op [-]   = CoreInt.opp
  op oner  = 1
  op ( * ) = CoreInt.mul
  op invr  = int_invr
  op unit  = int_unit

  proof addmA      by smt()
  proof addmC      by smt()
  proof add0m      by smt()
  proof addrN      by smt()
  proof oner_neq0  by smt()
  proof mulrA      by smt()
  proof mulrC      by smt()
  proof mul1r      by smt()
  proof mulrDl     by smt()
  proof mulVr      by smt(@CoreInt)
  proof unitP      by smt()
  proof unitout    by smt()
  proof mulf_eq0   by smt().

op _spacer1 : int = 0.

(* ==================================================================== *)
(* int-specific corollaries that sit on top of the [comring] /
   [idomain] instances. Mirrors the lemmas under [Ring.ec:IntID].       *)
(* ==================================================================== *)

(* int's abstract [intmul] coincides with concrete int multiplication. *)
lemma intmulz (z c : int) : intmul z c = Int.( * ) z c.
proof.
have h: forall cp, 0 <= cp => intmul z cp = Int.( * ) z cp.
  elim=> /= [|cp ge0_cp ih]; first by rewrite mulr0z.
  by rewrite mulrS // ih /#.
smt(opprK mulrNz opprK).
qed.

(* Parity of [exp x n] for [x : int] tracks parity of [x] when [n > 0]. *)
lemma poddX (n x : int) :
  0 < n => odd (exp x n) = odd x.
proof.
rewrite ltz_def => - [] + ge0_n; elim: n ge0_n => // + + _ _.
elim=> [|n ge0_n ih]; first by rewrite expr1.
by rewrite exprS ?addz_ge0 // oddM ih andbb.
qed.

lemma oddX (n x : int) :
  0 <= n => odd (exp x n) = (odd x \/ n = 0).
proof.
rewrite lez_eqVlt; case: (n = 0) => [->// _|+ h].
+ by rewrite expr0 odd1.
+ by case: h => [<-//|] /poddX ->.
qed.
