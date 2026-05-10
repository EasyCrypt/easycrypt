pragma +implicits.

(* -------------------------------------------------------------------- *)
require import Core.
require import TcMonoid TcRing TcNumber.
require import Real.
require CoreReal.

(* ==================================================================== *)
(* Canonical [real] instance for the [TcMonoid] / [TcRing] hierarchy.
   Mirrors [theories/datatypes/Real.ec:RField] (a [Ring.Field] clone in
   the legacy world). The TC declaration synthesises the comring /
   idomain / addgroup / addmonoid / mulmonoid / monoid ancestors along
   the way so a single [instance field] is enough.                     *)
(* ==================================================================== *)

(* Named wrapper for [real]'s [unit]: the TC instance form requires an
   op-name on the rhs of [op X = …], not an inline lambda. *)
op real_unit (x : real) : bool = x <> 0%r.

(* -------------------------------------------------------------------- *)
instance idomain with real reducible
  op idm   = CoreReal.zero
  op (+)   = CoreReal.add
  op [-]   = CoreReal.opp
  op oner  = CoreReal.one
  op ( * ) = CoreReal.mul
  op invr  = CoreReal.inv
  op unit  = real_unit

  proof addmA      by smt()
  proof addmC      by smt()
  proof add0m      by smt()
  proof addrN      by smt()
  proof oner_neq0  by smt()
  proof mulrA      by smt()
  proof mulrC      by smt()
  proof mul1r      by smt()
  proof mulrDl     by smt()
  proof mulVr      by smt()
  proof unitP      by smt()
  proof unitout    by smt()
  proof mulf_eq0   by smt().

(* -------------------------------------------------------------------- *)
(* Order and field structure on top of [idomain with real]. Mirrors
   [theories/algebra/StdOrder.ec:RealOrder] and the [Number.RealField]
   level of the legacy hierarchy. *)
op real_norm = Real."`|_|".
op real_le   = CoreReal.le.
op real_lt   = CoreReal.lt.
op real_min  = fun (x y : real) => if x <= y then x else y.
op real_max  = fun (x y : real) => if y <= x then x else y.

instance tcrealdomain with real reducible
  op "`|_|" = real_norm
  op (<=)   = real_le
  op (<)    = real_lt
  op minr   = real_min
  op maxr   = real_max

  proof ler_norm_add   by smt()
  proof addr_gt0       by smt()
  proof norm_eq0       by smt()
  proof ger_leVge      by smt()
  proof normrM         by smt()
  proof ler_def        by smt()
  proof ltr_def        by smt()
  proof real_axiom     by smt()
  proof minrE          by smt()
  proof maxrE          by smt().

instance tcrealfield with real reducible
  proof unitfP by smt().
