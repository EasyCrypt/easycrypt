(* -------------------------------------------------------------------- *)
(* Axioms on the ring structure [0, 1, +, -, *]
 * - 0 != 1
 * - forall x y z, (x + y) + z = x + (y + z)
 * - forall x y, x + y = y + z
 * - forall x, x + 0 = x
 * - forall x, x + (-x) = 0
 * - forall x y z, (x * y) * z = x * (y * z)
 * - forall x, x * 1 = x
 * - forall x y, x * y = y * z
 * - forall x y z, x * (y + z) = x * y + x * z
 *
 * Ring structures must come with an integer exponentation symbol (^)
 * - forall x, x^0 = 1
 * - forall x n, 0 <= n -> x^(n+1) = x * x^n
 *
 * Ring structures must come with an integer embedding (%:R)
 *   (optional for the [int] type)
 * - 0%:R = 0
 * - 1%:R = 1
 * - forall n, 0 <= n -> (n+1)%:R = n%:R + 1
 * - forall n, (-n)%:R = - n%:R
 *
 * If an explicit symbol (-) is given for the subtraction:
 * - forall x y, x - y = x + (-y)
 *
 * Axioms on the field structure [0, 1, +, -, *, ^-1]
 *   (only extra axioms are given)
 * - forall x, x != 0 -> x * x^-1 = 1
 * - forall x n, 0 <= n -> x^(-n) = (x^n)^-1
 *
 * If an explicit symbol (/) is given for the division:
 * - forall x y, x / y = x * y^-1
 *)

(* -------------------------------------------------------------------- *)
require import Int.

(* -------------------------------------------------------------------- *)
theory Requires.
  type domain.

  op rzero : domain.
  op rone  : domain.
  op add   : domain -> domain -> domain.
  op opp   : domain -> domain.
  op mul   : domain -> domain -> domain.
  op expr  : domain -> int -> domain.
  op ofint : int -> domain.
  op sub   : domain -> domain -> domain.
  op inv   : domain -> domain.
  op div   : domain -> domain -> domain.

  axiom nosmt oner_neq0:
    rone <> rzero.

  axiom nosmt addr0:
    forall (x : domain), add x rzero = x.

  axiom nosmt addrA:
    forall (x y z : domain), add (add x y) z = add x (add y z).

  axiom nosmt addrC:
    forall (x y : domain), add x y = add y x.

  axiom nosmt addrN:
    forall (x : domain), add x (opp x) = rzero.

  axiom nosmt mulr1:
    forall (x : domain), mul x rone = x.

  axiom nosmt mulrA:
    forall (x y z : domain), mul (mul x y) z = mul x (mul y z).

  axiom nosmt mulrC:
    forall (x y : domain), mul x y = mul y x.

  axiom nosmt mulrDl:
    forall (x y z: domain), mul x (add y z) = add (mul x y) (mul x z).

  axiom nosmt expr0:
    forall (x : domain), expr x 0 = rone.

  axiom nosmt exprS:
    forall (x : domain) (n : int), 0 <= n =>
      expr x (n+1) = mul x (expr x n).

  axiom nosmt ofint0: ofint 0 = rzero.
  axiom nosmt ofint1: ofint 1 = rone. (* This is e conseq of ofint0, ofintS *)

  axiom nosmt ofintS:
    forall (n : int), 0 <= n => ofint (n+1) = add (ofint n) rone.

  axiom nosmt ofintN:
    forall (n : int), ofint (-n) = opp (ofint n).

  axiom nosmt subrE:
    forall (x y : domain), sub x y = add x (opp y).

  axiom nosmt mulrV:
    forall (x : domain), x <> rzero => mul x (inv x) = rone.

  (* Can be usefull to add x <> 0 *)
  axiom nosmt exprN:
    forall (x : domain) (n : int), 0 <= n => expr x (-n) = inv (expr x n).

  axiom nosmt divrE:
    forall (x y : domain), div x y = mul x (inv y).
end Requires.
