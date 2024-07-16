(* -------------------------------------------------------------------- *)
(* Axioms on the ring structure [0, 1, +, -, *]
 * - 0 != 1
 * - forall x y z, x + (y + z) = (x + y) + z
 * - forall x y, x + y = y + z
 * - forall x, x + 0 = x
 * - forall x, x + (-x) = 0
 * - forall x y z, x * (y * z) = (x * y) * z
 * - forall x, x * 1 = x
 * - forall x y, x * y = y * z
 * - forall x y z, (x + y) * z = x * z + y * z
 *
 * Ring structures must come with an integer exponentation symbol (^)
 * - forall x, x^0 = 1
 * - forall x n, 0 <= n -> x^(n+1) = x * x^n
 *
 * Ring structures must come with an integer embedding (%:R)
 *   (optional for the [int] type)
 * - 0%:R = 0
 * - 1%:R = 1
 * - forall n, 0 <= n -> (n+1)%:R = 1 + n%:R
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
 *
 * If [Cn] is given:
 * - Cn%:R = 0
 *
 * If [Cp] is given:
 * - forall x, x^Cp = x
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

  axiom oner_neq0:
    rone <> rzero.

  axiom addr0:
    forall (x : domain), add x rzero = x.

  axiom addrA:
    forall (x y z : domain), add x (add y z) = add (add x y) z.

  axiom addrC:
    forall (x y : domain), add x y = add y x.

  axiom addrN:
    forall (x : domain), add x (opp x) = rzero.

  (* For boolean ring *)
  axiom addrK:
    forall (x : domain), add x x = rzero.

  axiom oppr_id:
    forall (x : domain), opp x = x.

  axiom mulr1:
    forall (x : domain), mul x rone = x.

  axiom mulrA:
    forall (x y z : domain), mul x (mul y z) = mul (mul x y) z.

  axiom mulrC:
    forall (x y : domain), mul x y = mul y x.

  axiom mulrDl:
    forall (x y z: domain), mul (add x y) z = add (mul x z) (mul y z).

  (* For boolean ring *)
  axiom mulrK:
    forall (x:domain), mul x x = x.

  axiom expr0:
    forall (x : domain), expr x 0 = rone.

  axiom exprS:
    forall (x : domain) (n : int), 0 <= n =>
      expr x (n+1) = mul x (expr x n).

  axiom ofint0: ofint 0 = rzero.
  axiom ofint1: ofint 1 = rone. (* This is a consequence of ofint0, ofintS *)

  axiom ofintS:
    forall (n : int), 0 <= n => ofint (n+1) = add rone (ofint n).

  axiom ofintN:
    forall (n : int), ofint (-n) = opp (ofint n).

  axiom subrE:
    forall (x y : domain), sub x y = add x (opp y).

  axiom mulrV:
    forall (x : domain), x <> rzero => mul x (inv x) = rone.

  axiom exprN:
    forall (x : domain) (n : int), 0 <= n => expr x (-n) = inv (expr x n).

  axiom divrE:
    forall (x y : domain), div x y = mul x (inv y).

  op Cn : int.

  axiom Cn_eq0: ofint Cn = rzero.

  op Cp : int.

  axiom Cp_idp:
    forall (x : domain), expr x Cp = x.

end Requires.
