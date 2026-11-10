(* -------------------------------------------------------------------- *)
(* The field Z/(2^130 - 5) and the polynomials over it.                 *)
require import AllCore IntDiv.
require ZModP Poly.
require import Poly1305_prime.

clone import ZModP.ZModField as Zp1305 with
  op p <- p1305
  proof prime_p by exact: prime_p1305.

clone import Poly.Poly as P1305 with
  type coeff <- zmod,
  theory IDCoeff <- ZModpField.
