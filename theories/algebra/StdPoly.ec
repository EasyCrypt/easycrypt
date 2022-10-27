(* ==================================================================== *)
require import AllCore Ring Poly StdOrder.
(*---*) import StdOrder.IntOrder StdOrder.RealOrder.



theory PolyInt.
  clone import Poly.Poly as PrePolyInt with
    type coeff           <- int,
    type IDCoeff.t       <- int,
    pred IDCoeff.unit (z : int) <- (z = 1 \/ z = -1),
    op   IDCoeff.zeror   <- 0,
    op   IDCoeff.oner    <- 1,
    op   IDCoeff.( + )   <- Int.( + ),
    op   IDCoeff.([ - ]) <- Int.([-]),
    op   IDCoeff.( * )   <- Int.( * ),
    op   IDCoeff.invr    <- (fun (z : int) => z),
    op   IDCoeff.intmul  <- IntID.intmul,
    op   IDCoeff.ofint   <- IntID.ofint_id,
    op   IDCoeff.exp     <- IntID.exp,
    op   IDCoeff.lreg    <- IntID.lreg.

  clone include PrePolyInt with
    theory IDCoeff <- IntOrder.Domain.

  clear [PrePolyInt.*].
end PolyInt.


theory PolyReal.
  clone import Poly.Poly as PrePolyReal with
    type coeff           <- real,
    type IDCoeff.t       <- real,
    pred IDCoeff.unit    <- (fun x => x <> 0%r),
    op   IDCoeff.zeror   <- 0%r,
    op   IDCoeff.oner    <- 1%r,
    op   IDCoeff.( + )   <- Real.( + ),
    op   IDCoeff.([ - ]) <- Real.([-]),
    op   IDCoeff.( * )   <- Real.( * ),
    op   IDCoeff.invr    <- Real.inv,
    op   IDCoeff.intmul  <- RField.intmul,
    op   IDCoeff.ofint   <- RField.ofint,
    op   IDCoeff.exp     <- RField.exp,
    op   IDCoeff.lreg    <- RField.lreg.

  clone include PrePolyReal with
    theory IDCoeff <- RealOrder.Domain.

  clear [PrePolyReal.*].

  clone import PolyReal.PrePolyReal.BigCf.BCA.
  clone import PolyReal.PrePolyReal.BigCf.BCM.
  clone import BigPoly.PCA.
  clone import BigPoly.PCM.

  lemma lc_lt0_lim p :
    (0%r < lc p /\ 1 < deg p) <=>
    (forall M , exists x , forall (y : real) , x < y => M < peval p y).
  proof.
    case/IntOrder.ler_eqVlt: (ge0_deg p) => [/eq_sym /deg_eq0 ->>|].
    + rewrite lc0 deg0 /= negb_forall /=; exists 1%r.
      rewrite negb_exists /= => a; rewrite negb_forall /=.
      by exists (a + 1%r); rewrite peval0 negb_imply ltr_addl -lerNgt ler01 ltr01.
    case/ltzE/IntOrder.ler_eqVlt => /= [/eq_sym /deg_eq1 [c] [neqc0 ->>]|lt1d].
    + rewrite degC neqc0 /= negb_forall /=; exists (c + 1%r).
      rewrite negb_exists /= => a; rewrite negb_forall /=; exists (a + 1%r).
      by rewrite negb_imply ltr_addl ltr01 /= pevalC -lerNgt ler_addl ler01.
    rewrite lt1d /=; move: (lc_eq0 p); rewrite -deg_eq0 IntOrder.gtr_eqF /=.
    + by apply/(IntOrder.ler_lt_trans _ _ _ _ lt1d).
    move/ltr_total => [ltlc0|lt0lc]; [rewrite ltrNge ltrW //=|rewrite lt0lc /=].
    + rewrite negb_forall /=; exists 0%r; rewrite negb_exists /= => a; rewrite negb_forall /=.
      exists (maxr 0%r a + 1%r - BCA.bigi predT (fun k => `|p.[k]|) 0 (deg p - 1) / lc p).
      rewrite negb_imply; split.
      - admit.
      rewrite -lerNgt.
      search _ (_ <= maxr _  _).
      print PCA.big.
      print PCM.big.
      admit.
    move => M.
    admit.
  admitted.
end PolyReal.


print PolyReal.
