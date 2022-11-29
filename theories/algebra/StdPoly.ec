(* ==================================================================== *)
require import AllCore Ring Poly StdOrder StdBigop List.
(*---*) import StdOrder.IntOrder StdOrder.RealOrder.
(*---*) import StdBigop.Bigint StdBigop.Bigreal.



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
    op   IDCoeff.lreg    <- IntID.lreg

    remove abbrev IDCoeff.(/)

    rename [theory] "BCA" as "BIA"
           [theory] "BCM" as "BIM".

  clone include PrePolyInt with
    theory IDCoeff <- IntOrder.Domain,
    theory BigCf   <- Bigint.

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
    op   IDCoeff.lreg    <- RField.lreg

    rename [theory] "BCA" as "BRA"
           [theory] "BCM" as "BRM".

  clone include PrePolyReal with
    theory IDCoeff <- RealOrder.Domain,
    theory BigCf   <- Bigreal.

  clear [PrePolyReal.*].

  import BigCf.
  import BigPoly.

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
    move/ltr_total => [ltlc0|lt0lc]; [rewrite ltrNge ltrW //=|rewrite lt0lc /= => C].
    + rewrite negb_forall /=; exists 0%r; rewrite negb_exists /= => a; rewrite negb_forall /=.
      pose M:= maxr (maxr 0%r a) (- BRA.bigi predT (fun k => `|p.[k]|) 0 (deg p - 1) / lc p).
      exists (M + 1%r); rewrite negb_imply; split.
      - apply/(ler_lt_trans M); [rewrite /M => {M}|by apply/ltr_addl].
        by apply/ger_maxrP; left; apply/ger_maxrP; right.
      rewrite -lerNgt (peval_extend (deg p)) // -(subrK (deg p) 1) rangeSr.
      - by rewrite subr_ge0 ltzW.
      rewrite Bigreal.BRA.big_rcons {1}/predT /= -ler_subr_addr /=.
      apply/(ler_trans _ _ _ (ler_sum_seq _ _ (fun i => `|p.[i]| * (M + 1%r) ^ i) _ _) _).
      - move=> k mem_k _ /=; rewrite ler_pmul2r ?ler_norm // expr_gt0.
        apply/(ler_lt_trans M); [rewrite /M => {M}|by apply/ltr_addl].
        by apply/ger_maxrP; left; apply/ger_maxrP; left.
      apply/(ler_trans _ _ _ (ler_sum_seq _ _ (fun i => `|p.[i]| * (M + 1%r) ^ (deg p - 2)) _ _) _).
      - move=> k mem_k _ /=; apply/ler_wpmul2l; [by apply/normr_ge0|].
        apply/ler_weexpn2l; [|by apply/le2_mem_range; move: mem_k; apply/mem_range_incl].
        by apply/ler_subl_addr => /=; apply/ger_maxrP; left; apply/ger_maxrP; left.
      rewrite -Bigreal.BRA.mulr_suml -RField.mulNr -(subrK (deg p - 1) 1) RField.exprS /=.
      - by rewrite -ltzS /= subr_gt0.
      rewrite RField.mulrA ler_pmul2r; [apply/expr_gt0|].
      - apply/(ler_lt_trans M); [rewrite /M => {M}|by apply/ltr_addl].
        by apply/ger_maxrP; left; apply/ger_maxrP; left.
      rewrite RField.mulrC -ler_pdivr_mulr ?oppr_gt0 // RField.invrN RField.mulrN.
      by apply/(ler_trans M); [rewrite /M => {M}; apply/ger_maxrP; right|apply/ler_addl].
    pose M:=
      maxr 0%r (- (`|p.[0] - C| + BRA.bigi predT (fun k => `|p.[k]|) 1 (deg p - 1)) / lc p).
    exists M; move=> y; apply/contraLR; rewrite -!lerNgt.
    admit.
  qed.
end PolyReal.
