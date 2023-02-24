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
  import RealSeq.

  
  lemma bigOC c1 c2 :
    bigO (fun k => peval (polyC c1) k%r) (fun k => peval (polyC c2) k%r).
  proof. by exists `|c2 /c1| 0 => n le1n; rewrite !pevalC. qed.

  lemma bigOXC c :
    bigO (fun k => peval polyX k%r) (fun k => peval (polyC c) k%r).
  proof.
    exists `|c| 1 => n le1n; rewrite pevalC pevalX normrM.
    apply/ler_pimulr; [by apply/normr_ge0|].
    rewrite normrV; [by apply/gtr_eqF/lt_fromint/ltzE|].
    rewrite gtr0_norm; [by apply/lt_fromint/ltzE|].
    by apply/invr_le1; [apply/gtr_eqF/lt_fromint/ltzE|apply/lt_fromint/ltzE|apply/le_fromint].
  qed.

  lemma bigO_pevalXn n c :
    0 <= n =>
    bigO (fun k => peval (polyXn n) k%r) (fun k => peval (polyC c) k%r).
  proof.
    move=> le0n; move: (bigOC 1%r c) => Oc.
    move: (bigO_prod predT (fun _ k => peval polyX k%r) (fun c k => peval (polyC c) k%r) (nseq n 1%r) _).
    + by apply/allP => ? _; rewrite /predT /=; apply/bigOXC.
    move=> OXn; move: (bigOM _ _ _ _ Oc OXn).
    apply/(eq_bigO_from 0) => m le0m /= {Oc OXn}.
    rewrite !pevalC !pevalXn le0n !Bigreal.BRM.big_nseq RField.expr1 /=.
    elim: n le0n => [|n le0n] //=; [by rewrite !iter0 // RField.expr0|].
    by rewrite !iterS //= pevalC => -[-> ?]; rewrite RField.exprS.
  qed.

  lemma bigO_pevalXn2 (m n : int) (p : poly) :
    0 <= n <= m =>
    bigO (fun k => peval (polyXn m) k%r) (fun k => peval (polyXn n) k%r).
  proof.
    case=> le0n lenm; move: (lenm); rewrite -subr_ge0; move=> le0_.
    move: (bigO_id (fun k => peval (polyXn n) k%r) _) (bigO_pevalXn (m - n) 1%r le0_).
    + by exists 1 => k le1k /=; rewrite pevalXn le0n /=; apply/gtr_eqF/expr_gt0/lt_fromint/ltzE.
    move=> O1 O2; move: (bigOM _ _ _ _ O1 O2); apply/(eq_bigO_from 0) => k le0k /= {O1 O2}.
    rewrite !pevalXn pevalC le0n le0_ (IntOrder.ler_trans _ _ _ le0n lenm) /=.
    by rewrite -RField.exprD_nneg //= addrC -addrA.
  qed.

  lemma bigO_peval_deg (n : int) (p : poly) :
    deg p < n =>
    bigO (fun k => peval (polyXn n) k%r) (fun k => peval p k%r).
  proof.
    move=> lt_; rewrite polyE; pose s:= (fun k => _ _ k%r).
    print bigO_sum.
    move: (bigO_sum s predT (fun i k => p.[i] * peval (polyXn i) k%r) (range 0 (deg p)) _).
    + apply/allP => i mem_i; rewrite /predU /predC /predT /(\o) /=.
      admit.
    apply/(eq_bigO_from 0) => m le0m /=; rewrite peval_sum.
    apply/Bigreal.BRA.eq_big_seq => i /= mem_i.
    rewrite pevalZ pevalXn peval_exp; [by move: mem_i; apply/mem_range_le|].
    by rewrite pevalX; have ->//: 0 <= i; move: mem_i; apply/mem_range_le.
  qed.

  lemma smalloXC c :
    smallo (fun k => peval polyX k%r) (fun k => peval (polyC c) k%r).
  proof.
    move=> e lt0e; exists (floor (`|c| / e) + 1) => n.
    rewrite -le_fromint fromintD -ler_subr_addr => le_.
    move: (floor_gt (`|c| / e)) => lt_; move: (ltr_le_trans _ _ _ lt_ le_).
    move=> /ltr_add2r {le_ lt_}; rewrite pevalC pevalX /= normrM => lt_.
    have lt0n: 0%r < n%r by apply/(ler_lt_trans _ _ _ _ lt_)/mulr_ge0; [apply/normr_ge0|apply/invr_ge0/ltrW].
    rewrite normrV; [by apply/gtr_eqF|]; rewrite (gtr0_norm n%r) //.
    by apply/ltr_pdivr_mulr => //; apply/ltr_pdivr_mull.
  qed.

  lemma smallo_pevalXn n c :
    0 < n =>
    smallo (fun k => peval (polyXn n) k%r) (fun k => peval (polyC c) k%r).
  proof.
    move=> lt0n.
    move: (smallo_prod predT (fun _ k => peval polyX k%r) (fun c k => peval (polyC c) k%r) (c :: nseq (n - 1) 1%r) _ _).
    + admit.
    + admit.
    apply/(eq_smallo_from 0) => m le0m /=.
    rewrite !Bigreal.BRM.big_cons /(predT c) !pevalXn pevalC RField.expr1 /=.
    rewrite ltzW //= !Bigreal.BRM.big_nseq; move: lt0n.
    rewrite -(subrK n 1); move: (n - 1) => {n} n /ltzS le0n /=.
    rewrite RField.exprS // pevalC.
    elim: n le0n => [|n le0n] //=; [by rewrite !iter0 // RField.expr0|].
    by rewrite !iterS //= pevalC => -[-> ?]; rewrite RField.exprS.
  qed.

  lemma smallo_pevalXn2 (m n : int) (p : poly) :
    n < m =>
    smallo (fun k => peval (polyXn m) k%r) (fun k => peval (polyXn n) k%r).
  proof.
    admit.
  qed.

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
