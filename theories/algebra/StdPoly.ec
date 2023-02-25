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

  lemma bigO_pevalXn2 (m n : int) :
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
    deg p <= n + 1 =>
    bigO (fun k => peval (polyXn n) k%r) (fun k => peval p k%r).
  proof.
    move=> lt_; rewrite polyE; pose s:= (fun k => _ _ k%r).
    move: (bigO_sum s predT (fun i k => p.[i] * peval (polyXn i) k%r) (range 0 (deg p)) _).
    + apply/allP => i mem_i; rewrite /predU /predC /predT /(\o) /=.
      move: (bigOM _ _ _ _ (bigOC 1%r p.[i]) (bigO_pevalXn2 n i _)).
      - by apply/le2_mem_range; move: mem_i; apply/mem_range_incl.
      by apply/(eq_bigO_from 0) => m le0m /=; rewrite /s !pevalC.
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
    move=> lt0n; move: (smallo_bigOM _ _ _ _ (smalloXC 1%r) (bigO_pevalXn (n - 1) c _)).
    + by apply/ltzS.
    apply/(eq_smallo_from 0) => m le0m /=; rewrite pevalC !pevalXn /=.
    by rewrite RField.expr1 -ltzS /= lt0n ltzW //= -RField.exprS // -ltzS.
  qed.

  lemma smallo_pevalXn2 (m n : int) (p : poly) :
    0 <= n < m =>
    smallo (fun k => peval (polyXn m) k%r) (fun k => peval (polyXn n) k%r).
  proof.
    move=> [le0n ltnm]; move: (smallo_bigOM _ _ _ _ (smalloXC 1%r) (bigO_pevalXn2 (m - 1) n _)).
    + by split => // _; apply/ltzS.
    apply/(eq_smallo_from 0) => k le0k /=; rewrite pevalC !pevalXn /=.
    rewrite RField.expr1 -ltzS /=; move: (IntOrder.ler_lt_trans _ _ _ le0n ltnm).
    by move=> lt0m; rewrite lt0m ltzW //= -RField.exprS // -ltzS.
  qed.

  lemma smallo_peval_deg (n : int) (p : poly) :
    deg p <= n =>
    smallo (fun k => peval (polyXn n) k%r) (fun k => peval p k%r).
  proof.
    move=> le_n; case/IntOrder.ler_eqVlt: (ge0_deg p) => [|lt0_].
    + move/eq_sym/deg_eq0 => ->>; move: le_n; rewrite deg0 => le0n.
      pose s:= (fun k => _ _ k%r); move: (smallo0 s).
      by apply/(eq_smallo_from 0) => k le0k /=; rewrite pevalC.
    move: (smallo_bigOM _ _ _ _ (smalloXC 1%r) (bigO_peval_deg (n - 1) p le_n)).
    apply/(eq_smallo_from 0) => k le0k /=; rewrite pevalC !pevalXn /=.
    rewrite RField.expr1 -ltzS /=; move: (IntOrder.ltr_le_trans _ _ _ lt0_ le_n).
    by move=> lt0n; rewrite lt0n ltzW //= -RField.exprS // -ltzS.
  qed.

  lemma gt0lc_cnvtopi p :
    1 < deg p =>
    0%r < lc p =>
    convergetopi (fun k => peval p k%r).
  proof.
    move=> lt1_ lt0lc M.
    move: (smallo_peval_deg (deg p - 1) (p - lc p ** polyXn (deg p - 1)) _).
    + apply/deg_leP => [|i /IntOrder.ler_eqVlt [<<-|/ltzE /= le_i]].
      - by apply/ltzW/ltzE/ltzS.
      - rewrite polyDE polyNE polyZE polyXnE /= ltzW //.
        by apply/ltzE/ltzS.
      rewrite polyDE polyNE polyZE polyXnE /= (IntOrder.gtr_eqF i) /=.
      - by apply/ltzE.
      by apply/gedeg_coeff.
    move=> /(_ (lc p / 2%r) _); [by apply/divr_gt0|].
    case=> N le_; exists (max (max 1 (floor (2%r * M / lc p) + 1)) N).
    move=> n /IntOrder.ler_maxrP [/IntOrder.ler_maxrP []].
    move=> /ltzS/IntOrder.ltr_subl_addr /= lt0n.
    move=> /IntOrder.ler_subr_addr /le_fromint le_floor leNn.
    move: (ltr_le_trans _ _ _ (floor_gt (2%r * M / lc p)) le_floor).
    move=> {le_floor}; rewrite fromintB ltr_add2r.
    rewrite ltr_pdivr_mulr // -ltr_pdivl_mull // => lt_.
    apply/(ltr_le_trans _ _ _ lt_) => {lt_}.
    move/(_ _ leNn): le_.
    rewrite pevalB pevalZ pevalXn ltzW /=.
    + by apply/ltzE/ltzS.
    rewrite ltr_norml.
    case=> + _; rewrite ltr_pdivl_mulr.
    + by apply/expr_gt0/lt_fromint.
    move/ltr_subr_addr; rewrite -RField.mulrDl.
    move/ltrW; rewrite (RField.addrC _ (lc p)).
    rewrite -{1}(RField.mulr1 (lc p)) -RField.mulrN -RField.mulrDr.
    apply/ler_trans; rewrite (RField.mulrC n%r) -!RField.mulrA ler_pmul2l //.
    rewrite (RField.mulrC n%r); apply/ler_pmul.
    + by apply/invr_ge0.
    + by apply/le_fromint/ltzW.
    + by apply/(ler_pmul2l 2%r).
    by apply/ler_eexpr; [apply/IntOrder.subr_gt0|apply/le_fromint/IntOrder.subr_ge0/ltzS].
  qed.
end PolyReal.
