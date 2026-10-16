(* -------------------------------------------------------------------- *)
open EcParsetree
open EcCoreGoal.FApi
open EcMatching.Position
open EcAst

(* ==================================================================== *)
(* Rules (trusted)                                                      *)

type bdhoare_seq_rule = {
  bsr_at  : codegap1;   (* split position k *)
  bsr_phi : ss_inv;     (* invariant phi established by the prefix *)
  bsr_r   : ss_inv;     (* event R splitting the prefix *)
  bsr_f1  : ss_inv;     (* bound for reaching R with the prefix *)
  bsr_f2  : ss_inv;     (* bound for the suffix, from phi /\ R *)
  bsr_g1  : ss_inv;     (* bound for reaching !R with the prefix *)
  bsr_g2  : ss_inv;     (* bound for the suffix, from phi /\ !R *)
}

(* [t_bdhoare_seq { bsr_at = k; bsr_phi = phi; bsr_r = R;
                    bsr_f1 = f1; bsr_f2 = f2; bsr_g1 = g1; bsr_g2 = g2 }]
   — sequence, splitting on the event [R]. With [c = c1; c2],
   [c1 = c[0..k)], and [~] the goal's comparison ([<=], [=] or [>=]):

     (H)  hoare  [c1 : P ==> phi]
     (F1) phoare [c1 : P ==> R]              ~ f1
     (F2) phoare [c2 : phi /\ R ==> Q]       ~ f2
     (G1) phoare [c1 : P ==> !R]             ~ g1
     (G2) phoare [c2 : phi /\ !R ==> Q]      ~ g2
     (B)  forall &m, P => (f1 * f2 + g1 * g2) ~ d
     (N)  forall r1 r2, hoare [c1 : P /\ f2 = r1 /\ g2 = r2 ==> f2 = r1 /\ g2 = r2]
     ------------------------------------------------------------------------
                          phoare [c : P ==> Q] ~ d

   (N) states that the prefix does not change the suffix bounds. Of the pair
   (F1, F2), only (F1) is kept when [f1] is syntactically [0%r], only (F2)
   when [f2] is; likewise for (G1, G2) with [g1], [g2]. Premises, in order:
   (H), the kept F's, the kept G's, (B), (N).

   Node: [RBdHoareSeq { bsn_at = k (resolved index); bsn_phi; bsn_r; bsn_f1;
                        bsn_f2; bsn_g1; bsn_g2 }].
   Checker: "bdhoare-seq". *)
val t_bdhoare_seq : bdhoare_seq_rule -> backward

(* ==================================================================== *)
(* Derived tactics                                                      *)

(* [t_bdhoare_seq_full r] — [t_bdhoare_seq r], then a best-effort discharge
   of (N): introduce [r1 r2], apply the framed consequence
   [EcPhlConseq.t_hoareS_conseq_nm] (the frame rule
   [EcHoareFrame.t_hoareS_frame], then the consequence rule) down to [hoare [c1 : _ ==> true]], and
   close everything with [EcPhlAuto.t_pl_trivial] — which succeeds when [c1]
   does not write the variables of [f2] / [g2]. Otherwise (N) is left open
   unchanged. Emits no node of its own. *)
val t_bdhoare_seq_full : bdhoare_seq_rule -> backward

(* ==================================================================== *)
(* Elaboration                                                          *)

(* [seq k : R [bound info]] on a [bdHoareS] goal: no side, single position
   and event. The optional bound information gives [phi] and the bounds:
   - none:           phi = true, f1 = d, f2 = 1, g1 = 0, g2 = 1;
   - a single [f]:   phi = true, f1 = d / f, f2 = f, g1 = 0, g2 = 1;
   - [phi f1 f2 g1 g2] (each optional, [_] for a bound defaulting to 1 when
     the other one of its pair is given as 0).
   Applies [t_bdhoare_seq_full]. *)
val process_bdhoare_seq : seq_info -> backward
