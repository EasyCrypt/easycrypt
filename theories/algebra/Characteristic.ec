require import AllCore Ring Int IntDiv.
(*TODO: merge the hakyber proofs, argmin stuff needed.*)


abstract theory ComRing_Characteristic.

  clone import ComRing as CR.

  op char = argmin idfun (fun n => 0 < n /\ ofint n = zeror).

  lemma ge0_char : 0 <= char.
  proof. by rewrite/char; apply ge0_argmin. qed.

  lemma neq1_char : char <> 1.
  proof.
    admit.
  qed.

  lemma eq0_ofint_char : ofint char = zeror.
  proof.
    admit.
  qed.

  (*TODO: should be in ZModule if all was good.*)
  lemma mulrM (x : t) (m n : int) : intmul x (m * n) = intmul (intmul x m) n.
  proof.
    wlog: m n / 0 <= n => [wlog|].
    + case (0 <= n); [by apply/wlog|].
      rewrite -ltzNge => gt0_n.
      move: wlog => /(_ (-m) (-n) _).
      - by rewrite oppz_ge0; apply/ltzW.
      by rewrite mulrNN !mulrNz mulNrz opprK.
    elim: n => //= [|n le0n]; [by rewrite !mulr0z|].
    by rewrite mulrDr /= mulrSz mulrDz addrC => ->.
  qed.

  (*TODO: and this should be in ComRing. Also I have the feeling I already did that somewhere.*)
  lemma mulr_int m n : ofint m * ofint n = ofint (m * n).
  proof. by rewrite mulr_intr /ofint mulrM. qed.

  lemma dvd_char n : char %| n <=> ofint n = zeror.
  proof.
    split => [/dvdzP [q] ->>|].
    + by rewrite -mulr_int eq0_ofint_char mulr0.
    admit.
  qed.

  lemma dvd2_char (m n : int) : char %| (m - n) <=> ofint m = ofint n.
  proof. by rewrite dvd_char /ofint mulrDz mulrNz subr_eq0. qed.

end ComRing_Characteristic.


abstract theory IDomain_Characteristic.

  clone import IDomain as ID.

  clone include ComRing_Characteristic with theory CR <- ID.

  lemma char_integral : char = 0 \/ prime char.
  proof.
    admit.
  qed.

end IDomain_Characteristic.


abstract theory Field_Characteristic.

  clone import Field as F.

  (*TODO: I am bad at clones, check.*)
  clone include IDomain_Characteristic with
    (*theory ID <- F *)
    type ID.t <- F.t,
    op ID.zeror <- F.zeror,
    op ID.oner <- F.oner,
    op ID.(+) <- F.(+),
    op ID.([-]) <- F.([-]),
    op ID.( * ) <- F.( * ),
    op ID.invr <- F.invr,
    pred ID.unit <- (fun x => x <> F.zeror)
  proof *.

  realize ID.addrA by exact F.addrA.
  realize ID.addrC by exact F.addrC.
  realize ID.add0r by exact F.add0r.
  realize ID.addNr by exact F.addNr.
  realize ID.oner_neq0 by exact F.oner_neq0.
  realize ID.mulrA by exact F.mulrA.
  realize ID.mulrC by exact F.mulrC.
  realize ID.mul1r by exact F.mul1r.
  realize ID.mulrDl by exact F.mulrDl.
  realize ID.mulVr by exact F.mulVr.
  realize ID.unitP by exact F.unitP.
  realize ID.unitout by exact F.unitout.
  realize ID.mulf_eq0 by exact F.mulf_eq0.

end Field_Characteristic.
