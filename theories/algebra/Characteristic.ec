require import AllCore Ring Int IntDiv.
(*TODO: merge the hakyber proofs, argmin stuff needed.*)
(*---*) import StdOrder.IntOrder IntID.


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
	      
  lemma dvd_char n : char %| n <=> ofint n = zeror.
  proof.      
    split => [/dvdzP [q] ->>|]; [by rewrite -mulrz eq0_ofint_char mulr0|].
    rewrite {1}(divz_eq n char) addrz -mulrz eq0_ofint_char mulr0 add0r.
    move => eq_ofint.
    admit.    
  qed.	      
	      
  lemma dvd2_char (m n : int) : char %| (m - n) <=> ofint m = ofint n.
  proof. by rewrite dvd_char /ofint mulrDz mulrNz subr_eq0. qed.
	      
  lemma char0P : char = 0 <=> injective ofint.
  proof.      
    split => [eq_char_0 x y /dvd2_char|inj_ofint].
    + by rewrite eq_char_0 => /dvd0z /IntID.subr_eq0.
    by move: (dvd2_char char 0); rewrite /= dvdzz /=; apply/inj_ofint.
  qed.	      
	      
end ComRing_Characteristic.
	      
	      
abstract theory IDomain_Characteristic.

  clone import IDomain as ID.

  clone include ComRing_Characteristic with theory CR <- ID.

  lemma char_integral : char = 0 \/ prime char.
  proof.
    case/ler_eqVlt: ge0_char => [-> //|lt0char]; right.
    move/ltzE/ler_eqVlt: lt0char; rewrite /= eq_sym neq1_char /=.
    move => lt1char; split => // y /dvdzP [x] eq_char.
    move: (congr1 ofint _ _ eq_char); rewrite -mulrz eq0_ofint_char eq_sym.
    case/mulf_eq0 => /dvd_char /dvdzP [q ->>]; move/IntID.subr_eq0: eq_char.
    + rewrite mulrAC -{1}(IntID.mul1r char) -mulNr -mulrDl.
      case/IntID.mulf_eq0; [|by move => eq_; move: eq_ lt1char => ->].
      by move/IntID.subr_eq0 => eq1; left; apply/dvdz1/dvdzP; exists q.
    rewrite mulrA -{1}(IntID.mul1r char) -mulNr -mulrDl.
    case/IntID.mulf_eq0; [|by move => eq_; move: eq_ lt1char => ->].
    move/IntID.subr_eq0 => eq1; right; rewrite normrM (ger0_norm char) ?ge0_char //.
    apply/IntID.subr_eq0; rewrite -{2}(IntID.mul1r char) -mulNr -mulrDl.
    by apply/IntID.mulf_eq0; left; apply/IntID.subr_eq0/dvdz1/dvdzP; exists x.
  qed.

  section Frobenius.

    declare axiom prime_char : prime char.

    op frobenius x = ID.exp x char.

    lemma frobenius0 :
      frobenius zeror = zeror.
    proof. by rewrite /frobenius expr0z; move: prime_char => /gt0_prime /gtr_eqF ->. qed.

    lemma frobenius1 :
      frobenius oner = oner.
    proof. by rewrite /frobenius expr1z. qed.

    lemma frobenius_add (x y : t) :
      frobenius (x + y) = frobenius x + frobenius y.
    proof.
      admit.
    qed.

    lemma frobenius_opp (x : t) :
      frobenius (-x) = - frobenius x.
    proof.
      rewrite /frobenius -{1}(mul1r x) -mulNr exprMn ?ge0_char //.
      rewrite -signr_odd ?ge0_char //.
      admit.
    qed.

    lemma frobenius_mul (x y : t) :
      frobenius (x * y) = frobenius x * frobenius y.
    proof.
      admit.
    qed.

    lemma frobenius_invr (x : t) :
      frobenius (invr x) = invr (frobenius x).
    proof.
      admit.
    qed.

    lemma frobenius_unit (x : t) :
      unit x <=> unit (frobenius x).
    proof.
      admit.
    qed.

    lemma bijective_frobenius :
      bijective frobenius.
    proof.
      admit.
    qed.
  
  end section Frobenius.

end IDomain_Characteristic.


abstract theory Field_Characteristic.

  clone import Field as F.

  clone include IDomain_Characteristic with
    theory ID <- F.

end Field_Characteristic.
