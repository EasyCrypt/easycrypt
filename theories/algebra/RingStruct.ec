(* ==================================================================== *)
require import AllCore List Ring Int IntMin IntDiv Bigalg Binomial Finite.
(*---*) import StdOrder.IntOrder IntID.


(* ==================================================================== *)
abstract theory ZModuleStruct.
  type t.

  clone import ZModule as ZMod with
    type t <= t.

  op order (x : t) = argmin idfun (fun n => 0 < n /\ intmul x n = zeror).

  lemma ge0_order x :
    0 <= order x.
  proof. by rewrite/order; apply ge0_argmin. qed.

  lemma intmul_order x :
    intmul x (order x) = zeror.
  proof.
    rewrite /order; pose p:= (fun (n : int) => _ < n /\ _ _ n = _).
    case: (exists i, 0 <= i /\ p (idfun i)) => [[i] [le0i p_i]|].
    + move: (argminP _ _ _ le0i p_i); pose m:= argmin _ _.
      by move: m => m []; rewrite /idfun.
    rewrite negb_exists /= => forall_; rewrite argmin_out ?mulr0z //.
    by move => i le0i; apply/negP => p_i; move: (forall_ i).
  qed.

  lemma dvd_order x n :
    order x %| n <=> intmul x n = zeror.
  proof.
    split => [/dvdzP [q] ->>|]; [by rewrite mulrC mulrM intmul_order mul0i|].
    rewrite {1}(divz_eq n (order x)) mulrDz mulrC mulrM intmul_order mul0i add0r.
    move => eq_intmul; apply/dvdzE; move: eq_intmul; rewrite /order.
    pose p:= (fun (n : int) => _ < n /\ _ _ n = _); move => eq_intmul.
    case: (exists n , 0 < n /\ intmul x n = zeror).
    + move => [i] [lt0i eq0]; move: (mem_range_mod n (argmin idfun p) _).
      - apply/gtr_eqF; move: (argminP idfun p i _); [by apply/ltzW|].
        pose m:= argmin idfun p; move: m => m; rewrite /p /idfun /=.
        by rewrite lt0i eq0 /=; case.
      rewrite ger0_norm ?ge0_argmin //; move/mem_range/argmin_min.
      move: eq_intmul; move: (argminP idfun p i _); [by apply/ltzW|].
      pose m:= argmin idfun p; move: m => m; rewrite /p /idfun /= => {p}.
      rewrite lt0i eq0 /= => -[lt0m _] -> /= /lerNgt /ler_eqVlt [] // /ltrNge.
      by rewrite modz_ge0 //; apply/gtr_eqF.
    move => /negb_exists /= /(_ (`|n %% argmin idfun p|)).
    rewrite normr_gt0; case: (n %% argmin idfun p = 0) => //= _.
    rewrite normE; case: (0 <= n %% argmin idfun p) => _ //.
    by rewrite mulrNz eq_intmul oppr0.
  qed.

  lemma order0 :
    order zeror = 1.
  proof.
    by move: (dvd_order zeror 1); rewrite mul0i /= dvdz1 ger0_norm // ge0_order.
  qed.

  lemma dvd2_order x (m n : int) : order x %| (m - n) <=> intmul x m = intmul x n.
  proof. by rewrite dvd_order mulrDz mulrNz subr_eq0. qed.
	      
  lemma order0P x : order x = 0 <=> injective (intmul x).
  proof.
    split => [eq_order_0 y z /dvd2_order|inj_intmul].
    + by rewrite eq_order_0 => /dvd0z /IntID.subr_eq0.
    by move: (dvd2_order x (order x) 0); rewrite /= dvdzz /=; apply/inj_intmul.
  qed.

  op orbit (x y : t) = exists n , y = intmul x n.

  op orbit_list (x : t) = mkseq (fun n => intmul x n) (order x).

  op eqv_orbit (x y z : t) = orbit x (y - z).

  lemma orbit0 x:
    orbit x zeror.
  proof. by exists 0; rewrite mulr0z. qed.

  lemma orbitD x y z:
    orbit x y =>
    orbit x z =>
    orbit x (y + z).
  proof. by move => [m] ->> [n] ->>; exists (m + n); rewrite mulrDz. qed.

  lemma orbitN x y:
    orbit x y =>
    orbit x (-y).
  proof. by move => [n] ->>; exists (-n); rewrite mulrNz. qed.

  lemma orbitB x y z:
    orbit x y =>
    orbit x z =>
    orbit x (y - z).
  proof. by move => ? ?; apply/orbitD => //; apply/orbitN. qed.

  lemma orbit_listP x y:
    0 < order x =>
    orbit x y <=> (y \in orbit_list x).
  proof.
    rewrite mkseqP; move => lt0ord; split => [[n] ->>|[n] [mem_n_range ->>]]; [|by exists n].
    exists (n %% (order x)); move: (mem_range_mod n (order x) _); rewrite ?gtr_eqF // -mem_range /=.
    by rewrite ger0_norm ?ltzW // => -> /=; apply/dvd2_order; rewrite -divzE; apply/dvdz_mull/dvdzz.
  qed.

  lemma size_orbit_list x:
    size (orbit_list x) = order x.
  proof. by rewrite size_mkseq ler_maxr // ge0_order. qed.

  lemma iota_range m n:
    iota_ m n = range m (m + n).
  proof. by rewrite /range addrAC. qed.

  lemma uniq_orbit_list x:
    uniq (orbit_list x).
  proof.
    apply/map_inj_in_uniq; [|by rewrite iota_range range_uniq].
    move => y z /=; rewrite !iota_range /= => mem_y mem_z /dvd2_order.
    rewrite -(IntID.opprK z) mem_range_opp in mem_z; rewrite -subr_eq0.
    move: (mem_range_add2 _ _ _ _ _ _ mem_y mem_z) => /= {mem_y mem_z} mem_.
    rewrite dvdzP => -[q] eq_; move: eq_ mem_ => ->; case/ler_eqVlt: (ge0_order x) => [<- //|].
    move => gt0_order; rewrite mem_range_mulr // opprD /= divz_small /=.
    + by rewrite -ltzS /= gt0_order /= ltzE /= ler_norm.
    rewrite -(mulN1r (order _)) mulzK /=; [by apply/gtr_eqF|].
    by rewrite rangeS /= => ->.
  qed.

  lemma eqv_orbit_refl x : reflexive (eqv_orbit x).
  proof. by move => y; rewrite /eqv_orbit subrr orbit0. qed.

  lemma eqv_orbit_sym x : symmetric (eqv_orbit x).
  proof. by move => y z; apply/eqboolP; rewrite /eqv_orbit; split => ?; rewrite -opprB orbitN. qed.

  lemma eqv_orbit_trans x : transitive (eqv_orbit x).
  proof. by move => y z t; rewrite /eqv_orbit => orbit1 orbit2; move: (orbitD _ _ _ orbit1 orbit2); rewrite addrA subrK. qed.
end ZModuleStruct.

(* -------------------------------------------------------------------- *)
abstract theory ComRingStruct.
  type t.

  clone import ComRing as CR with
    type t <= t.

  clone include ZModuleStruct with
    type t <- t,
    theory ZMod <- CR.

  op char = order oner.

  lemma ge0_char : 0 <= char.
  proof. by apply/ge0_order. qed.

  lemma neq1_char : char <> 1.
  proof.
    rewrite/char; apply/negP => eq_; move: eq_ (dvd_order oner 1) => ->.
    by rewrite dvdzz mulr1z /= oner_neq0.
  qed.

  lemma ofint_char : ofint char = zeror.
  proof. by rewrite /ofint /char intmul_order. qed.

  lemma dvd_char n : char %| n <=> ofint n = zeror.
  proof. by rewrite /char /ofint dvd_order. qed.

  lemma dvd2_char (m n : int) : char %| (m - n) <=> ofint m = ofint n.
  proof. by rewrite /char /ofint dvd2_order. qed.

  lemma char0P : char = 0 <=> injective ofint.
  proof. by rewrite /char /ofint order0P. qed.

  lemma neq1_order x : order x = 1 <=> x = zeror.
  proof.
    split => [dvd_1|->>]; [|by apply/order0].
    by move: (dvd_order x 1); rewrite mulr1z dvd_1 => <-; rewrite dvdzz.
  qed.

  lemma dvd_order_char x :
    order x %| char.
  proof.
    rewrite dvd_order -(mulr1 x) -mulrzAr.
    by move: ofint_char; rewrite /ofint => ->; rewrite mulr0.
  qed.
end ComRingStruct.
	      
(* -------------------------------------------------------------------- *)	      
abstract theory IDomainStruct.
  type t.

  clone import IDomain as ID with
    type t <= t.

  clone include ComRingStruct with
    type t <- t,
    theory CR <- ID.

  lemma char_integral : char = 0 \/ prime char.
  proof.
    case/ler_eqVlt: ge0_char => [-> //|lt0char]; right.
    move/ltzE/ler_eqVlt: lt0char; rewrite /= eq_sym neq1_char /=.
    move => lt1char; split => // y /dvdzP [x] eq_char.
    move: (congr1 ofint _ _ eq_char); rewrite -mulrz ofint_char eq_sym.
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

  lemma order_integral x :
    order x = if x = zeror then 1 else char.
  proof.
    case: (x = zeror) => [eqx0|neqx0]; [by apply/neq1_order|].
    case: char_integral => [eqchar0|prime_char].
    + case: (order0P x) => _ ->; [|by rewrite eqchar0].
      move => y z; rewrite -!mulr_intr => eq_; move: (mulfI _ neqx0 _ _ eq_).
      by apply/char0P.
    move: (dvd_prime _ _ prime_char (ge0_order x) (dvd_order_char x)).
    by rewrite neq1_order neqx0.
  qed.

  clone import BigComRing as BID with
    theory CR <- ID.

  clone import BinomialCoeffs as Bin with
    theory R <- ID,
    theory BCR <- BID.

  section Frobenius.

    declare axiom prime_char : prime char.

    op frobenius x = ID.exp x char.

    lemma frobenius0 :
      frobenius zeror = zeror.
    proof. by rewrite /frobenius expr0z; move: prime_char => /gt0_prime /gtr_eqF ->. qed.

    lemma frobenius1 :
      frobenius oner = oner.
    proof. by rewrite /frobenius expr1z. qed.

    lemma frobeniusD (x y : t) :
      frobenius (x + y) = frobenius x + frobenius y.
    proof.
      rewrite /frobenius Bin.binomial ?ge0_char // BAdd.big_int_recr ?ge0_char //=.
      rewrite expr0 mulr1 binn ?ge0_char // mulr1z addrC; congr.
      rewrite BAdd.big_ltn ?gt0_prime ?prime_char //= expr0 mul1r bin0 ?ge0_char //.
      rewrite mulr1z addrC eq_sym -subr_eq eq_sym subrr (BAdd.eq_big_seq _ (fun _ => zeror)); last by apply/BAdd.big1_eq.
      move => k mem_k /=; rewrite -mulr_intr; case: (dvd_char (bin char k)) => + _; move => ->; [|by rewrite mulr0].
      by apply/prime_dvd_bin; [apply/prime_char|case/mem_range: mem_k => le1k -> //=; apply/ltzE].
    qed.

    lemma frobeniusN (x : t) :
      frobenius (-x) = - frobenius x.
    proof.
      rewrite /frobenius -{1}(mul1r x) -mulNr exprMn ?ge0_char // -signr_odd ?ge0_char //.
      case: (prime_or_2_odd _ prime_char) => [eq_char|->]; rewrite /b2i ?odd2 ?expr1 ?mulNr ?mul1r //=.
      by rewrite eq_char odd2 /= expr0 mul1r -addr_eq0 -mul1r2z -eq_char ofint_char mulr0.
    qed.

    lemma frobeniusB (x y : t) :
      frobenius (x - y) = frobenius x - frobenius y.
    proof. by rewrite frobeniusD frobeniusN. qed.

    lemma frobeniusM (x y : t) :
      frobenius (x * y) = frobenius x * frobenius y.
    proof. by rewrite /frobenius; apply/exprMn/ge0_char. qed.

    lemma frobeniusV (x : t) :
      frobenius (invr x) = invr (frobenius x).
    proof. by rewrite /frobenius exprV exprN. qed.

    lemma frobenius_unit (x : t) :
      unit x <=> unit (frobenius x).
    proof.
      rewrite /frobenius; split => [|/unitrP [y] eq_]; [by apply/unitrX|apply/unitrP].
      by exists (y * exp x (char - 1)); rewrite -mulrA -exprSr // subr_ge0; apply/ltzW/gt1_prime/prime_char.
    qed.

    lemma eq_frobenius_0 (x : t) :
      frobenius x = zeror <=> x = zeror.
    proof.
      split => [|->>]; [rewrite /frobenius; move/gt0_prime: prime_char|by apply/frobenius0].
      elim: char ge0_char => // n le0n IHn _; case/ler_eqVlt: (le0n) => [<<-/=|lt0n]; [by rewrite expr1|].
      by rewrite exprSr // => /mulf_eq0 [|] //; apply/IHn.
    qed.

    lemma frobenius_inj :
      injective frobenius.
    proof. by move => x y /subr_eq0; rewrite -frobeniusB => /eq_frobenius_0 /subr_eq0. qed.

    lemma iter_frobenius n x :
      0 <= n =>
      iter n frobenius x =
      exp x (char ^ n).
    proof.
      elim: n => [|n le0n IHn]; [by rewrite iter0 // expr0 expr1|].
      by rewrite iterS // IHn exprSr // exprM.
    qed.

    op iter_frobenius_fixed n x =
      iter n frobenius x = x.
  
  end section Frobenius.
end IDomainStruct.

(* -------------------------------------------------------------------- *)
abstract theory FieldStruct.
  type t.

  clone import Field as F
    with type t <= t.

  clone include IDomainStruct with
    type t <- t,
    theory ID <- F.

  (*TODO: polynomial result.*)
  lemma is_finite_iter_frobenius n :
    0 <= n =>
    is_finite (iter_frobenius_fixed n).
  proof.
    admit.
  qed.

  (*TODO: polynomial result.*)
  lemma size_to_seq_iter_frobenius n :
    0 <= n =>
    size (to_seq (iter_frobenius_fixed n)) <= char ^ n.
  proof.
    admit.
  qed.

end FieldStruct.
