(* ==================================================================== *)
require import AllCore List Ring Int IntMin IntDiv Bigalg Binomial Finite Poly.
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

  lemma intmul_modz_order x n : intmul x (n %% order x) = intmul x n.
  proof.
    apply/dvd2_order; rewrite -opprB; apply/dvdzN; rewrite -divzE.
    by apply/dvdz_mull/dvdzz.
  qed.
	      
  lemma order0P x : order x = 0 <=> injective (intmul x).
  proof.
    split => [eq_order_0 y z /dvd2_order|inj_intmul].
    + by rewrite eq_order_0 => /dvd0z /IntID.subr_eq0.
    by move: (dvd2_order x (order x) 0); rewrite /= dvdzz /=; apply/inj_intmul.
  qed.

  lemma gt0_order_intmul (x : t) n :
    0 < order x =>
    0 < order (intmul x n).
  proof.
    case/ler_eqVlt: (ge0_order (intmul x n)) => // /eq_sym.
    move => eq_0; move/order0P: eq_0 (eq_0) => inj_ ->.
    move/gtr_eqF; rewrite order0P /= => y z.
    by move => eq_; apply/inj_; rewrite -!mulrM !(mulrC n) !mulrM eq_.
  qed.

  lemma dvd_order_intmul (x : t) n :
    order (intmul x n) %| order x.
  proof. by apply/dvd_order; rewrite -mulrM mulrC mulrM intmul_order mul0i. qed.

  lemma order_intmul (x : t) n :
    0 < order x =>
    order (intmul x n) = (order x) %/ gcd (order x) n.
  proof.
    move => lt0_; apply/(mulIf (gcd (order x) n)).
    + by rewrite gcd_eq0 /= gtr_eqF.
    rewrite divzK ?dvdz_gcdl // mulrC {2}(divz_eq (order x) (order (intmul x n))).
    case: (dvdzE (order (intmul x n)) (order x)) => + _; move => -> /=; [by apply/dvd_order_intmul|].
    congr; apply/eq_sym/gcd_uniq.
    + by rewrite /= gtr_eqF.
    + by apply/divz_ge0; [apply/gt0_order_intmul|apply/ltzW].
    + by apply/dvdz_div; [apply/gtr_eqF/gt0_order_intmul|apply/dvd_order_intmul].
    + apply/dvdzP; exists (n * order (intmul x n) %/ order x).
      apply/(mulIf (order (intmul x n))); [by apply/gtr_eqF/gt0_order_intmul|].
      rewrite -mulrA divzK ?dvd_order_intmul // divzK //.
      by apply/dvd_order; rewrite mulrM intmul_order.
    move => y dvdy_ dvdyn; apply/lez_divRL; [by apply/gt0_order_intmul|].
    rewrite mulrC; case (0 < y) => [lt0y|/lerNgt ley0]; last first.
    + by apply/(ler_trans 0); [apply/mulr_ge0_le0 => //|]; apply/ge0_order.
    apply/lez_divRL => //; rewrite -(ger0_norm (order _)); [by apply/ge0_order|].
    rewrite -(ger0_norm (_ %/ _)); [by apply/divz_ge0 => //; apply/ge0_order|].
    apply/dvdz_le; [apply/gtr_eqF; rewrite ltzE /=; apply/lez_divRL => //=|].
    + rewrite -(ger0_norm y) 1:ltzW // -(ger0_norm (order _)); [by apply/ge0_order|].
      by apply/dvdz_le => //; apply/gtr_eqF.
    by apply/dvd_order; rewrite -mulrM divzpMr // mulrC -divzpMr // mulrM intmul_order mul0i.
  qed.

  lemma order_intmul_coprime (x : t) n :
    0 < order x =>
    coprime (order x) n =>
    order (intmul x n) = order x.
  proof. by move => /order_intmul -> ->; rewrite divz1. qed.

  op orbit (x y : t) = exists n , y = intmul x n.

  op is_generator g = forall x , orbit g x.

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
  proof.
    by move => y z t; rewrite /eqv_orbit => orbit1 orbit2;
    move: (orbitD _ _ _ orbit1 orbit2); rewrite addrA subrK.
  qed.

  pred is_zmod_automorph (f : t -> t) =
    bijective f /\
    f zeror = zeror /\
    morphism_2 f ZMod.(+) ZMod.(+).

  lemma zmod_automorph_idfun :
    is_zmod_automorph idfun.
  proof. by rewrite /is_zmod_automorph bij_idfun /idfun. qed.

  lemma zmod_automorphism_comp f g :
    is_zmod_automorph f =>
    is_zmod_automorph g =>
    is_zmod_automorph (f \o g).
  proof.
    rewrite /is_zmod_automorph /(\o) => |> ?? fD ?-> gD.
    by rewrite bij_comp //=; split => // ??; rewrite gD fD.
  qed.

  lemma zmod_automorph_bij f :
    is_zmod_automorph f =>
    bijective f.
  proof. by case. qed.

  lemma zmod_automorph_inv f :
    is_zmod_automorph f =>
    exists g ,
      cancel f g /\
      is_zmod_automorph g.
  proof.
    rewrite /is_zmod_automorph => |> bijf; move: bijf (bijf) => /bij_inj injf.
    move => /> g canfg cangf f0 fD; exists g; rewrite canfg /=; split; [by exists f; split|].
    by rewrite -{1}f0 canfg /= => x y; apply/injf; rewrite fD !cangf.    
  qed.

  lemma zmod_automorph0 f :
    is_zmod_automorph f =>
    f zeror = zeror.
  proof. by case => _ []. qed.

  lemma zmod_automorphD f x y :
    is_zmod_automorph f =>
    f (x + y)%ZMod = f x + f y.
  proof. by case => _ [_ ->]. qed.

  lemma zmod_automorphN f x :
    is_zmod_automorph f =>
    f (-x)%ZMod = - f x.
  proof. by rewrite -addr_eq0 => -[_ [? <-]]; rewrite addNr. qed.

  lemma zmod_automorphI f (x : t) n :
    is_zmod_automorph f =>
    f (intmul x n) = intmul (f x) n.
  proof.
    move => iszma_f; wlog: x n / 0 <= n => [wlog|].
    + case (0 <= n) => [|/ltrNge /ltzW /oppr_ge0]; [by apply/wlog|].
      by move => /wlog /(_ (-x)); rewrite zmod_automorphN // !mulNrNz.
    elim: n => [|n le0n IHn]; [by rewrite !mulr0z zmod_automorph0|].
    by rewrite !mulrS // zmod_automorphD // IHn.
  qed.
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

  pred is_comring_automorph (f : t -> t) =
    is_zmod_automorph f /\
    f oner = oner /\
    morphism_2 f CR.( * ) CR.( * ).

  lemma comring_zmod_automorph f:
    is_comring_automorph f =>
    is_zmod_automorph f.
  proof. by case. qed.

  lemma comring_automorph_idfun :
    is_comring_automorph idfun.
  proof. by rewrite /is_comring_automorph zmod_automorph_idfun /idfun. qed.

  lemma comring_automorphism_comp f g :
    is_comring_automorph f =>
    is_comring_automorph g =>
    is_comring_automorph (f \o g).
  proof.
    rewrite /is_comring_automorph => |> ? f0 fM ? g0 gM.
    rewrite zmod_automorphism_comp //= /(\o) g0 f0 /= => ??.
    by rewrite gM fM.
  qed.

  lemma comring_automorph_bij f :
    is_comring_automorph f =>
    bijective f.
  proof. by move/comring_zmod_automorph/zmod_automorph_bij. qed.

  lemma comring_automorph_inv f :
    is_comring_automorph f =>
    exists g ,
      cancel f g /\
      is_comring_automorph g.
  proof.
    rewrite /is_comring_automorph /is_zmod_automorph => |> bijf.
    move: bijf (bijf) => /bij_inj injf /> g canfg cangf f0 fD f1 fM; exists g.
    rewrite canfg /=; split; [split; [by exists f; split|]|].
    + by rewrite -{1}f0 canfg /= => x y; apply/injf; rewrite fD !cangf.
    by rewrite -{1}f1 canfg /= => x y; apply/injf; rewrite fM !cangf.  
  qed.

  lemma comring_automorph0 f :
    is_comring_automorph f =>
    f zeror = zeror.
  proof. by move/comring_zmod_automorph/zmod_automorph0. qed.

  lemma comring_automorphD f x y :
    is_comring_automorph f =>
    f (x + y)%CR = f x + f y.
  proof. by move/comring_zmod_automorph/zmod_automorphD => ->. qed.

  lemma comring_automorphN f x :
    is_comring_automorph f =>
    f (-x)%CR = - f x.
  proof. by move/comring_zmod_automorph/zmod_automorphN => ->. qed.

  lemma comring_automorph1 f :
    is_comring_automorph f =>
    f oner = oner.
  proof. by case => _ []. qed.

  lemma comring_automorphM f x y :
    is_comring_automorph f =>
    f (x * y)%CR = f x * f y.
  proof. by case => _ [_ ->]. qed.

  lemma comring_automorphU f x :
    is_comring_automorph f =>
    unit (f x) <=> unit x.
  proof.
    move => iscraf; move: iscraf (iscraf) => /comring_automorph_inv.
    move => [g] [canfg iscrag] [_] [f1 fM]; rewrite !unitrP.
    split => -[y] eq_; [|by exists (f y); rewrite -fM eq_ f1].
    by move: iscrag => [_] [g1 gM]; exists (g y); rewrite -(canfg x) -gM eq_.
  qed.

  lemma comring_automorphV f x :
    is_comring_automorph f =>
    f (invr x) = invr (f x).
  proof.
    move => iscraf; move: (iscraf) => [_] [f1 fM]; case: (unit x) => [ux|Nux].
    + move/(congr1 f): (mulVr _ ux); rewrite fM f1.
      rewrite -(mulVr (f x)); [by apply/comring_automorphU|].
      by apply/mulIr/comring_automorphU.
    by rewrite !unitout // comring_automorphU.
  qed.

  lemma comring_automorphI f (x : t) n :
    is_comring_automorph f =>
    f (intmul x n) = intmul (f x) n.
  proof. by move/comring_zmod_automorph/zmod_automorphI => ->. qed.

  lemma comring_automorphZ f n :
    is_comring_automorph f =>
    f (ofint n) = ofint n.
  proof. by move => iscra_f; rewrite /ofint comring_automorphI // comring_automorph1. qed.

  lemma comring_automorphX_le0 f x n :
    is_comring_automorph f =>
    0 <= n =>
    f (CR.exp x n) = CR.exp (f x) n.
  proof.
    move => iscra_f; elim n => [|n le0n]; [by rewrite !expr0 comring_automorph1|].
    by rewrite !exprS // comring_automorphM // => ->.
  qed.
end ComRingStruct.
	      
(* -------------------------------------------------------------------- *)	      
abstract theory IDomainStruct.
  type t, pt.

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
    move: (prime_dvd _ _ prime_char (ge0_order x)).
    by rewrite dvd_order_char neq1_order neqx0.
  qed.

  clone import BigComRing as BID with
    theory CR <- ID.

  clone import Poly as IDPoly with
    type coeff <= t,
    type poly <= pt,
    theory IDCoeff <- ID.

  op eq_pow_1 n x = ID.exp x n = oner.

  lemma eq_pow_1_poly n :
    0 <= n =>
    eq_pow_1 n = root (polyXn n - poly1).
  proof.
    move => le0n; apply/fun_ext => x; rewrite eqboolP /eq_pow_1.
    by rewrite pevalB pevalXn peval1 le0n /= subr_eq0.
  qed.

  lemma is_finite_eq_pow_1 n :
    0 < n =>
    is_finite (eq_pow_1 n).
  proof.
    move => lt0n; move: (finite_root (polyXn n - poly1) _).
    + by rewrite IDPoly.subr_eq0 eq_polyXn1 gtr_eqF.
    by apply/finite_leq => x; rewrite eq_pow_1_poly // ltzW.
  qed.

  lemma size_to_seq_eq_pow_1 n :
    0 < n =>
    size (to_seq (eq_pow_1 n)) <= n.
  proof.
    move => lt0n; move: (size_roots (polyXn n - poly1) _).
    + by rewrite IDPoly.subr_eq0 eq_polyXn1 gtr_eqF.
    move => le__; apply/(ler_trans (deg (polyXn n - poly1) - 1)); [move: le__; apply/ler_trans|].
    + apply/lerr_eq/perm_eq_size/uniq_perm_eq; [by apply/uniq_to_seq/is_finite_eq_pow_1| |].
      - by apply/uniq_to_seq/is_finite_root; rewrite IDPoly.subr_eq0 eq_polyXn1 gtr_eqF.
      move => x; rewrite !mem_to_seq /=; [by apply/is_finite_eq_pow_1| |].
      - by apply/finite_root; rewrite IDPoly.subr_eq0 eq_polyXn1 gtr_eqF.
      by rewrite eq_pow_1_poly //; apply/ltzW.
    apply/ler_subl_addr; apply/(ler_trans _ _ _ (degB (polyXn n) poly1)).
    rewrite degXn deg1; apply/ler_maxrP; rewrite -(ler_subl_addr 1 1 n) /= (ltzW 0) //=.
    by apply/ler_maxrP => /=; apply/addr_ge0 => //; apply/ltzW.
  qed.

  clone import BinomialCoeffs as Bin with
    theory R <- ID,
    theory BCR <- BID.

  op frobenius x = ID.exp x char.

  lemma frobenius0 :
    prime char =>
    frobenius zeror = zeror.
  proof. by rewrite /frobenius expr0z => /gt0_prime /gtr_eqF ->. qed.

  lemma frobenius1 :
    frobenius oner = oner.
  proof. by rewrite /frobenius expr1z. qed.

  lemma frobeniusD (x y : t) :
    prime char =>
    frobenius (x + y) = frobenius x + frobenius y.
  proof.
    move => prime_char; rewrite /frobenius Bin.binomial ?ge0_char //.
    rewrite BAdd.big_int_recr ?ge0_char //= expr0 mulr1 binn ?ge0_char // mulr1z addrC; congr.
    rewrite BAdd.big_ltn ?gt0_prime ?prime_char //= expr0 mul1r bin0 ?ge0_char //.
    rewrite mulr1z addrC eq_sym -subr_eq eq_sym subrr (BAdd.eq_big_seq _ (fun _ => zeror)); last by apply/BAdd.big1_eq.
    move => k mem_k /=; rewrite -mulr_intr; case: (dvd_char (bin char k)) => + _; move => ->; [|by rewrite mulr0].
    by apply/prime_dvd_bin; [apply/prime_char|case/mem_range: mem_k => le1k -> //=; apply/ltzE].
  qed.

  lemma frobeniusN (x : t) :
    prime char =>
    frobenius (-x) = - frobenius x.
  proof. by move => prime_char; rewrite -addr_eq0 -frobeniusD // addNr frobenius0. qed.

  lemma frobeniusB (x y : t) :
    prime char =>
    frobenius (x - y) = frobenius x - frobenius y.
  proof. by move => prime_char; rewrite frobeniusD // frobeniusN. qed.

  lemma frobeniusM (x y : t) :
    frobenius (x * y) = frobenius x * frobenius y.
  proof. by rewrite /frobenius; apply/exprMn/ge0_char. qed.

  lemma frobeniusV (x : t) :
    frobenius (invr x) = invr (frobenius x).
  proof. by rewrite /frobenius exprV exprN. qed.

  lemma frobenius_unit (x : t) :
    prime char =>
    unit x <=> unit (frobenius x).
  proof.
    move => prime_char; rewrite /frobenius; split => [|/unitrP [y] eq_]; [by apply/unitrX|apply/unitrP].
    by exists (y * exp x (char - 1)); rewrite -mulrA -exprSr // subr_ge0; apply/ltzW/gt1_prime/prime_char.
  qed.

  lemma eq_frobenius_0 (x : t) :
    prime char =>
    frobenius x = zeror <=> x = zeror.
  proof.
    move => prime_char; split => [|->>]; [|by apply/frobenius0].
    rewrite /frobenius; move/gt0_prime: prime_char.
    elim: char ge0_char => // n le0n IHn _.
    case/ler_eqVlt: (le0n) => [<<-/=|lt0n]; [by rewrite expr1|].
    by rewrite exprSr // => /mulf_eq0 [|] //; apply/IHn.
  qed.

  lemma frobenius_inj :
    prime char =>
    injective frobenius.
  proof.
    move => prime_char x y /subr_eq0.
    by rewrite -frobeniusB // eq_frobenius_0 // => /subr_eq0.
  qed.

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

  lemma frobenius_polyXchar x :
    frobenius x = peval (polyXn char) x.
  proof. by rewrite pevalXn ge0_char. qed.

  lemma iter_frobenius_fixed_poly n :
    0 <= n =>
    iter_frobenius_fixed n = root (polyXn (char ^ n) - X).
  proof.
    move => le0n; apply/fun_ext => x; rewrite eqboolP /iter_frobenius_fixed iter_frobenius //.
    by rewrite pevalB pevalXn pevalX expr_ge0 ?ge0_char //= subr_eq0.
  qed.

  lemma eq_poly_iter_frobenius_fixed_eq_pow_1 n :
    0 < n =>
    polyXn n - X = X * (polyXn (n - 1) - poly1).
  proof.
    move => lt0n; rewrite -{1}(IDPoly.mulr1 X) -{1}(IntID.subrK n 1).
    move: (polyMXXn (n - 1)); rewrite -ltzS lt0n /= => <-.
    by rewrite -IDPoly.mulrN -IDPoly.mulrDr.
  qed.

  lemma is_finite_iter_frobenius n :
    prime char =>
    0 < n =>
    is_finite (iter_frobenius_fixed n).
  proof.
    move => prime_char lt0n; move: (finite_root (polyXn (char ^ n) - X) _).
    + rewrite IDPoly.subr_eq0 eq_polyXnX gtr_eqF //.
      apply/(ltr_le_trans char); [by apply/gt1_prime|].
      rewrite -{1}(expr1) ler_weexpn2l /=; [by apply/ltzW/gt1_prime|].
      by move/ltzE: lt0n.
    by apply/finite_leq => x; rewrite iter_frobenius_fixed_poly // ltzW.
  qed.

  lemma size_to_seq_iter_frobenius n :
    prime char =>
    0 < n =>
    size (to_seq (iter_frobenius_fixed n)) <= char ^ n.
  proof.
    move => prime_char lt0n; rewrite iter_frobenius_fixed_poly; [by apply/ltzW|].
    rewrite eq_poly_iter_frobenius_fixed_eq_pow_1.
    + by apply/expr_gt0/gt0_prime.
    apply/(ler_trans _ _ _ (size_rootsM _ _ _ _)).
    + by rewrite eq_polyXn0.
    + rewrite IDPoly.subr_eq0 eq_polyXn1 gtr_eqF //.
      apply/subr_gt0/(ltr_le_trans char); [by apply/gt1_prime|].
      rewrite -{1}expr1; apply/ler_weexpn2l => /=; [|by move: lt0n; rewrite ltzE].
      by move: (gt0_prime _ prime_char); rewrite ltzE.
    rewrite size_rootsX -ler_subr_addl -eq_pow_1_poly.
    + by apply/ltzS => /=; apply/expr_gt0/gt0_prime.
    apply/size_to_seq_eq_pow_1/subr_gt0/(ltr_le_trans char); [by apply/gt1_prime|].
    rewrite -{1}expr1; apply/ler_weexpn2l => /=; [|by move: lt0n; rewrite ltzE].
    by move: (gt0_prime _ prime_char); rewrite ltzE.
  qed.
end IDomainStruct.

(* -------------------------------------------------------------------- *)
abstract theory FieldStruct.
  type t.

  clone import Field as F
    with type t <= t.

  clone include IDomainStruct with
    type t <- t,
    theory ID <- F.

  lemma comring_automorphX f x n :
    is_comring_automorph f =>
    f (F.exp x n) = F.exp (f x) n.
  proof.
    move => iscra_f; wlog: x n / 0 <= n => [wlog|]; [|by apply/comring_automorphX_le0].
    case (0 <= n) => [|/ltrNge /ltzW /oppr_ge0]; [by apply/wlog|].
    by move => /wlog /(_ (invr x)); rewrite comring_automorphV // !exprV.
  qed.
end FieldStruct.
