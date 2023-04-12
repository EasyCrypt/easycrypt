(* ==================================================================== *)
require import AllCore List Ring Int IntMin IntDiv Bigalg Binomial Finite Poly.
(*---*) import StdOrder.IntOrder IntID.



(* ==================================================================== *)
abstract theory ZModuleStruct.
  type t.

  clone import ZModule as RL with
    type t <= t.

  theory ZModStr.
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
      case: (dvdzE (order (intmul x n)) (order x)) => + _; move => -> /=.
      + by apply/dvd_order_intmul.
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

    lemma orbit_refl x:
      orbit x x.
    proof. by exists 1; rewrite mulr1z. qed.

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

    lemma orbitMz x y n:
      orbit x y =>
      orbit x (intmul y n).
    proof. by move => [m] ->>; rewrite -mulrM; exists (m * n). qed.

    lemma orbit_listP x y:
      0 < order x =>
      orbit x y <=> (y \in orbit_list x).
    proof.
      rewrite mkseqP; move => lt0ord; split => [|[n] [mem_n_range ->>]]; [|by exists n].
      case=> n ->>; exists (n %% (order x)); move: (mem_range_mod n (order x) _).
      + by rewrite gtr_eqF.
      rewrite -mem_range /= ger0_norm ?ltzW // => -> /=.
      by apply/dvd2_order; rewrite -divzE; apply/dvdz_mull/dvdzz.
    qed.

    lemma size_orbit_list x:
      size (orbit_list x) = order x.
    proof. by rewrite size_mkseq ler_maxr // ge0_order. qed.

    lemma orbit_list_nil x:
      order x = 0 <=> orbit_list x = [].
    proof. by rewrite -size_orbit_list size_eq0. qed.

    lemma uniq_orbit_list x:
      uniq (orbit_list x).
    proof.
      apply/map_inj_in_uniq; [|by rewrite range_iota range_uniq].
      move => y z /=; rewrite !range_iota /= => mem_y mem_z /dvd2_order.
      rewrite -(IntID.opprK z) mem_range_opp in mem_z; rewrite -subr_eq0.
      move: (mem_range_add2 _ _ _ _ _ _ mem_y mem_z) => /= {mem_y mem_z} mem_.
      rewrite dvdzP => -[q] eq_; move: eq_ mem_ => ->; case/ler_eqVlt: (ge0_order x) => [<- //|].
      move => gt0_order; rewrite mem_range_mulr // opprD /= divz_small /=.
      + by rewrite -ltzS /= gt0_order /= ltzE /= ler_norm.
      rewrite -(mulN1r (order _)) mulzK /=; [by apply/gtr_eqF|].
      by rewrite rangeS /= => ->.
    qed.

    lemma nth_orbit_list x0 n x:
      nth x0 (orbit_list x) n =
      if n \in range 0 (order x)
      then intmul x n
      else x0.
    proof.
      case: (n \in range 0 (order x)) => [mem_|Nmem_].
      + by rewrite nth_mkseq // -mem_range.
      by rewrite nth_out // -mem_range size_orbit_list.
    qed.

    lemma eqv_orbit_refl x : reflexive (eqv_orbit x).
    proof. by move => y; rewrite /eqv_orbit subrr orbit0. qed.

    lemma eqv_orbit_sym x : symmetric (eqv_orbit x).
    proof.
      by move => y z; apply/eqboolP; rewrite /eqv_orbit; split => ?; rewrite -opprB orbitN.
    qed.

    lemma eqv_orbit_trans x : transitive (eqv_orbit x).
    proof.
      by move => y z t; rewrite /eqv_orbit => orbit1 orbit2;
      move: (orbitD _ _ _ orbit1 orbit2); rewrite addrA subrK.
    qed.

    op subzmod (P : t -> bool) =
      P zeror /\
      (forall x y , P x => P y => P (x + y)) /\
      (forall x , P x => P (-x)).

    lemma subzmodT : subzmod predT.
    proof. by rewrite /predT. qed.

    lemma subzmodI P1 P2 : subzmod P1 => subzmod P2 => subzmod (predI P1 P2).
    proof.
      case=> P10 [] P1D P1N [] P20 [] P2D P2N; do!split => //.
      + by move=> x y; rewrite /predI => /> ? ? ? ?; rewrite P1D // P2D.
      by move=> x; rewrite /predI => /> ? ?; rewrite P1N // P2N.
    qed.

    lemma subzmod_pred10 : subzmod (pred1 zeror).
    proof.
      by rewrite /pred1; do!split => // [? ? ->> ->>| ? ->>]; [rewrite addr0|rewrite oppr0].
    qed.

    lemma subzmod_orbit x : subzmod (orbit x).
    proof. do!split; [by apply/orbit0|apply/orbitD|apply/orbitN]. qed.

    lemma subzmod0 P : subzmod P => P zeror.
    proof. by case. qed.

    lemma subzmodD P : subzmod P => forall x y , P x => P y => P (x + y).
    proof. by case. qed.

    lemma subzmodN P : subzmod P => forall x , P x => P (-x).
    proof. by case. qed.
  
    lemma subzmodB P : subzmod P => forall x y , P x => P y => P (x - y).
    proof. by move=> szmP x y Px Py; apply/subzmodD/subzmodN. qed.

    lemma subzmodMz P : subzmod P => forall x n , P x => P (intmul x n).
    proof.
      move=> szmP x n; wlog: n / 0 <= n => [wlogn|].
      + case (0 <= n) => [|/ltrNge/ltzW/ler_opp2/=] /wlogn // + Px.
        move/(_ Px); rewrite RL.mulrNz => /(subzmodN _ szmP).
        by rewrite opprK.
      elim: n => [|n le0n IHn]; [by rewrite RL.mulr0z subzmod0|].
      by rewrite RL.mulrSz => Px; move/(_ Px): IHn => P_; apply/subzmodD.
    qed.
  
    lemma subzmod_mem_orbit P : subzmod P => forall x y , orbit x y => P x => P y.
    proof. by move=> szmP x y [n] ->>; apply/subzmodMz. qed.
  
    lemma subzmod_mem_orbit_list P : subzmod P => forall x y , y \in orbit_list x => P x => P y.
    proof. by move=> szmP x y /mapP [n] [] _ /= => ->; apply/subzmodMz. qed.
  
    lemma subzmod_eqv_orbit P :
      subzmod P =>
      forall x y z ,
        eqv_orbit x y z =>
        P x =>
        P y <=> P z.
    proof.
      move=> szmP x y z [n] /(congr1 P) + Px; rewrite subzmodMz // eqT => P_; split=> [Py|Pz].
      + by move: (subzmodB _ _ _ _ Py P_); rewrite // opprD addrA opprK subrr add0r.
      by move: (subzmodD _ _ _ _ P_ Pz); rewrite // -addrA addNr addr0.
    qed.

    pred zmod_endo f =
      morphism_0 f zeror zeror /\
      morphism_2 f RL.(+) RL.(+).

    lemma zmod_endo_id :
      zmod_endo idfun.
    proof. by rewrite /zmod_endo /idfun. qed.

    lemma zmod_endo_comp f g :
      zmod_endo f =>
      zmod_endo g =>
      zmod_endo (f \o g).
    proof.
      rewrite /zmod_endo /(\o) => |> f0 fD g0 gD /=; split.
      + by rewrite /morphism_0 g0 f0.
      by move=> ? ?; rewrite gD fD.
    qed.

    lemma zmod_endo_iter f :
      zmod_endo f =>
      forall n ,
        zmod_endo (iter n f).
    proof.
      move=> ef n; case (0 <= n) => [|/ltrNge/ltzW len0]; last first.
      + have ->: iter n f = idfun; [|by apply/zmod_endo_id].
        by apply/fun_ext => x; rewrite iter0.
      elim: n => [|n le0n IHn].
      + have ->: iter 0 f = idfun; [|by apply/zmod_endo_id].
        by apply/fun_ext => x; rewrite iter0.
      have ->: iter (n + 1) f = f \o (iter n f); [|by apply/zmod_endo_comp].
      by apply/fun_ext => x; rewrite iterS.
    qed.

    lemma zmod_endo0 f :
      zmod_endo f =>
      morphism_0 f zeror zeror.
    proof. by case. qed.

    lemma zmod_endoD f :
      zmod_endo f =>
      morphism_2 f RL.(+) RL.(+).
    proof. by case. qed.

    lemma zmod_endoN f :
      zmod_endo f =>
      morphism_1 f RL.([-]) RL.([-]).
    proof. by move=> ef x; rewrite -addr_eq0 -zmod_endoD // addNr zmod_endo0. qed.

    lemma zmod_endoB f :
      zmod_endo f =>
      morphism_2 f RL.( - ) RL.( - ).
    proof. by move=> ef x y; rewrite zmod_endoD // zmod_endoN. qed.

    lemma zmod_endoMz f :
      zmod_endo f =>
      forall (x : t) n , f (intmul x n) = intmul (f x) n.
    proof.
      move => ef x n; wlog: x n / 0 <= n => [wlog|].
      + case (0 <= n) => [|/ltrNge/ltzW/oppr_ge0]; [by apply/wlog|].
        by move => /wlog /(_ (-x)); rewrite zmod_endoN // !mulNrNz.
      elim: n => [|n le0n IHn]; [by rewrite !mulr0z zmod_endo0|].
      by rewrite !mulrS // zmod_endoD // IHn.
    qed.

    lemma zmod_endo_order f :
      zmod_endo f =>
      forall x , order (f x) %| order x.
    proof. by move=> ef x; rewrite dvd_order -zmod_endoMz // intmul_order zmod_endo0. qed.

    lemma zmod_endo_orbit f :
      zmod_endo f =>
      forall x y ,
        orbit x y => orbit (f x) (f y).
    proof.
      move=> ef x y [n] ->>; rewrite zmod_endoMz //.
      by apply/orbitMz/orbit_refl.
    qed.
  
    lemma zmod_endo_orbit_list f :
      zmod_endo f =>
      forall x ,
        0 < order (f x) =>
        flatten (nseq (order x %/ order (f x)) (orbit_list (f x))) = map f (orbit_list x).
    proof.
      move=> ef x lt0__; case/ler_eqVlt: (ge0_order x) => [/eq_sym eq_|lt0_].
      + by move/orbit_list_nil: (eq_) => ->; rewrite eq_ /= nseq0 flatten_nil.
      case/dvdzP: (zmod_endo_order _ ef x) => q eq_; move: (lt0_); rewrite eq_.
      rewrite pmulr_lgt0 // => lt0q; rewrite mulzK; [by apply/gtr_eqF|].
      rewrite /orbit_list eq_; move/ltzW: lt0q => {eq_}.
      elim: q => [|n le0n IHn]; [rewrite /= !mkseq0 /=|].
      + by rewrite nseq0 flatten_nil.
      rewrite nseqSr // -cats1 flatten_cat flatten_seq1.
      rewrite mulrDl /= mkseq_add; [|by apply/ge0_order|].
      + by apply/mulr_ge0 => //; apply/ge0_order.
      rewrite map_cat IHn; congr; [by apply/eq_in_map|].
      rewrite map_mkseq; apply/eq_in_mkseq => i /mem_range memi.
      by rewrite /(\o) /= zmod_endoMz // mulrDz mulrC mulrM intmul_order mul0i add0r.
    qed.
  
    lemma zmod_endo_eqv_orbit f :
      zmod_endo f =>
      forall x y z ,
        eqv_orbit x y z =>
        eqv_orbit (f x) (f y) (f z).
    proof. by move=> ef x y z; rewrite /eqv_orbit -zmod_endoB //; apply/zmod_endo_orbit. qed.

    lemma subzmod_subzmod_zmod_endo f P :
      zmod_endo f =>
      subzmod P =>
      subzmod (P \o f).
    proof.
      move=> ef sP; rewrite /(\o); split; [|split].
      + by rewrite zmod_endo0 // subzmod0.
      + by move=> x y; rewrite zmod_endoD //; apply/subzmodD.
      by move=> x; rewrite zmod_endoN //; apply/subzmodN.
    qed.

    lemma subzmod_zmod_endo_subzmod f P :
      zmod_endo f =>
      subzmod P =>
      subzmod (fun y => exists x , f x = y /\ P x).
    proof.
      move=> ef sP; split; [|split].
      + by exists zeror; rewrite zmod_endo0 // subzmod0.
      + move=> ? ? [x] [] <<- Px [y] [] <<- Py; exists (x + y).
        by rewrite zmod_endoD // subzmodD.
      move=> ? [x] [] <<- Px; exists (-x).
      by rewrite zmod_endoN // subzmodN.
    qed.

    lemma zmod_endo_fixed_subzmod f :
      zmod_endo f =>
      subzmod (fun x => f x = x).
    proof.
      move=> ef; split; [by rewrite zmod_endo0|split].
      + by move=> x y; rewrite zmod_endoD // => -> ->.
      by move=> x; rewrite zmod_endoN // => ->.
    qed.

    pred zmod_mono_endo f =
      injective f /\
      zmod_endo f.

    lemma zmod_mono_endo_inj f :
      zmod_mono_endo f => injective f.
    proof. by case. qed.

    lemma zmod_mono_endo_endo f :
      zmod_mono_endo f => zmod_endo f.
    proof. by case. qed.

    lemma zmod_mono_endo_id :
      zmod_mono_endo idfun<:t>.
    proof. by split; [rewrite inj_idfun<:t>|rewrite zmod_endo_id]. qed.

    lemma zmod_mono_endo_comp f g :
      zmod_mono_endo f =>
      zmod_mono_endo g =>
      zmod_mono_endo (f \o g).
    proof.
      by case=> injf ef [] injg eg; split; [apply/inj_comp|apply/zmod_endo_comp].
    qed.

    lemma zmod_mono_endo_iter f :
      zmod_mono_endo f =>
      forall n ,
        zmod_mono_endo (iter n f).
    proof.
      move=> ef n; case (0 <= n) => [|/ltrNge/ltzW len0]; last first.
      + have ->: iter n f = idfun; [|by apply/zmod_mono_endo_id].
        by apply/fun_ext => x; rewrite iter0.
      elim: n => [|n le0n IHn].
      + have ->: iter 0 f = idfun; [|by apply/zmod_mono_endo_id].
        by apply/fun_ext => x; rewrite iter0.
      have ->: iter (n + 1) f = f \o (iter n f); [|by apply/zmod_mono_endo_comp].
      by apply/fun_ext => x; rewrite iterS.
    qed.

    lemma zmod_mono_endo0 f :
      zmod_mono_endo f =>
      morphism_0 f zeror zeror.
    proof. by move/zmod_mono_endo_endo/zmod_endo0. qed.

    lemma zmod_mono_endoD f :
      zmod_mono_endo f =>
      morphism_2 f RL.(+) RL.(+).
    proof. by move/zmod_mono_endo_endo/zmod_endoD. qed.

    lemma zmod_mono_endoN f :
      zmod_mono_endo f =>
      morphism_1 f RL.([-]) RL.([-]).
    proof. by move/zmod_mono_endo_endo/zmod_endoN. qed.

    lemma zmod_mono_endoB f :
      zmod_mono_endo f =>
      morphism_2 f RL.( - ) RL.( - ).
    proof. by move/zmod_mono_endo_endo/zmod_endoB. qed.

    lemma zmod_mono_endoMz f :
      zmod_mono_endo f =>
      forall (x : t) n , f (intmul x n) = intmul (f x) n.
    proof. by move/zmod_mono_endo_endo/zmod_endoMz. qed.

    lemma zmod_mono_endo_eq0 f :
      zmod_mono_endo f =>
      forall x , f x = zeror <=> x = zeror.
    proof.
      move=> ief x; split=> [|->>]; [|by apply/zmod_mono_endo0].
      by move/zmod_mono_endo_inj/(_ x zeror): (ief); rewrite zmod_mono_endo0.
    qed.

    lemma zmod_mono_endoP0 f :
      zmod_mono_endo f <=>
      ( (forall x , f x = zeror => x = zeror) /\
        zmod_endo f ).
    proof.
      split=> [ief|[eq0 ef]].
      + by split=> [x|]; [rewrite zmod_mono_endo_eq0|apply/zmod_mono_endo_endo].
      by split=> // x y; rewrite -subr_eq0 -zmod_endoB // => /eq0 /subr_eq0.
    qed.

    lemma zmod_mono_endo_order f :
      zmod_mono_endo f =>
      forall x , order (f x) = order x.
    proof.
      move=> ef x; move: (dvdz_anti (order (f x)) (order x) _ _).
      + by apply/zmod_endo_order/zmod_mono_endo_endo.
      + rewrite dvd_order -(zmod_mono_endo_eq0 _ ef) zmod_mono_endoMz //.
        by rewrite intmul_order.
      by rewrite !ger0_norm // ge0_order.
    qed.

    lemma zmod_mono_endo_orbit f :
      zmod_mono_endo f =>
      forall x y ,
        orbit (f x) (f y) = orbit x y.
    proof.
      move=> ef x y; apply/eq_iff; split; [|by apply/zmod_endo_orbit/zmod_mono_endo_endo].
      case=> n; rewrite -zmod_mono_endoMz // => /(zmod_mono_endo_inj _ ef) ->>.
      by apply/orbitMz/orbit_refl.
    qed.
  
    lemma zmod_mono_endo_orbit_list f :
      zmod_mono_endo f =>
      forall x ,
        orbit_list (f x) = map f (orbit_list x).
    proof.
      move=> ef x; case/ler_eqVlt: (ge0_order x) => [/eq_sym eq_|lt0_].
      + move/orbit_list_nil: (eq_) => ->; move: eq_; rewrite -(zmod_mono_endo_order _ ef).
        by move/orbit_list_nil => ->.
      rewrite -zmod_endo_orbit_list ?zmod_mono_endo_endo ?zmod_mono_endo_order //.
      by rewrite divzz gtr_eqF //= b2i1 nseq1 flatten_seq1.
    qed.
  
    lemma zmod_mono_endo_eqv_orbit f :
      zmod_mono_endo f =>
      forall x y z ,
        eqv_orbit (f x) (f y) (f z) =
        eqv_orbit x y z.
    proof. by move=> ef x y z; rewrite /eqv_orbit -zmod_mono_endoB // zmod_mono_endo_orbit. qed.

    lemma subzmod_subzmod_zmod_mono_endo f P :
      zmod_mono_endo f =>
      subzmod P =>
      subzmod (P \o f).
    proof. by move/zmod_mono_endo_endo/subzmod_subzmod_zmod_endo/(_ P). qed.

    lemma subzmod_zmod_mono_endo_subzmod f P :
      zmod_mono_endo f =>
      subzmod P =>
      subzmod (fun y => exists x , f x = y /\ P x).
    proof. by move/zmod_mono_endo_endo/subzmod_zmod_endo_subzmod/(_ P). qed.

    lemma zmod_mono_endo_fixed_subzmod f :
      zmod_mono_endo f =>
      subzmod (fun x => f x = x).
    proof. by move/zmod_mono_endo_endo/zmod_endo_fixed_subzmod. qed.

    pred zmod_auto f =
      surjective f /\
      zmod_mono_endo f.

    lemma zmod_auto_inj f :
      zmod_auto f => injective f.
    proof. by case=> _ /zmod_mono_endo_inj. qed.

    lemma zmod_auto_surj f :
      zmod_auto f => surjective f.
    proof. by case. qed.

    lemma zmod_auto_bij f :
      zmod_auto f => bijective f.
    proof. by move=> af; apply/bij_inj_surj; rewrite zmod_auto_inj // zmod_auto_surj. qed.

    lemma zmod_auto_mono_endo f :
      zmod_auto f => zmod_mono_endo f.
    proof. by case. qed.

    lemma zmod_auto_endo f :
      zmod_auto f => zmod_endo f.
    proof. by move/zmod_auto_mono_endo/zmod_mono_endo_endo. qed.

    lemma zmod_autoP f :
      zmod_auto f <=> (bijective f /\ zmod_endo f).
    proof.
      split=> [af|[/bij_inj_surj [injf surjf] ef]]; split=> //.
      + by apply/zmod_auto_bij.
      by apply/zmod_auto_endo.
    qed.

    lemma zmod_auto_id :
      zmod_auto idfun<:t>.
    proof. by split; [apply/bij_surj; rewrite bij_idfun<:t>|rewrite zmod_mono_endo_id]. qed.

    lemma zmod_auto_comp f g :
      zmod_auto f =>
      zmod_auto g =>
      zmod_auto (f \o g).
    proof.
      case/zmod_autoP=> bijf ef /zmod_autoP [] bijg eg; apply/zmod_autoP.
      by split; [apply/bij_comp|apply/zmod_endo_comp].
    qed.

    lemma zmod_auto_iter f :
      zmod_auto f =>
      forall n ,
        zmod_auto (iter n f).
    proof.
      move=> ef n; case (0 <= n) => [|/ltrNge/ltzW len0]; last first.
      + have ->: iter n f = idfun; [|by apply/zmod_auto_id].
        by apply/fun_ext => x; rewrite iter0.
      elim: n => [|n le0n IHn].
      + have ->: iter 0 f = idfun; [|by apply/zmod_auto_id].
        by apply/fun_ext => x; rewrite iter0.
      have ->: iter (n + 1) f = f \o (iter n f); [|by apply/zmod_auto_comp].
      by apply/fun_ext => x; rewrite iterS.
    qed.

    lemma zmod_auto0 f :
      zmod_auto f =>
      morphism_0 f zeror zeror.
    proof. by move/zmod_auto_mono_endo/zmod_mono_endo0. qed.

    lemma zmod_autoD f :
      zmod_auto f =>
      morphism_2 f RL.(+) RL.(+).
    proof. by move/zmod_auto_mono_endo/zmod_mono_endoD. qed.

    lemma zmod_autoN f :
      zmod_auto f =>
      morphism_1 f RL.([-]) RL.([-]).
    proof. by move/zmod_auto_mono_endo/zmod_mono_endoN. qed.

    lemma zmod_autoB f :
      zmod_auto f =>
      morphism_2 f RL.( - ) RL.( - ).
    proof. by move/zmod_auto_mono_endo/zmod_mono_endoB. qed.

    lemma zmod_autoMz f :
      zmod_auto f =>
      forall (x : t) n , f (intmul x n) = intmul (f x) n.
    proof. by move/zmod_auto_mono_endo/zmod_mono_endoMz. qed.

    lemma zmod_auto_eq0 f :
      zmod_auto f =>
      forall x , f x = zeror <=> x = zeror.
    proof. by move/zmod_auto_mono_endo/zmod_mono_endo_eq0. qed.

    lemma zmod_auto_inv f :
      zmod_auto f =>
      exists g ,
        cancel f g /\
        cancel g f /\
        zmod_auto g.
    proof.
      rewrite zmod_autoP => |> bijf; move: (bijf) => [] g [] canfg cangf ef.
      exists g; rewrite canfg cangf /= zmod_autoP; split; [by exists f; split|].
      split; [by rewrite -{1}(zmod_endo0 f) // /morphism_0 canfg|].
      by move=> x y; apply/(bij_inj _ bijf); rewrite (zmod_endoD _ ef) !cangf.    
    qed.

    lemma zmod_auto_order f :
      zmod_auto f =>
      forall x , order (f x) = order x.
    proof. by move/zmod_auto_mono_endo/zmod_mono_endo_order. qed.

    lemma zmod_auto_orbit f :
      zmod_auto f =>
      forall x y ,
        orbit (f x) (f y) = orbit x y.
    proof. by move/zmod_auto_mono_endo/zmod_mono_endo_orbit. qed.
  
    lemma zmod_auto_orbit_list f :
      zmod_auto f =>
      forall x ,
        orbit_list (f x) = map f (orbit_list x).
    proof. by move/zmod_auto_mono_endo/zmod_mono_endo_orbit_list. qed.
  
    lemma zmod_auto_eqv_orbit f :
      zmod_auto f =>
      forall x y z ,
        eqv_orbit (f x) (f y) (f z) =
        eqv_orbit x y z.
    proof. by move/zmod_auto_mono_endo/zmod_mono_endo_eqv_orbit. qed.

    lemma subzmod_subzmod_zmod_auto f P :
      zmod_auto f =>
      subzmod P =>
      subzmod (P \o f).
    proof. by move/zmod_auto_mono_endo/subzmod_subzmod_zmod_mono_endo/(_ P). qed.

    lemma subzmod_zmod_auto_subzmod f P :
      zmod_auto f =>
      subzmod P =>
      subzmod (fun y => exists x , f x = y /\ P x).
    proof. by move/zmod_auto_mono_endo/subzmod_zmod_mono_endo_subzmod/(_ P). qed.

    lemma zmod_auto_fixed_subzmod f :
      zmod_auto f =>
      subzmod (fun x => f x = x).
    proof. by move/zmod_auto_mono_endo/zmod_mono_endo_fixed_subzmod. qed.
  end ZModStr.
end ZModuleStruct.

(* -------------------------------------------------------------------- *)
abstract theory ComRingStruct.
  type t.

  clone import ComRing as RL with
    type t <= t.

  clone include ZModuleStruct with
    type t    <- t,
    theory RL <- RL
    rename [theory] "RL" as "Gone".

  theory CRStr.
    import ZModStr.
  
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

    op subcr P =
      subzmod P /\
      P oner /\
      (forall x y , P x => P y => P (x * y)).

    lemma subcr_zmod P : subcr P => subzmod P.
    proof. by case. qed.

    lemma subcrT : subcr predT.
    proof. by rewrite /predT. qed.

    lemma subcrI P1 P2 : subcr P1 => subcr P2 => subcr (predI P1 P2).
    proof.
      case=> P1_ [] P11 P1M [] P2_ [] P21 P2M; split; [|split].
      + by apply/subzmodI/subcr_zmod.
      + by split.
      by move=> x y; rewrite /predI => /> ? ? ? ?; rewrite P1M // P2M.
    qed.

    lemma subcr_orbit1 : subcr (orbit oner).
    proof.
      split; [by apply/subzmod_orbit|split; [by apply/orbit_refl|]].
      move=> x y [nx] ->> [ny] ->>; rewrite mulrz.
      by exists (nx * ny).
    qed.

    lemma subcr0 P : subcr P => P zeror.
    proof. by move/subcr_zmod; apply/subzmod0. qed.

    lemma subcrD P : subcr P => forall x y , P x => P y => P (x + y).
    proof. by move/subcr_zmod; apply/subzmodD. qed.

    lemma subcrN P : subcr P => forall x , P x => P (-x).
    proof. by move/subcr_zmod; apply/subzmodN. qed.
  
    lemma subcrB P : subcr P => forall x y , P x => P y => P (x - y).
    proof. by move/subcr_zmod; apply/subzmodB. qed.

    lemma subcrMz P : subcr P => forall x n , P x => P (intmul x n).
    proof. by move/subcr_zmod; apply/subzmodMz. qed.

    lemma subcr_mem_orbit P : subcr P => forall x y , orbit x y => P x => P y.
    proof. by move/subcr_zmod; apply/subzmod_mem_orbit. qed.
  
    lemma subcr_mem_orbit_list P : subcr P => forall x y , y \in orbit_list x => P x => P y.
    proof. by move/subcr_zmod; apply/subzmod_mem_orbit_list. qed.
  
    lemma subcr_eqv_orbit P :
      subcr P =>
      forall x y z ,
        eqv_orbit x y z =>
        P x =>
        P y <=> P z.
    proof. by move/subcr_zmod; apply/subzmod_eqv_orbit. qed.

    lemma subcr1 P : subcr P => P oner.
    proof. by case. qed.
  
    lemma subcrM P : subcr P => forall x y , P x => P y => P (x * y).
    proof. by case. qed.

    lemma subcrZ P n : subcr P => P (ofint n).
    proof. by move=> subcrP; apply/subcrMz/subcr1. qed.

    lemma subcrXR P : subcr P => forall x n , P x => 0 <= n => P (exp x n).
    proof.
      move=> subcrP x n Px; elim: n => [|n le0n IHn]; [by rewrite RL.expr0 subcr1|].
      by rewrite RL.exprS //; apply/subcrM.
    qed.

    pred cr_endo f =
      zmod_endo f /\
      morphism_0 f oner oner /\
      morphism_2 f RL.( * ) RL.( * ).

    lemma cr_endo_zmod f :
      cr_endo f => zmod_endo f.
    proof. by case. qed.

    lemma cr_endo_id :
      cr_endo idfun.
    proof. by rewrite /cr_endo /idfun. qed.

    lemma cr_endo_comp f g :
      cr_endo f =>
      cr_endo g =>
      cr_endo (f \o g).
    proof.
      case=> ef [] f1 fM [] eg [] g1 gM; split; [by apply/zmod_endo_comp|].
      by rewrite /(\o) /morphism_0 /= g1 f1 /= => x y; rewrite gM fM.
    qed.

    lemma cr_endo_iter f :
      cr_endo f =>
      forall n ,
        cr_endo (iter n f).
    proof.
      move=> ef n; case (0 <= n) => [|/ltrNge/ltzW len0]; last first.
      + have ->: iter n f = idfun; [|by apply/cr_endo_id].
        by apply/fun_ext => x; rewrite iter0.
      elim: n => [|n le0n IHn].
      + have ->: iter 0 f = idfun; [|by apply/cr_endo_id].
        by apply/fun_ext => x; rewrite iter0.
      have ->: iter (n + 1) f = f \o (iter n f); [|by apply/cr_endo_comp].
      by apply/fun_ext => x; rewrite iterS.
    qed.

    lemma cr_endo0 f :
      cr_endo f =>
      morphism_0 f zeror zeror.
    proof. by move/cr_endo_zmod/zmod_endo0. qed.

    lemma cr_endoD f :
      cr_endo f =>
      morphism_2 f RL.(+) RL.(+).
    proof. by move/cr_endo_zmod/zmod_endoD. qed.

    lemma cr_endoN f :
      cr_endo f =>
      morphism_1 f RL.([-]) RL.([-]).
    proof. by move/cr_endo_zmod/zmod_endoN. qed.

    lemma cr_endoB f :
      cr_endo f =>
      morphism_2 f RL.( - ) RL.( - ).
    proof. by move/cr_endo_zmod/zmod_endoB. qed.

    lemma cr_endoMz f :
      cr_endo f =>
      forall (x : t) n , f (intmul x n) = intmul (f x) n.
    proof. by move/cr_endo_zmod/zmod_endoMz. qed.

    lemma cr_endo1 f :
      cr_endo f =>
      morphism_0 f oner oner.
    proof. by case => _ []. qed.
  
    lemma cr_endoM f :
      cr_endo f =>
      morphism_2 f RL.( * ) RL.( * ).
    proof. by case => _ []. qed.
  
    lemma cr_endoUR f :
      cr_endo f =>
      forall x ,
        unit x =>
        unit (f x).
    proof.
      move=> ef x /unitrP [y] eq_; apply/unitrP; exists (f y).
      by rewrite -cr_endoM // eq_ cr_endo1.
    qed.
  
    lemma cr_endoVR f :
      cr_endo f =>
      forall x ,
        f (invr x) =
        if unit x
        then invr (f x)
        else f x.
    proof.
      move=> ef x; case (unit x) => [ux|Nux].
      + apply/(mulIr (f x)); [by apply/cr_endoUR|].
        by rewrite -cr_endoM // !mulVr ?cr_endo1 // cr_endoUR.
      by rewrite unitout.
    qed.
  
    lemma cr_endoZ f :
      cr_endo f =>
      forall n , f (ofint n) = ofint n.
    proof. by move=> ef n; rewrite /ofint cr_endoMz // cr_endo1. qed.
  
    lemma cr_endoXR f :
      cr_endo f =>
      forall x n ,
        f (RL.exp x n) =
        if unit x
        then RL.exp (f x) n
        else RL.exp (f x) `|n|.
    proof.
      move=> ef x n; wlog: n x / 0 <= n => [wlogn|].
      + case (0 <= n) => [/wlogn -> //|/ltrNge/ltzW].
        move=> len0; move/ler_opp2: (len0) => /= /wlogn {wlogn} /(_ (invr x)).
        rewrite (ler0_norm n) // ger0_norm; [by apply/ler_opp2|].
        rewrite -!exprV invrK unitrV (cr_endoVR _ ef) => ->.
        by case: (unit x) => //; rewrite invrK.
      move=> le0n; rewrite ger0_norm //; elim: n le0n => [|n le0n IHn].
      + by rewrite !expr0 cr_endo1.
      by rewrite !exprS // cr_endoM // IHn; case (unit x).
    qed.

    lemma cr_endo_order f :
      cr_endo f =>
      forall x , order (f x) %| order x.
    proof. by move/cr_endo_zmod/zmod_endo_order. qed.

    lemma cr_endo_orbit f :
      cr_endo f =>
      forall x y ,
        orbit x y => orbit (f x) (f y).
    proof. by move/cr_endo_zmod/zmod_endo_orbit. qed.
  
    lemma cr_endo_orbit_list f :
      cr_endo f =>
      forall x ,
        0 < order (f x) =>
        flatten (nseq (order x %/ order (f x)) (orbit_list (f x))) = map f (orbit_list x).
    proof. by move/cr_endo_zmod/zmod_endo_orbit_list. qed.
  
    lemma cr_endo_eqv_orbit f :
      cr_endo f =>
      forall x y z ,
        eqv_orbit x y z =>
        eqv_orbit (f x) (f y) (f z).
    proof. by move/cr_endo_zmod/zmod_endo_eqv_orbit. qed.

    lemma subcr_subcr_cr_endo f P :
      cr_endo f =>
      subcr P =>
      subcr (P \o f).
    proof.
      move=> ef sP; rewrite /(\o); split; [|split].
      + by apply/subzmod_subzmod_zmod_endo; [apply/cr_endo_zmod|apply/subcr_zmod].
      + by rewrite cr_endo1 // subcr1.
      by move=> x y; rewrite cr_endoM //; apply/subcrM.
    qed.

    lemma subcr_cr_endo_subcr f P :
      cr_endo f =>
      subcr P =>
      subcr (fun y => exists x , f x = y /\ P x).
    proof.
      move=> ef sP; rewrite /(\o); split; [|split].
      + by apply/subzmod_zmod_endo_subzmod; [apply/cr_endo_zmod|apply/subcr_zmod].
      + by exists oner; rewrite cr_endo1 // subcr1.
      move=> ? ? [x] [] <<- Px [y] [] <<- Py; exists (x * y).
      by rewrite cr_endoM // subcrM.
    qed.

    lemma cr_endo_fixed_subcr f :
      cr_endo f =>
      subcr (fun x => f x = x).
    proof.
      move=> ef; split; [by apply/zmod_endo_fixed_subzmod/cr_endo_zmod|split].
      + by rewrite cr_endo1.
      by move=> x y; rewrite cr_endoM // => -> ->.
    qed.

    pred cr_mono_endo f =
      injective f /\
      cr_endo f.

    lemma cr_mono_endo_inj f :
      cr_mono_endo f => injective f.
    proof. by case. qed.

    lemma cr_mono_endo_endo f :
      cr_mono_endo f => cr_endo f.
    proof. by case. qed.

    lemma cr_mono_endo_zmod f :
      cr_mono_endo f => zmod_mono_endo f.
    proof.
      by move=> ef; split; [apply/cr_mono_endo_inj|apply/cr_endo_zmod/cr_mono_endo_endo].
    qed.

    lemma cr_mono_endo_zmod_endo f :
      cr_mono_endo f => zmod_endo f.
    proof. by move/cr_mono_endo_endo/cr_endo_zmod. qed.

    lemma cr_mono_endo_id :
      cr_mono_endo idfun<:t>.
    proof. by split; [rewrite inj_idfun<:t>|rewrite cr_endo_id]. qed.

    lemma cr_mono_endo_comp f g :
      cr_mono_endo f =>
      cr_mono_endo g =>
      cr_mono_endo (f \o g).
    proof.
      by case=> injf ef [] injg eg; split; [apply/inj_comp|apply/cr_endo_comp].
    qed.

    lemma cr_mono_endo_iter f :
      cr_mono_endo f =>
      forall n ,
        cr_mono_endo (iter n f).
    proof.
      move=> ef n; case (0 <= n) => [|/ltrNge/ltzW len0]; last first.
      + have ->: iter n f = idfun; [|by apply/cr_mono_endo_id].
        by apply/fun_ext => x; rewrite iter0.
      elim: n => [|n le0n IHn].
      + have ->: iter 0 f = idfun; [|by apply/cr_mono_endo_id].
        by apply/fun_ext => x; rewrite iter0.
      have ->: iter (n + 1) f = f \o (iter n f); [|by apply/cr_mono_endo_comp].
      by apply/fun_ext => x; rewrite iterS.
    qed.

    lemma cr_mono_endo0 f :
      cr_mono_endo f =>
      morphism_0 f zeror zeror.
    proof. by move/cr_mono_endo_endo/cr_endo0. qed.

    lemma cr_mono_endoD f :
      cr_mono_endo f =>
      morphism_2 f RL.(+) RL.(+).
    proof. by move/cr_mono_endo_endo/cr_endoD. qed.

    lemma cr_mono_endoN f :
      cr_mono_endo f =>
      morphism_1 f RL.([-]) RL.([-]).
    proof. by move/cr_mono_endo_endo/cr_endoN. qed.

    lemma cr_mono_endoB f :
      cr_mono_endo f =>
      morphism_2 f RL.( - ) RL.( - ).
    proof. by move/cr_mono_endo_endo/cr_endoB. qed.

    lemma cr_mono_endoMz f :
      cr_mono_endo f =>
      forall (x : t) n , f (intmul x n) = intmul (f x) n.
    proof. by move/cr_mono_endo_endo/cr_endoMz. qed.

    lemma cr_mono_endo1 f :
      cr_mono_endo f =>
      morphism_0 f oner oner.
    proof. by move/cr_mono_endo_endo/cr_endo1. qed.
  
    lemma cr_mono_endoM f :
      cr_mono_endo f =>
      morphism_2 f RL.( * ) RL.( * ).
    proof. by move/cr_mono_endo_endo/cr_endoM. qed.
  
    lemma cr_mono_endoUR f :
      cr_mono_endo f =>
      forall x ,
        unit x =>
        unit (f x).
    proof. by move/cr_mono_endo_endo/cr_endoUR. qed.
  
    lemma cr_mono_endoVR f :
      cr_mono_endo f =>
      forall x ,
        f (invr x) =
        if unit x
        then invr (f x)
        else f x.
    proof. by move/cr_mono_endo_endo/cr_endoVR. qed.
  
    lemma cr_mono_endoZ f :
      cr_mono_endo f =>
      forall n , f (ofint n) = ofint n.
    proof. by move/cr_mono_endo_endo/cr_endoZ. qed.
  
    lemma cr_mono_endoXR f :
      cr_mono_endo f =>
      forall x n ,
        f (RL.exp x n) =
        if unit x
        then RL.exp (f x) n
        else RL.exp (f x) `|n|.
    proof. by move/cr_mono_endo_endo/cr_endoXR. qed.

    lemma cr_mono_endo_eq0 f :
      cr_mono_endo f =>
      forall x , f x = zeror <=> x = zeror.
    proof. by move/cr_mono_endo_zmod/zmod_mono_endo_eq0. qed.

    lemma cr_mono_endoP0 f :
      cr_mono_endo f <=>
      ( (forall x , f x = zeror => x = zeror) /\
        cr_endo f ).
    proof. by rewrite /cr_endo 2!andbA -zmod_mono_endoP0 /cr_mono_endo /cr_endo -!andbA. qed.

    lemma cr_mono_endo_order f :
      cr_mono_endo f =>
      forall x , order (f x) = order x.
    proof. by move/cr_mono_endo_zmod/zmod_mono_endo_order. qed.

    lemma cr_mono_endo_orbit f :
      cr_mono_endo f =>
      forall x y ,
        orbit (f x) (f y) = orbit x y.
    proof. by move/cr_mono_endo_zmod/zmod_mono_endo_orbit. qed.
  
    lemma cr_mono_endo_orbit_list f :
      cr_mono_endo f =>
      forall x ,
        orbit_list (f x) = map f (orbit_list x).
    proof. by move/cr_mono_endo_zmod/zmod_mono_endo_orbit_list. qed.
  
    lemma cr_mono_endo_eqv_orbit f :
      cr_mono_endo f =>
      forall x y z ,
        eqv_orbit (f x) (f y) (f z) =
        eqv_orbit x y z.
    proof. by move/cr_mono_endo_zmod/zmod_mono_endo_eqv_orbit. qed.

    lemma subcr_subcr_cr_mono_endo f P :
      cr_mono_endo f =>
      subcr P =>
      subcr (P \o f).
    proof. by move/cr_mono_endo_endo/subcr_subcr_cr_endo/(_ P). qed.

    lemma subcr_cr_mono_endo_subcr f P :
      cr_mono_endo f =>
      subcr P =>
      subcr (fun y => exists x , f x = y /\ P x).
    proof. by move/cr_mono_endo_endo/subcr_cr_endo_subcr/(_ P). qed.

    lemma cr_mono_endo_fixed_subcr f :
      cr_mono_endo f =>
      subcr (fun x => f x = x).
    proof. by move/cr_mono_endo_endo/cr_endo_fixed_subcr. qed.

    pred cr_auto (f : t -> t) =
      surjective f /\
      cr_mono_endo f.

    lemma cr_auto_inj f :
      cr_auto f => injective f.
    proof. by case=> _ /cr_mono_endo_inj. qed.

    lemma cr_auto_surj f :
      cr_auto f => surjective f.
    proof. by case. qed.

    lemma cr_auto_bij f :
      cr_auto f => bijective f.
    proof. by move=> af; apply/bij_inj_surj; rewrite cr_auto_inj // cr_auto_surj. qed.

    lemma cr_auto_mono_endo f :
      cr_auto f => cr_mono_endo f.
    proof. by case. qed.

    lemma cr_auto_endo f :
      cr_auto f => cr_endo f.
    proof. by move/cr_auto_mono_endo/cr_mono_endo_endo. qed.

    lemma cr_auto_zmod f :
      cr_auto f => zmod_auto f.
    proof.
      move=> ef; split.
      + by apply/cr_auto_surj.
      by apply/cr_mono_endo_zmod/cr_auto_mono_endo.
    qed.

    lemma cr_auto_zmod_mono_endo f :
      cr_auto f => zmod_mono_endo f.
    proof. by move/cr_auto_zmod/zmod_auto_mono_endo. qed.

    lemma cr_auto_zmod_endo f :
      cr_auto f => zmod_endo f.
    proof. by move/cr_auto_zmod/zmod_auto_endo. qed.

    lemma cr_autoP f :
      cr_auto f <=> (bijective f /\ cr_endo f).
    proof.
      split=> [af|[/bij_inj_surj [injf surjf] ef]]; split=> //.
      + by apply/cr_auto_bij.
      by apply/cr_auto_endo.
    qed.

    lemma cr_auto_id :
      cr_auto idfun<:t>.
    proof. by split; [apply/bij_surj; rewrite bij_idfun<:t>|rewrite cr_mono_endo_id]. qed.

    lemma cr_auto_comp f g :
      cr_auto f =>
      cr_auto g =>
      cr_auto (f \o g).
    proof.
      case/cr_autoP=> bijf ef /cr_autoP [] bijg eg; apply/cr_autoP.
      by split; [apply/bij_comp|apply/cr_endo_comp].
    qed.

    lemma cr_auto_iter f :
      cr_auto f =>
      forall n ,
        cr_auto (iter n f).
    proof.
      move=> ef n; case (0 <= n) => [|/ltrNge/ltzW len0]; last first.
      + have ->: iter n f = idfun; [|by apply/cr_auto_id].
        by apply/fun_ext => x; rewrite iter0.
      elim: n => [|n le0n IHn].
      + have ->: iter 0 f = idfun; [|by apply/cr_auto_id].
        by apply/fun_ext => x; rewrite iter0.
      have ->: iter (n + 1) f = f \o (iter n f); [|by apply/cr_auto_comp].
      by apply/fun_ext => x; rewrite iterS.
    qed.

    lemma cr_auto0 f :
      cr_auto f =>
      morphism_0 f zeror zeror.
    proof. by move/cr_auto_mono_endo; apply/cr_mono_endo0. qed.

    lemma cr_autoD f :
      cr_auto f =>
      morphism_2 f RL.(+) RL.(+).
    proof. by move/cr_auto_mono_endo; apply/cr_mono_endoD. qed.

    lemma cr_autoN f :
      cr_auto f =>
      morphism_1 f RL.([-]) RL.([-]).
    proof. by move/cr_auto_mono_endo; apply/cr_mono_endoN. qed.

    lemma cr_autoB f :
      cr_auto f =>
      morphism_2 f RL.( - ) RL.( - ).
    proof. by move/cr_auto_mono_endo; apply/cr_mono_endoB. qed.

    lemma cr_autoMz f :
      cr_auto f =>
      forall (x : t) n , f (intmul x n) = intmul (f x) n.
    proof. by move/cr_auto_mono_endo; apply/cr_mono_endoMz. qed.

    lemma cr_auto1 f :
      cr_auto f =>
      morphism_0 f oner oner.
    proof. by move/cr_auto_mono_endo/cr_mono_endo1. qed.
  
    lemma cr_autoM f :
      cr_auto f =>
      morphism_2 f RL.( * ) RL.( * ).
    proof. by move/cr_auto_mono_endo/cr_mono_endoM. qed.

    lemma cr_autoU f :
      cr_auto f =>
      forall x ,
        unit (f x) = unit x.
    proof.
      move=> ef x; apply/eq_iff; split; [|by apply/cr_mono_endoUR/cr_auto_mono_endo].
      move/cr_auto_bij: (ef) => [g] [] canfg cangf; rewrite !unitrP => -[y] eq_.
      by exists (g y); apply/(cr_auto_inj _ ef); rewrite cr_auto1 // cr_autoM // cangf.
    qed.
  
    lemma cr_autoV f :
      cr_auto f =>
      morphism_1 f RL.invr RL.invr.
    proof.
      move=> ef x; rewrite cr_mono_endoVR ?cr_auto_mono_endo //.
      by case (unit x) => // Nux; rewrite -eq_sym unitout // cr_autoU.
    qed.
  
    lemma cr_autoZ f :
      cr_auto f =>
      forall n , f (ofint n) = ofint n.
    proof. by move/cr_auto_mono_endo/cr_mono_endoZ. qed.
  
    lemma cr_autoX f :
      cr_auto f =>
      forall x n ,
        f (RL.exp x n) =
        RL.exp (f x) n.
    proof.
      move=> ef x n; rewrite cr_mono_endoXR ?cr_auto_mono_endo //.
      case (unit x) => // Nux; case (0 <= n) => [le0n|/ltrNge/ltzW len0].
      + by rewrite ger0_norm.
      by rewrite ler0_norm // -exprV unitout // cr_autoU.
    qed.

    lemma cr_auto_eq0 f :
      cr_auto f =>
      forall x , f x = zeror <=> x = zeror.
    proof. by move/cr_auto_mono_endo; apply/cr_mono_endo_eq0. qed.

    lemma cr_auto_inv f :
      cr_auto f =>
      exists g ,
        cancel f g /\
        cancel g f /\
        cr_auto g.
    proof.
      rewrite cr_autoP => |> bijf; move: (bijf) => [] g [] canfg cangf ef.
      exists g; rewrite canfg cangf /= cr_autoP; split; [by exists f; split|].
      split; split; [by rewrite -{1}(cr_endo0 f) // /morphism_0 canfg| | |].
      + by move=> x y; apply/(bij_inj _ bijf); rewrite (cr_endoD _ ef) !cangf.
      + by rewrite -{1}(cr_endo1 f) // /morphism_0 canfg.
      by move=> x y; apply/(bij_inj _ bijf); rewrite (cr_endoM _ ef) !cangf.
    qed.

    lemma cr_auto_order f :
      cr_auto f =>
      forall x , order (f x) = order x.
    proof. by move/cr_auto_zmod/zmod_auto_order. qed.

    lemma cr_auto_orbit f :
      cr_auto f =>
      forall x y ,
        orbit (f x) (f y) = orbit x y.
    proof. by move/cr_auto_zmod/zmod_auto_orbit. qed.
  
    lemma cr_auto_orbit_list f :
      cr_auto f =>
      forall x ,
        orbit_list (f x) = map f (orbit_list x).
    proof. by move/cr_auto_zmod/zmod_auto_orbit_list. qed.
  
    lemma cr_auto_eqv_orbit f :
      cr_auto f =>
      forall x y z ,
        eqv_orbit (f x) (f y) (f z) =
        eqv_orbit x y z.
    proof. by move/cr_auto_zmod/zmod_auto_eqv_orbit. qed.

    lemma subcr_subcr_cr_auto f P :
      cr_auto f =>
      subcr P =>
      subcr (P \o f).
    proof. by move/cr_auto_mono_endo/subcr_subcr_cr_mono_endo/(_ P). qed.

    lemma subcr_cr_auto_subcr f P :
      cr_auto f =>
      subcr P =>
      subcr (fun y => exists x , f x = y /\ P x).
    proof. by move/cr_auto_mono_endo/subcr_cr_mono_endo_subcr/(_ P). qed.

    lemma cr_auto_fixed_subcr f :
      cr_auto f =>
      subcr (fun x => f x = x).
    proof. by move/cr_auto_mono_endo/cr_mono_endo_fixed_subcr. qed.
  end CRStr.
end ComRingStruct.

(* -------------------------------------------------------------------- *)	      
abstract theory IDomainStruct.
  type t.

  clone import IDomain as RL with
    type t <= t.

  clone include ComRingStruct with
    type t    <- t,
    theory RL <- RL
    rename [theory] "RL" as "Gone".

  theory IDStr.
    import ZModStr CRStr.
  
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
  
    clone import BigComRing as Big with
      theory CR <- RL.
  
    clone import BinomialCoeffs as Bin with
      theory R   <- RL,
      theory BCR <- Big.
  
    op frobenius x = RL.exp x char.

    lemma frobenius_cr_mono_endo :
      prime char =>
      cr_mono_endo frobenius.
    proof.
      move=> prime_char; apply/cr_mono_endoP0; do!split.
      + rewrite /frobenius; move/gt0_prime: prime_char.
        elim: char ge0_char => // n le0n IHn _ x.
        case/ler_eqVlt: (le0n) => [<<-/=|lt0n]; [by rewrite expr1|].
        by rewrite exprSr // => /mulf_eq0 [|] //; apply/IHn.
      + by rewrite /frobenius /morphism_0 expr0z; move/gt0_prime/gtr_eqF: prime_char => ->.
      + move=> x y; rewrite /frobenius Bin.binomial ?ge0_char //.
        rewrite BAdd.big_int_recr ?ge0_char //= expr0 mulr1.
        rewrite binn ?ge0_char // mulr1z addrC; congr.
        rewrite BAdd.big_ltn ?gt0_prime ?prime_char //= expr0 mul1r bin0 ?ge0_char //.
        rewrite mulr1z addrC eq_sym -subr_eq eq_sym subrr.
        rewrite (BAdd.eq_big_seq _ (fun _ => zeror)); last by apply/BAdd.big1_eq.
        move => k mem_k /=; rewrite -mulr_intr; case: (dvd_char (bin char k)) => + _.
        move => ->; [|by rewrite mulr0].
        apply/prime_dvd_bin; [by apply/prime_char|].
        by case/mem_range: mem_k => le1k -> //=; apply/ltzE.
      + by rewrite /frobenius /morphism_0 expr1z.
      by move=> x y; rewrite /frobenius; apply/exprMn/ge0_char.
    qed.

    lemma frobenius_inj :
      prime char =>
      injective frobenius.
    proof. by move/frobenius_cr_mono_endo/cr_mono_endo_inj. qed.

    lemma frobenius_cr_endo :
      prime char =>
      cr_endo frobenius.
    proof. by move/frobenius_cr_mono_endo/cr_mono_endo_endo. qed.

    lemma frobenius_zmod_mono_endo :
      prime char =>
      zmod_mono_endo frobenius.
    proof. by move/frobenius_cr_mono_endo/cr_mono_endo_zmod. qed.

    lemma cr_mono_endo_zmod_endo :
      prime char =>
      zmod_endo frobenius.
    proof. by move/frobenius_cr_mono_endo/cr_mono_endo_zmod_endo. qed.

    lemma frobenius0 :
      prime char =>
      morphism_0 frobenius zeror zeror.
    proof. by move/frobenius_cr_mono_endo/cr_mono_endo0. qed.
  
    lemma frobeniusD :
      prime char =>
      morphism_2 frobenius RL.( + ) RL.( + ).
    proof. by move/frobenius_cr_mono_endo/cr_mono_endoD. qed.
  
    lemma frobeniusN :
      prime char =>
      morphism_1 frobenius RL.([-]) RL.([-]).
    proof. by move/frobenius_cr_mono_endo/cr_mono_endoN. qed.
  
    lemma frobeniusB :
      prime char =>
      morphism_2 frobenius RL.( - ) RL.( - ).
    proof. by move/frobenius_cr_mono_endo/cr_mono_endoB. qed.

    lemma frobeniusMz :
      prime char =>
      forall (x : t) n , frobenius (intmul x n) = intmul (frobenius x) n.
    proof. by move/frobenius_cr_mono_endo/cr_mono_endoMz. qed.

    lemma frobenius1 :
      frobenius oner = oner.
    proof. by rewrite /frobenius expr1z. qed.
  
    lemma frobeniusM :
      prime char =>
      morphism_2 frobenius RL.( * ) RL.( * ).
    proof. by move/frobenius_cr_mono_endo/cr_mono_endoM. qed.
  
    lemma frobeniusU :
      prime char =>
      forall x , unit (frobenius x) = unit x.
    proof.
      move=> prime_char x; apply/eq_iff; split; last first.
      + by apply/cr_mono_endoUR/frobenius_cr_mono_endo.
      by rewrite /frobenius; apply/unitrX_neq0/gtr_eqF/gt0_prime.
    qed.
  
    lemma frobeniusV :
      prime char =>
      morphism_1 frobenius RL.invr RL.invr.
    proof.
      move=> prime_char x; rewrite cr_mono_endoVR ?frobenius_cr_mono_endo //.
      by case (unit x) => //; rewrite -frobeniusU // => Nu_; rewrite unitout.
    qed.

    lemma frobeniusZ :
      prime char =>
      forall n , frobenius (ofint n) = ofint n.
    proof. by move/frobenius_cr_mono_endo/cr_mono_endoZ. qed.

    lemma frobeniusX x n :
      frobenius (RL.exp x n) =
      RL.exp (frobenius x) n.
    proof. by rewrite /frobenius -!exprM mulrC. qed.

    lemma frobenius_eq0 :
      prime char =>
      forall x , frobenius x = zeror <=> x = zeror.
    proof. by move/frobenius_cr_mono_endo/cr_mono_endo_eq0. qed.

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
  
    theory FrobeniusPoly.
  
      clone import Poly as Po with
        type coeff       <- t,
        theory BigCf.BCA <- Big.BAdd,
        theory BigCf.BCM <- Big.BMul,
        theory IDCoeff   <- RL.
  
      op eq_pow_1 n x = RL.exp x n = oner.
  
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
        move => le__; apply/(ler_trans (deg (polyXn n - poly1) - 1)).
        + move: le__; apply/ler_trans.
          apply/lerr_eq/perm_eq_size/uniq_perm_eq; [by apply/uniq_to_seq/is_finite_eq_pow_1| |].
          - by apply/uniq_to_seq/is_finite_root; rewrite IDPoly.subr_eq0 eq_polyXn1 gtr_eqF.
          move => x; rewrite !mem_to_seq /=; [by apply/is_finite_eq_pow_1| |].
          - by apply/finite_root; rewrite IDPoly.subr_eq0 eq_polyXn1 gtr_eqF.
          by rewrite eq_pow_1_poly //; apply/ltzW.
        apply/ler_subl_addr; apply/(ler_trans _ _ _ (degB (polyXn n) poly1)).
        rewrite degXn deg1; apply/ler_maxrP; rewrite -(ler_subl_addr 1 1 n) /= (ltzW 0) //=.
        by apply/ler_maxrP => /=; apply/addr_ge0 => //; apply/ltzW.
      qed.
  
      lemma frobenius_polyXchar x :
        frobenius x = peval (polyXn char) x.
      proof. by rewrite pevalXn ge0_char. qed.
  
      lemma iter_frobenius_fixed_poly n :
        0 <= n =>
        iter_frobenius_fixed n = root (polyXn (char ^ n) - X).
      proof.
        move => le0n; apply/fun_ext => x; rewrite eqboolP /iter_frobenius_fixed.
        rewrite iter_frobenius //.
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
    end FrobeniusPoly.

    import FrobeniusPoly Po.
  
    lemma is_finite_iter_frobenius n :
      prime char =>
      0 < n =>
      is_finite (iter_frobenius_fixed n).
    proof.
      move => prime_char lt0n.
      move: (finite_root (polyXn (char ^ n) - X ) _).
      + rewrite PolyComRing.subr_eq0 eq_polyXnX gtr_eqF //.
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
      + rewrite PolyComRing.subr_eq0 eq_polyXn1 gtr_eqF //.
        apply/subr_gt0/(ltr_le_trans char); [by apply/gt1_prime|].
        rewrite -{1}expr1; apply/ler_weexpn2l => /=; [|by move: lt0n; rewrite ltzE].
        by move: (gt0_prime _ prime_char); rewrite ltzE.
      rewrite size_rootsX -ler_subr_addl -eq_pow_1_poly.
      + by apply/ltzS => /=; apply/expr_gt0/gt0_prime.
      apply/size_to_seq_eq_pow_1/subr_gt0/(ltr_le_trans char); [by apply/gt1_prime|].
      rewrite -{1}expr1; apply/ler_weexpn2l => /=; [|by move: lt0n; rewrite ltzE].
      by move: (gt0_prime _ prime_char); rewrite ltzE.
    qed.

    lemma subcr_iter_frobenius_fixed :
      prime char =>
      forall n , subcr (iter_frobenius_fixed n).
    proof.
      rewrite /iter_frobenius_fixed => prime_char n.
      by apply/cr_endo_fixed_subcr/cr_endo_iter/frobenius_cr_endo.
    qed.

    lemma iter_frobenius_fixed0 :
      prime char =>
      forall n ,
        iter_frobenius_fixed n zeror.
    proof. by move/subcr_iter_frobenius_fixed => + n; move/(_ n)/subcr0. qed.

    lemma iter_frobenius_fixedD :
      prime char =>
      forall n x y ,
        iter_frobenius_fixed n x =>
        iter_frobenius_fixed n y =>
        iter_frobenius_fixed n (x + y).
    proof. by move/subcr_iter_frobenius_fixed => + n; move/(_ n)/subcrD. qed.

    lemma iter_frobenius_fixedN :
      prime char =>
      forall n x ,
        iter_frobenius_fixed n x =>
        iter_frobenius_fixed n (-x).
    proof. by move/subcr_iter_frobenius_fixed => + n; move/(_ n)/subcrN. qed.

    lemma iter_frobenius_fixedB :
      prime char =>
      forall n x y ,
        iter_frobenius_fixed n x =>
        iter_frobenius_fixed n y =>
        iter_frobenius_fixed n (x - y).
    proof. by move/subcr_iter_frobenius_fixed => + n; move/(_ n)/subcrB. qed.

    lemma iter_frobenius_fixedMz :
      prime char =>
      forall n x m ,
        iter_frobenius_fixed n x =>
        iter_frobenius_fixed n (intmul x m).
    proof. by move/subcr_iter_frobenius_fixed => + n; move/(_ n)/subcrMz. qed.

    lemma iter_frobenius_fixed1 :
      forall n ,
        iter_frobenius_fixed n oner.
    proof.
      rewrite /iter_frobenius_fixed => n; case (0 <= n) => [le0n|/ltrNge/ltzW len0].
      + by rewrite iter_frobenius // expr1z.
      by rewrite iter0.
    qed.

    lemma iter_frobenius_fixedM :
      prime char =>
      forall n x y ,
        iter_frobenius_fixed n x =>
        iter_frobenius_fixed n y =>
        iter_frobenius_fixed n (x * y).
    proof. by move/subcr_iter_frobenius_fixed => + n; move/(_ n)/subcrM. qed.

    lemma iter_frobenius_fixedZ :
      prime char =>
      forall n m ,
        iter_frobenius_fixed n (ofint m).
    proof. by move/subcr_iter_frobenius_fixed => + n; move/(_ n)/subcrZ. qed.

    lemma iter_frobenius_fixedV :
      forall n x ,
        iter_frobenius_fixed n x =>
        iter_frobenius_fixed n (invr x).
    proof.
      rewrite /iter_frobenius_fixed => n x; case (0 <= n) => [le0n|/ltrNge/ltzW len0].
      + by rewrite !iter_frobenius // exprVn ?expr_ge0 ?ge0_char // => ->.
      by rewrite !iter0.
    qed.

    lemma iter_frobenius_fixedX :
      forall n x m ,
        iter_frobenius_fixed n x =>
        iter_frobenius_fixed n (exp x m).
    proof.
      rewrite /iter_frobenius_fixed => n x m; case (0 <= n) => [le0n|/ltrNge/ltzW len0].
      + by rewrite !iter_frobenius // -exprM mulrC exprM => ->.
      by rewrite !iter0.
    qed.

    lemma subcr_frobenius P :
      subcr P =>
      forall x ,
        P x =>
        P (frobenius x).
    proof.
      by rewrite /frobenius => sP x Px; apply/subcrXR => //; apply/ge0_char.
    qed.

    lemma cr_endo_frobenius f :
      cr_endo f =>
      forall x ,
        f (frobenius x) = frobenius (f x).
    proof. by rewrite /frobenius => ef x; rewrite cr_endoXR // ger0_norm ?ge0_char. qed.

    lemma cr_endo_iter_frobenius_fixed f :
      cr_endo f =>
      forall n x ,
        iter_frobenius_fixed n x =>
        iter_frobenius_fixed n (f x).
    proof.
      rewrite /iter_frobenius_fixed => ef n x; case: (0 <= n) => [le0n|/ltrNge/ltzW len0].
      + rewrite !iter_frobenius //; move: (cr_endoXR _ ef x (char ^ n)).
        by rewrite ger0_norm ?expr_ge0 ?ge0_char // if_same => <- ->.
      by rewrite !iter0.
    qed.

    lemma cr_mono_endo_frobenius f :
      cr_mono_endo f =>
      forall x ,
        f (frobenius x) = frobenius (f x).
    proof. by move/cr_mono_endo_endo/cr_endo_frobenius. qed.

    lemma cr_mono_endo_iter_frobenius_fixed f :
      cr_mono_endo f =>
      forall n x ,
        iter_frobenius_fixed n (f x) = iter_frobenius_fixed n x.
    proof.
      rewrite /iter_frobenius_fixed => ef n x; case: (0 <= n) => [le0n|/ltrNge/ltzW len0].
      + rewrite !iter_frobenius //; move: (cr_mono_endoXR _ ef x (char ^ n)).
        rewrite ger0_norm ?expr_ge0 ?ge0_char // if_same => <-.
        by apply/eq_iff/inj_eq/cr_mono_endo_inj.
      by rewrite !iter0.
    qed.

    lemma cr_auto_frobenius f :
      cr_auto f =>
      forall x ,
        f (frobenius x) = frobenius (f x).
    proof. by move/cr_auto_mono_endo/cr_mono_endo_frobenius. qed.

    lemma cr_auto_iter_frobenius_fixed f :
      cr_auto f =>
      forall n x ,
        iter_frobenius_fixed n (f x) = iter_frobenius_fixed n x.
    proof. by move/cr_auto_mono_endo/cr_mono_endo_iter_frobenius_fixed. qed.
  
    (*TODO: this clear should remove everything once subtypes are introduced without axioms. *)
    clear [ Bin.* Big.BAdd.* Big.BMul.* Big.*
            FrobeniusPoly.Po.BigCf.*
            FrobeniusPoly.Po.Lift.* FrobeniusPoly.Po.ZPoly.*
            FrobeniusPoly.Po.PolyComRing.AddMonoid.* FrobeniusPoly.Po.PolyComRing.MulMonoid.*
            FrobeniusPoly.Po.PolyComRing.*
            FrobeniusPoly.Po.BigPoly.PCA.* FrobeniusPoly.Po.BigPoly.PCM.*
            FrobeniusPoly.Po.BigPoly.*
            FrobeniusPoly.Po.IDPoly.AddMonoid.* FrobeniusPoly.Po.IDPoly.MulMonoid.*
            FrobeniusPoly.Po.IDPoly.* FrobeniusPoly.Po.* FrobeniusPoly.* ].
  end IDStr.
end IDomainStruct.

(* -------------------------------------------------------------------- *)
abstract theory FieldStruct.
  type t.

  clone import Field as RL with
    type t <= t.

  clone include IDomainStruct with
    type t    <- t,
    theory RL <- RL
    rename [theory] "RL" as "Gone".

  theory FStr.
    import ZModStr CRStr IDStr.

    op subf P =
      subcr P /\
      (forall x , P x => P (invr x)).

    lemma subf_cr P : subf P => subcr P.
    proof. by case. qed.

    lemma subf_zmod P : subf P => subzmod P.
    proof. by move/subf_cr; apply/subcr_zmod. qed.

    lemma subfT : subf predT.
    proof. by rewrite /predT. qed.

    lemma subfI P1 P2 : subf P1 => subf P2 => subf (predI P1 P2).
    proof.
      case=> P1_ P1V [] P2_ P2V; split.
      + by apply/subcrI/subf_cr.
      by move=> x; rewrite /predI => /> ? ?; rewrite P1V // P2V.
    qed.

    lemma subf0 P : subf P => P zeror.
    proof. by move/subf_cr; apply/subcr0. qed.

    lemma subfD P : subf P => forall x y , P x => P y => P (x + y).
    proof. by move/subf_cr; apply/subcrD. qed.

    lemma subfN P : subf P => forall x , P x => P (-x).
    proof. by move/subf_cr; apply/subcrN. qed.
  
    lemma subfB P : subf P => forall x y , P x => P y => P (x - y).
    proof. by move/subf_cr; apply/subcrB. qed.

    lemma subfMz P : subf P => forall x n , P x => P (intmul x n).
    proof. by move/subf_cr; apply/subcrMz. qed.

    lemma subf_mem_orbit P : subf P => forall x y , orbit x y => P x => P y.
    proof. by move/subf_cr; apply/subcr_mem_orbit. qed.
  
    lemma subf_mem_orbit_list P : subf P => forall x y , y \in orbit_list x => P x => P y.
    proof. by move/subf_cr; apply/subcr_mem_orbit_list. qed.
  
    lemma subf_eqv_orbit P :
      subf P =>
      forall x y z ,
        eqv_orbit x y z =>
        P x =>
        P y <=> P z.
    proof. by move/subf_cr; apply/subcr_eqv_orbit. qed.

    lemma subf1 P : subf P => P oner.
    proof. by move/subf_cr; apply/subcr1. qed.
  
    lemma subfM P : subf P => forall x y , P x => P y => P (x * y).
    proof. by move/subf_cr; apply/subcrM. qed.

    lemma subfZ P n : subf P => P (ofint n).
    proof. by move/subf_cr; apply/subcrZ. qed.

    lemma subfV P : subf P => forall x , P x => P (invr x).
    proof. by case. qed.

    lemma subfX P : subf P => forall x n , P x => P (exp x n).
    proof.
      move=> subfP x n Px; case (0 <= n) => [|/ltrNge/ltzW/ler_opp2/=].
      + by apply/subcrXR => //; apply/subf_cr/subfP.
      move/(subcrXR _ (subf_cr _ subfP) _ _ (subfV _ subfP _ Px)).
      by rewrite exprV.
    qed.

    lemma subf_frobenius P :
      subf P =>
      forall x ,
        P x =>
        P (frobenius x).
    proof. by move/subf_cr; apply/subcr_frobenius. qed.

    lemma cr_endoU f :
      cr_endo f =>
      forall x ,
        unit (f x) = unit x.
    proof.
      move=> ef x; apply/eq_iff; split; [|by apply/cr_endoUR].
      by rewrite -!unitfE; apply/implybNN => ->>; apply/cr_endo0.
    qed.
  
    lemma cr_endoV f :
      cr_endo f =>
      morphism_1 f RL.invr RL.invr.
    proof.
      move=> ef x; rewrite cr_endoVR //; case (unit x) => //.
      by rewrite -(cr_endoU _ ef) => Nu_; rewrite unitout.
    qed.
  
    lemma cr_endoX f :
      cr_endo f =>
      forall x n ,
        f (RL.exp x n) =
        RL.exp (f x) n.
    proof.
      move=> ef x n; rewrite cr_endoXR //; case (unit x) => //.
      case (0 <= n) => [le0n|/ltrNge/ltzW len0].
      + by rewrite ger0_norm.
      by rewrite ler0_norm // -exprV -(cr_endoU _ ef) => Nu_; rewrite unitout.
    qed.

    lemma cr_endo_fixed_subf f :
      cr_endo f =>
      subf (fun x => f x = x).
    proof.
      move=> ef; split; [by apply/cr_endo_fixed_subcr|].
      by move=> x; rewrite cr_endoV // => ->.
    qed.

    lemma cr_mono_endoU f :
      cr_mono_endo f =>
      forall x ,
        unit (f x) = unit x.
    proof. by move/cr_mono_endo_endo/cr_endoU. qed.
  
    lemma cr_mono_endoV f :
      cr_mono_endo f =>
      morphism_1 f RL.invr RL.invr.
    proof. by move/cr_mono_endo_endo/cr_endoV. qed.
  
    lemma cr_mono_endoX f :
      cr_mono_endo f =>
      forall x n ,
        f (RL.exp x n) =
        RL.exp (f x) n.
    proof. by move/cr_mono_endo_endo/cr_endoX. qed.

    lemma cr_mono_endo_fixed_subf f :
      cr_mono_endo f =>
      subf (fun x => f x = x).
    proof. by move/cr_mono_endo_endo/cr_endo_fixed_subf. qed.

    lemma cr_autoU f :
      cr_auto f =>
      forall x ,
        unit (f x) = unit x.
    proof. by move/cr_auto_mono_endo/cr_mono_endoU. qed.
  
    lemma cr_autoV f :
      cr_auto f =>
      morphism_1 f RL.invr RL.invr.
    proof. by move/cr_auto_mono_endo/cr_mono_endoV. qed.
  
    lemma cr_autoX f :
      cr_auto f =>
      forall x n ,
        f (RL.exp x n) =
        RL.exp (f x) n.
    proof. by move/cr_auto_mono_endo/cr_mono_endoX. qed.

    lemma cr_auto_fixed_subf f :
      cr_auto f =>
      subf (fun x => f x = x).
    proof. by move/cr_auto_mono_endo/cr_mono_endo_fixed_subf. qed.

    lemma subf_iter_frobenius_fixed n :
      prime char =>
      subf (iter_frobenius_fixed n).
    proof.
      rewrite /iter_frobenius_fixed => prime_char.
      by apply/cr_endo_fixed_subf/cr_endo_iter/frobenius_cr_endo.
    qed.

    lemma subf_subf_cr_endo f P :
      cr_endo f =>
      subf P =>
      subf (P \o f).
    proof.
      move=> ef sP; rewrite /(\o); split.
      + by apply/subcr_subcr_cr_endo => //; apply/subf_cr.
      by move=> x; rewrite cr_endoV //; apply/subfV.
    qed.

    lemma subf_cr_endo_subf f P :
      cr_endo f =>
      subf P =>
      subf (fun y => exists x , f x = y /\ P x).
    proof.
      move=> ef sP; split.
      + by apply/subcr_cr_endo_subcr => //; apply/subf_cr.
      move=> ? [x] [] <<- Px; exists (invr x).
      by rewrite cr_endoV // subfV.
    qed.

    lemma subf_subf_cr_mono_endo f P :
      cr_mono_endo f =>
      subf P =>
      subf (P \o f).
    proof. by move/cr_mono_endo_endo/subf_subf_cr_endo/(_ P). qed.

    lemma subf_cr_mono_endo_subf f P :
      cr_mono_endo f =>
      subf P =>
      subf (fun y => exists x , f x = y /\ P x).
    proof. by move/cr_mono_endo_endo/subf_cr_endo_subf/(_ P). qed.

    lemma subf_subf_cr_auto f P :
      cr_auto f =>
      subf P =>
      subf (P \o f).
    proof. by move/cr_auto_mono_endo/subf_subf_cr_mono_endo/(_ P). qed.

    lemma subf_cr_auto_subf f P :
      cr_auto f =>
      subf P =>
      subf (fun y => exists x , f x = y /\ P x).
    proof. by move/cr_auto_mono_endo/subf_cr_mono_endo_subf/(_ P). qed.
  end FStr.
end FieldStruct.

