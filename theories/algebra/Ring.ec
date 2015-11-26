(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2015 - IMDEA Software Institute
 * Copyright (c) - 2012--2015 - Inria
 * 
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

pragma +implicits.

(* -------------------------------------------------------------------- *)
require import Fun Int IntExtra.
require (*--*) Monoid.

(* -------------------------------------------------------------------- *)
abstract theory ZModule.
  type t.

  op zeror : t.
  op ( + ) : t -> t -> t.
  op [ - ] : t -> t.

  axiom nosmt addrA: associative   (+).
  axiom nosmt addrC: commutative   (+).
  axiom nosmt add0r: left_id zeror (+).
  axiom nosmt addNr: left_inverse  zeror [-] (+).

  clone Monoid as AddMonoid with
    type t   <- t,
      op idm <- zeror,
      op (+) <- (+)
    proof *.

  realize Axioms.addmA by apply/addrA.
  realize Axioms.addmC by apply/addrC.
  realize Axioms.add0m by apply/add0r.

  op ( - ) (x y : t) = x + -y axiomatized by subrE.

  lemma nosmt addr0: right_id zeror (+).
  proof. by move=> x; rewrite addrC add0r. qed.

  lemma nosmt addrN: right_inverse zeror [-] (+).
  proof. by move=> x; rewrite addrC addNr. qed.

  lemma nosmt addrCA: left_commutative (+).
  proof. by move=> x y z; rewrite !addrA (@addrC x y). qed.

  lemma nosmt addrAC: right_commutative (+).
  proof. by move=> x y z; rewrite -!addrA (@addrC y z). qed.

  lemma nosmt addrACA: interchange (+) (+).
  proof. by move=> x y z t; rewrite -!addrA (addrCA y). qed.

  lemma nosmt subrr (x : t): x - x = zeror.
  proof. by rewrite subrE /= addrN. qed.

  lemma nosmt addKr: left_loop [-] (+).
  proof. by move=> x y; rewrite addrA addNr add0r. qed.

  lemma nosmt addNKr: rev_left_loop [-] (+).
  proof. by move=> x y; rewrite addrA addrN add0r. qed.

  lemma nosmt addrK: right_loop [-] (+).
  proof. by move=> x y; rewrite -addrA addrN addr0. qed.

  lemma addrK_sub (x y : t): x + y - y = x.
  proof. by rewrite subrE addrK. qed.

  lemma nosmt addrNK: rev_right_loop [-] (+).
  proof. by move=> x y; rewrite -addrA addNr addr0. qed.

  lemma nosmt subrK x y: (x - y) + y = x.
  proof. by rewrite subrE addrNK. qed.

  lemma nosmt addrI: right_injective (+).
  proof. by move=> x y z h; rewrite -(@addKr x z) -h addKr. qed.

  lemma nosmt addIr: left_injective (+).
  proof. by move=> x y z h; rewrite -(@addrK x z) -h addrK. qed.

  lemma nosmt opprK: involutive [-].
  proof. by move=> x; apply (@addIr (-x)); rewrite addNr addrN. qed.

  lemma nosmt oppr0: -zeror = zeror.
  proof. by rewrite -(@addr0 (-zeror)) addNr. qed.

  lemma oppr_eq0 x : (- x = zeror) <=> (x = zeror).
  proof. by rewrite (inv_eq opprK) oppr0. qed.

  lemma nosmt subr0 (x : t): x - zeror = x.
  proof. by rewrite subrE /= oppr0 addr0. qed.

  lemma nosmt sub0r (x : t): zeror - x = - x.
  proof. by rewrite subrE /= add0r. qed.

  lemma nosmt opprD (x y : t): -(x + y) = -x + -y.
  proof. by apply (@addrI (x + y)); rewrite addrA addrN addrAC addrK addrN. qed.

  lemma nosmt opprB (x y : t): -(x - y) = y - x.
  proof. by rewrite !subrE opprD opprK addrC. qed.

  lemma nosmt subrACA: interchange (-) (+).
  proof. by move=> x y z t; rewrite !subrE addrACA opprD. qed.

  lemma nosmt subr_eq (x y z : t):
    (x - z = y) <=> (x = y + z).
  proof.
    move: (can2_eq (fun x, x - z) (fun x, x + z) _ _ x y) => //=.
    by move=> {x} x /=; rewrite subrE /= addrNK.
    by move=> {x} x /=; rewrite subrE /= addrK.
  qed.

  lemma nosmt subr_eq0 (x y : t): (x - y = zeror) <=> (x = y).
  proof. by rewrite subr_eq add0r. qed.

  lemma nosmt addr_eq0 (x y : t): (x + y = zeror) <=> (x = -y).
  proof. by rewrite -(@subr_eq0 x) subrE /= opprK. qed.

  lemma nosmt eqr_opp (x y : t): (- x = - y) <=> (x = y).
  proof. by apply/(@can_eq _ _ opprK x y). qed.

  lemma eqr_oppLR x y : (- x = y) <=> (x = - y).
  proof. by apply/(@inv_eq _ opprK x y). qed.

  lemma nosmt eqr_sub (x y z t : t) : (x - y = z - t) <=> (x + t = z + y).
  proof.
  rewrite -{1}(addrK t x) -{1}(addrK y z) 2!subrE -!addrA.
  by rewrite (addrC (-t)) !addrA; split=> [/addIr /addIr|->//].
  qed.

  lemma subr_add2r (z x y : t): (x + z) - (y + z) = x - y.
  proof. by rewrite subrE opprD addrACA addrN addr0 subrE. qed.

  op intmul (x : t) (n : int) =
    if n < 0
    then -(iterop (-n) ZModule.(+) x zeror)
    else  (iterop   n  ZModule.(+) x zeror).

  lemma intmulpE z c : 0 <= c =>
    intmul z c = iterop c ZModule.(+) z zeror.
  proof. by rewrite /intmul lezNgt => ->. qed.

  lemma mulr0z (x : t): intmul x 0 = zeror.
  proof. by rewrite /intmul /= iterop0. qed.

  lemma mulr1z (x : t): intmul x 1 = x.
  proof. by rewrite /intmul /= iterop1. qed.

  lemma mulr2z (x : t): intmul x 2 = x + x.
  proof. by rewrite /intmul /= (@iteropS 1) // (@iterS 0) // iter0. qed.

  lemma mulrNz (x : t) (n : int): intmul x (-n) = -(intmul x n).
  proof.
    case: (n = 0)=> [->|nz_c]; first by rewrite oppz0 mulr0z oppr0.
    rewrite /intmul oppz_lt0 oppzK ltz_def nz_c lezNgt /=.
    by case: (n < 0); rewrite ?opprK.
  qed.

  lemma mulrS (x : t) (n : int): 0 <= n =>
    intmul x (n+1) = x + intmul x n.
  proof.
    move=> ge0n; rewrite !intmulpE 1:addz_ge0 //.
    by rewrite !AddMonoid.iteropE iterS.
  qed.
end ZModule.

(* -------------------------------------------------------------------- *)
abstract theory ComRing.
  type t.

  clone include ZModule with type t <- t.

  op   oner  : t.
  op   ( * ) : t -> t -> t.
  op   invr  : t -> t.
  pred unit  : t.

  op ( / ) (x y : t) = x * (invr y) axiomatized by divrE.

  axiom nosmt oner_neq0 : oner <> zeror.
  axiom nosmt mulrA     : associative ( * ).
  axiom nosmt mulrC     : commutative ( * ).
  axiom nosmt mul1r     : left_id oner ( * ).
  axiom nosmt mulrDl    : left_distributive ( * ) (+).
  axiom nosmt mulVr     : left_inverse_in unit oner invr ( * ).
  axiom nosmt unitP     : forall (x y : t), y * x = oner => unit x.
  axiom nosmt unitout   : forall (x : t), !unit x => invr x = x.

  clone Monoid as MulMonoid with
    type t     <- t,
      op idm   <- oner,
      op ( + ) <- ( * )
    proof *.

  realize Axioms.addmA by apply/mulrA.
  realize Axioms.addmC by apply/mulrC.
  realize Axioms.add0m by apply/mul1r.

  lemma nosmt mulr1: right_id oner ( * ).
  proof. by move=> x; rewrite mulrC mul1r. qed.

  lemma nosmt mulrCA: left_commutative ( * ).
  proof. by move=> x y z; rewrite !mulrA (@mulrC x y). qed.

  lemma nosmt mulrAC: right_commutative ( * ).
  proof. by move=> x y z; rewrite -!mulrA (@mulrC y z). qed.

  lemma nosmt mulrACA: interchange ( * ) ( * ).
  proof. by move=> x y z t; rewrite -!mulrA (mulrCA y). qed.

  lemma nosmt mulrDr: right_distributive ( * ) (+).
  proof. by move=> x y z; rewrite mulrC mulrDl !(@mulrC _ x). qed.

  lemma nosmt mul0r: left_zero zeror ( * ).
  proof. by move=> x; apply: (@addIr (oner * x)); rewrite -mulrDl !add0r mul1r. qed.

  lemma nosmt mulr0: right_zero zeror ( * ).
  proof. by move=> x; apply: (@addIr (x * oner)); rewrite -mulrDr !add0r mulr1. qed.

  lemma nosmt mulrN (x y : t): x * (- y) = - (x * y).
  proof. by apply: (@addrI (x * y)); rewrite -mulrDr !addrN mulr0. qed.

  lemma nosmt mulNr (x y : t): (- x) * y = - (x * y).
  proof. by apply: (@addrI (x * y)); rewrite -mulrDl !addrN mul0r. qed.

  lemma nosmt mulrNN (x y : t): (- x) * (- y) = x * y.
  proof. by rewrite mulrN mulNr opprK. qed.

  lemma nosmt mulN1r (x : t): (-oner) * x = -x.
  proof. by rewrite mulNr mul1r. qed.

  lemma nosmt mulrN1 x: x * -oner = -x.
  proof. by rewrite mulrN mulr1. qed.

  lemma nosmt mulrBl: left_distributive ( * ) (-).
  proof. by move=> x y z; rewrite !subrE mulrDl !mulNr. qed.

  lemma nosmt mulrBr: right_distributive ( * ) (-).
  proof. by move=> x y z; rewrite !subrE mulrDr !mulrN. qed.

  lemma mulrnAl x y n : 0 <= n => (intmul x n) * y = intmul (x * y) n.
  proof.
    elim: n => [|n ge0n ih]; rewrite !(mulr0z, mulrS) ?mul0r //.
    by rewrite mulrDl ih.
  qed.

  lemma mulrnAr x y n : 0 <= n => x * (intmul y n) = intmul (x * y) n.
  proof.
    elim: n => [|n ge0n ih]; rewrite !(mulr0z, mulrS) ?mulr0 //.
    by rewrite mulrDr ih.
  qed.

  lemma mulrzAl x y z : (intmul x z) * y = intmul (x * y) z.
  proof.
    case: (lezWP 0 z)=> [|_] le; first by rewrite mulrnAl.
    by rewrite -oppzK mulrNz mulNr mulrnAl -?mulrNz // oppz_ge0.
  qed.

  lemma mulrzAr x y z : x * (intmul y z) = intmul (x * y) z.
  proof.
    case: (lezWP 0 z)=> [|_] le; first by rewrite mulrnAr.
    by rewrite -oppzK mulrNz mulrN mulrnAr -?mulrNz // oppz_ge0.
  qed.

  lemma nosmt mulrV: right_inverse_in unit oner invr ( * ).
  proof. by move=> x /mulVr; rewrite mulrC. qed.

  lemma nosmt divrr (x : t): unit x => x / x = oner.
  proof. by rewrite divrE => /mulrV. qed.

  lemma nosmt invr_out (x : t): !unit x => invr x = x.
  proof. by apply/unitout. qed.

  lemma nosmt unitrP (x : t): unit x <=> (exists y, y * x = oner).
  proof. by split=> [/mulVr<- |]; [exists (invr x) | case=> y /unitP]. qed.

  lemma nosmt mulKr: left_loop_in unit invr ( * ).
  proof. by move=> x un_x y; rewrite mulrA mulVr // mul1r. qed.

  lemma nosmt mulrK: right_loop_in unit invr ( * ).
  proof. by move=> y un_y x; rewrite -mulrA mulrV // mulr1. qed.

  lemma nosmt mulVKr: rev_left_loop_in unit invr ( * ).
  proof. by move=> x un_x y; rewrite mulrA mulrV // mul1r. qed.

  lemma nosmt mulrVK: rev_right_loop_in unit invr ( * ).
  proof. by move=> y nz_y x; rewrite -mulrA mulVr // mulr1. qed.

  lemma nosmt mulrI: right_injective_in unit ( * ).
  proof. by move=> x Ux; have /can_inj h := mulKr _ Ux. qed.

  lemma nosmt mulIr: left_injective_in unit ( * ).
  proof. by move=> x /mulrI h y1 y2; rewrite !(@mulrC _ x) => /h. qed.

  lemma nosmt unitrE (x : t): unit x <=> (x / x = oner).
  proof.
    split=> [Ux|xx1]; 1: by apply/divrr.
    by apply/unitrP; exists (invr x); rewrite mulrC -divrE.
  qed.

  lemma nosmt invrK: involutive invr.
  proof.
    move=> x; case: (unit x)=> Ux; 2: by rewrite !invr_out.
    rewrite -(mulrK _ Ux (invr (invr x))) -mulrA.
    rewrite (@mulrC x) mulKr //; apply/unitrP.
    by exists x; rewrite mulrV.
  qed.

  lemma nosmt invr_inj: injective invr.
  proof. by apply: (can_inj _ _ invrK). qed.

  lemma nosmt unitrV x: unit (invr x) <=> unit x.
  proof. by rewrite !unitrE !divrE invrK mulrC. qed.

  lemma nosmt unitr1: unit oner.
  proof. by apply/unitrP; exists oner; rewrite mulr1. qed.

  lemma nosmt invr1: invr oner = oner.
  proof. by rewrite -{2}(mulVr _ unitr1) mulr1. qed.

  lemma nosmt div1r x: oner / x = invr x.
  proof. by rewrite divrE mul1r. qed.

  lemma nosmt divr1 x: x / oner = x.
  proof. by rewrite divrE invr1 mulr1. qed.

  lemma nosmt unitr0: !unit zeror.
  proof. by apply/negP=> /unitrP [y]; rewrite mulr0 eq_sym oner_neq0. qed.

  lemma nosmt invr0: invr zeror = zeror.
  proof. by rewrite invr_out ?unitr0. qed.

  lemma nosmt unitrN1: unit (-oner).
  proof. by apply/unitrP; exists (-oner); rewrite mulrNN mulr1. qed.

  lemma nosmt invrN1: invr (-oner) = -oner.
  proof. by rewrite -{2}(divrr unitrN1) divrE mulN1r opprK. qed.

  lemma nosmt unitrMl x y : unit y => (unit (x * y) <=> unit x).
  proof.                        (* FIXME: wlog *)
    move=> uy; case: (unit x)=> /=; last first.
      apply/contra=> uxy; apply/unitrP; exists (y * invr (x * y)).
      apply/(mulrI (invr y)); first by rewrite unitrV.
      rewrite !mulrA mulVr // mul1r; apply/(mulIr y)=> //.
      by rewrite -mulrA mulVr // mulr1 mulVr.
    move=> ux; apply/unitrP; exists (invr y * invr x).
    by rewrite -!mulrA mulKr // mulVr.
  qed.

  lemma nosmt unitrMr x y : unit x => (unit (x * y) <=> unit y).
  proof.
    move=> ux; split=> [uxy|uy]; last by rewrite unitrMl.
    by rewrite -(mulKr _ ux y) unitrMl ?unitrV.
  qed.

  lemma nosmt unitrN x : unit (-x) <=> unit x.
  proof. by rewrite -mulN1r unitrMr // unitrN1. qed.

  lemma nosmt invrM x y : unit x => unit y => invr (x * y) = invr y * invr x.
  proof.
    move=> Ux Uy; have Uxy: unit (x * y) by rewrite unitrMl.
    by apply: (mulrI _ Uxy); rewrite mulrV ?mulrA ?mulrK ?mulrV.
  qed.

  lemma nosmt invrN (x : t) : invr (- x) = - (invr x).
  proof.
    case: (unit x) => ux; last by rewrite !invr_out ?unitrN.
    by rewrite -mulN1r invrM ?unitrN1 // invrN1 mulrN1.
  qed.

  lemma nosmt invr_neq0 x : x <> zeror => invr x <> zeror.
  proof.
    move=> nx0; case: (unit x)=> Ux; last by rewrite invr_out ?Ux.
    by apply/negP=> x'0; move: Ux; rewrite -unitrV x'0 unitr0.
  qed.

  lemma nosmt invr_eq0 x : (invr x = zeror) <=> (x = zeror).
  proof. by apply/iff_negb; split=> /invr_neq0; rewrite ?invrK. qed.

  lemma nosmt invr_eq1 x : (invr x = oner) <=> (x = oner).
  proof. by rewrite (inv_eq invrK) invr1. qed.

  op ofint n = intmul oner n.

  lemma ofint0: ofint 0 = zeror.
  proof. by apply/mulr0z. qed.

  lemma ofint1: ofint 1 = oner.
  proof. by apply/mulr1z. qed.

  lemma ofintS (i : int): 0 <= i => ofint (i+1) = oner + ofint i.
  proof. by apply/mulrS. qed.

  lemma ofintN (i : int): ofint (-i) = - (ofint i).
  proof. by apply/mulrNz. qed.

  lemma mul1r0z x: x * ofint 0 = zeror.
  proof. by rewrite ofint0 mulr0. qed.

  lemma mul1r1z x : x * ofint 1 = x.
  proof. by rewrite ofint1 mulr1. qed.

  lemma mul1r2z x : x * ofint 2 = x + x.
  proof. by rewrite /ofint mulr2z mulrDr mulr1. qed.

  lemma mulr_intl x z : (ofint z) * x = intmul x z.
  proof. by rewrite mulrzAl mul1r. qed.

  lemma mulr_intr x z : x * (ofint z) = intmul x z.
  proof. by rewrite mulrzAr mulr1. qed.

  op exp (x : t) (n : int) =
    if   n < 0
    then invr (iterop (-n) ComRing.( * ) x oner)
    else iterop n ComRing.( * ) x oner.

  lemma expr0 x: exp x 0 = oner.
  proof. by rewrite /exp /= iterop0. qed.

  lemma expr1 x: exp x 1 = x.
  proof. by rewrite /exp /= iterop1. qed.

  lemma exprS (x : t) i: 0 <= i => exp x (i+1) = x * (exp x i).
  proof.
    move=> ge0i; rewrite /exp !ltzNge ge0i addz_ge0 //=.
    by rewrite !MulMonoid.iteropE iterS.
  qed.

  lemma expr2 x: exp x 2 = x * x.
  proof. by rewrite (@exprS _ 1) // expr1. qed.

  lemma exprN (x : t) (i : int): exp x (-i) = invr (exp x i).
  proof.
    case: (i = 0) => [->|]; first by rewrite oppz0 expr0 invr1.
    rewrite /exp oppz_lt0 ltzNge lez_eqVlt oppzK=> -> /=.
    by case: (_ < _)=> //=; rewrite invrK.
  qed.

  lemma signr_odd n : 0 <= n => exp (-oner) (b2i (odd n)) = exp (-oner) n.
  proof.
    elim: n => [|n ge0_nih]; first by rewrite odd0 expr0.
    rewrite !(iterS, oddS) // exprS // -/(odd _) => <-.
    by case: (odd _); rewrite /b2i /= !(expr0, expr1) mulN1r ?opprK.
  qed.

  lemma subr_sqr_1 x : exp x 2 - oner = (x - oner) * (x + oner).
  proof.
  rewrite mulrBl mulrDr !(mulr1, mul1r) !subrE expr2 -addrA.
  by congr; rewrite opprD addrA addrN add0r.
  qed.
end ComRing.

(* -------------------------------------------------------------------- *)
abstract theory BoolRing.
  type t.

  clone include ComRing with type t <- t.

  axiom mulrr : forall (x : t), x * x = x.

  lemma nosmt addrr (x : t): x + x = zeror.
  proof.
    apply (@addrI (x + x)); rewrite addr0 -{1 2 3 4}mulrr.
    by rewrite -mulrDr -mulrDl mulrr.
  qed.
end BoolRing.

(* -------------------------------------------------------------------- *)
abstract theory IDomain.
  type t.

  clone include ComRing with type t <- t.

  axiom mulf_eq0:
    forall (x y : t), x * y = zeror <=> x = zeror \/ y = zeror.

  lemma mulf_neq0 (x y : t): x <> zeror => y <> zeror => x * y <> zeror.
  proof. by move=> nz_x nz_y; apply/not_def; rewrite mulf_eq0; smt. qed.

  lemma mulfI (x : t): x <> zeror => injective (( * ) x).
  proof.
    move=> ne0_x y y'; rewrite -(opprK (x * y')) -mulrN -addr_eq0.
    by rewrite -mulrDr mulf_eq0 ne0_x /= addr_eq0 opprK.
  qed.

  lemma mulIf x: x <> zeror => injective (fun y => y * x).
  proof. by move=> nz_x y z; rewrite -!(@mulrC x); exact: mulfI. qed.

  lemma sqrf_eq1 x : (exp x 2 = oner) <=> (x = oner \/ x = -oner).
  proof. by rewrite -subr_eq0 subr_sqr_1 mulf_eq0 subr_eq0 addr_eq0. qed.
end IDomain.

(* -------------------------------------------------------------------- *)
abstract theory Field.
  type t.

  clone include IDomain with type t <- t, pred unit (x : t) <- x <> zeror.

  lemma mulfV (x : t): x <> zeror => x * (invr x) = oner.
  proof. by apply/mulrV. qed.

  lemma mulVf (x : t): x <> zeror => (invr x) * x = oner.
  proof. by apply/mulVr. qed.

  lemma nosmt divff (x : t): x <> zeror => x / x = oner.
  proof. by apply/divrr. qed.
end Field.

(* --------------------------------------------------------------------- *)
abstract theory Additive.
  type t1, t2.

  clone import Self.ZModule as ZM1 with type t <- t1.
  clone import Self.ZModule as ZM2 with type t <- t2.

  pred additive (f : t1 -> t2) =
    forall (x y : t1), f (x - y) = f x - f y.

  op f : { t1 -> t2 | additive f } as f_is_additive.

  lemma raddf0: f ZM1.zeror = ZM2.zeror.
  proof. by rewrite -ZM1.subr0 f_is_additive ZM2.subrr. qed.

  lemma raddfB (x y : t1): f (x - y) = f x - f y.
  proof. by apply/f_is_additive. qed.

  lemma raddfN (x : t1): f (- x) = - (f x).
  proof. by rewrite -ZM1.sub0r raddfB raddf0 ZM2.sub0r. qed.

  lemma raddfD (x y : t1): f (x + y) = f x + f y.
  proof.
    rewrite -{1}(@ZM1.opprK y) -ZM1.subrE raddfB raddfN.
    by rewrite ZM2.subrE ZM2.opprK.
  qed.
end Additive.

(* --------------------------------------------------------------------- *)
abstract theory Multiplicative.
  type t1, t2.

  clone import Self.ComRing as ZM1 with type t <- t1.
  clone import Self.ComRing as ZM2 with type t <- t2.

  pred multiplicative (f : t1 -> t2) =
       f ZM1.oner = ZM2.oner
    /\ forall (x y : t1), f (x * y) = f x * f y.
end Multiplicative.

(* --------------------------------------------------------------------- *)
(* Rewrite database for algebra tactic                                   *)

hint rewrite rw_algebra  : .
hint rewrite inj_algebra : .

(* -------------------------------------------------------------------- *)
theory IntID.
clone include IDomain with
  type t <- int,
  pred unit (z : int) <- (z = 1 \/ z = -1),
  op   zeror <- 0,
  op   oner  <- 1,
  op   ( + ) <- Int.( + ),
  op   [ - ] <- Int.([-]),
  op   ( - ) <- Int.( - ),
  op   ( * ) <- Int.( * ),
  op   ( / ) <- Int.( * ),
  op   invr  <- (fun (z : int) => z)
  proof * by smt.

lemma intmulz z c : intmul z c = z * c.
proof.
have h: forall cp, 0 <= cp => intmul z cp = z * cp.
  elim=> /= [|cp ge0_cp ih].
    by rewrite mulr0z.
  by rewrite mulrS // ih mulrDr /= addrC.
case: (c < 0); 1: rewrite -opprK mulrNz opprK; smt.
qed.
end IntID.
