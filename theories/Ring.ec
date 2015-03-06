(* --------------------------------------------------------------------
 * Copyright (c) - 2012-2015 - IMDEA Software Institute and INRIA
 * Distributed under the terms of the CeCILL-C license
 * -------------------------------------------------------------------- *)

pragma +implicits.

(* -------------------------------------------------------------------- *)
require import Fun Int IntExtra.

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

  op ( - ) (x y : t) = x + -y axiomatized by subrE.

  lemma nosmt addr0: right_id zeror (+).
  proof. by move=> x; rewrite addrC add0r. qed.

  lemma nosmt addrN: right_inverse zeror [-] (+).
  proof. by move=> x; rewrite addrC addNr. qed.

  lemma nosmt addrCA: left_commutative (+).
  proof. by move=> x y z; rewrite !addrA @(addrC x y). qed.

  lemma nosmt addrAC: right_commutative (+).
  proof. by move=> x y z; rewrite -!addrA @(addrC y z). qed.

  lemma nosmt subrr (x : t): x - x = zeror.
  proof. by rewrite subrE /= addrN. qed.

  lemma nosmt addKr: left_loop [-] (+).
  proof. by move=> x y; rewrite addrA addNr add0r. qed.

  lemma nosmt addNKr: rev_left_loop [-] (+).
  proof. by move=> x y; rewrite addrA addrN add0r. qed.

  lemma nosmt addrK: right_loop [-] (+).
  proof. by move=> x y; rewrite -addrA addrN addr0. qed.

  lemma nosmt addrNK: rev_right_loop [-] (+).
  proof. by move=> x y; rewrite -addrA addNr addr0. qed.

  lemma nosmt addrI: right_injective (+).
  proof. by move=> x y z h; rewrite -@(addKr x z) -h addKr. qed.

  lemma nosmt addIr: left_injective (+).
  proof. by move=> x y z h; rewrite -@(addrK x z) -h addrK. qed.

  lemma nosmt opprK: involutive [-].
  proof. by move=> x; apply @(addIr (-x)); rewrite addNr addrN. qed.

  lemma nosmt oppr0: -zeror = zeror.
  proof. by rewrite -@(addr0 (-zeror)) addNr. qed.

  lemma nosmt subr0 (x : t): x - zeror = x.
  proof. by rewrite subrE /= oppr0 addr0. qed.

  lemma nosmt sub0r (x : t): zeror - x = - x.
  proof. by rewrite subrE /= add0r. qed.

  lemma nosmt opprD (x y : t): -(x + y) = -x + -y.
  proof. by apply @(addrI (x + y)); rewrite addrA addrN addrAC addrK addrN. qed.

  lemma nosmt opprB (x y : t): -(x - y) = y - x.
  proof. by rewrite !subrE opprD opprK addrC. qed.

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
  proof. by rewrite -@(subr_eq0 x) subrE /= opprK. qed.

  lemma nosmt eqr_opp (x y : t): (- x = - y) <=> (x = y).
  proof.
    move: (can_eq (fun (z : t), -z) (fun (z : t), -z) _ x y) => //=.
    by move=> z /=; rewrite opprK.
  qed.

  op intmul (x : t) (n : int) =
    if n < 0
    then -(iterop (-n) ZModule.(+) x zeror)
    else  (iterop   n  ZModule.(+) x zeror).

  lemma intmul0 (x : t): intmul x 0 = zeror.
  proof. by rewrite /intmul /= iterop0. qed.

  lemma intmul1 (x : t): intmul x 1 = x.
  proof. by rewrite /intmul /= iterop1. qed.

  lemma intmulN (x : t) (n : int): intmul x (-n) = -(intmul x n).
  proof.
    case: (n = 0)=> [-> |nz_n]; 1: by rewrite oppz0 intmul0 oppr0.
    rewrite /intmul; have ->: -n < 0 <=> !(n < 0) by smt.
    by case: (n < 0)=> //= _; rewrite ?(opprK, oppzK).
  qed.

  lemma intmulS (x : t) (n : int): 0 <= n =>
    intmul x (n+1) = x + intmul x n.
  proof.
    by elim: n=> /= [|i ge0_i ih]; 2: smt; rewrite intmul0 intmul1 addr0.
  qed.
end ZModule.

(* -------------------------------------------------------------------- *)
clone ZModule as IntZMod with
  type t <- int,
  op   zeror <- 0,
  op   (+)   <- Int.( + ),
  op   [-]   <- Int.([-]),
  op   (-)   <- Int.( - )
  proof *.

realize addrA. by smt. qed.
realize addrC. by smt. qed.
realize add0r. by smt. qed.
realize addNr. by smt. qed.
realize subrE. by smt. qed.

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

  lemma nosmt mulr1: right_id oner ( * ).
  proof. by move=> x; rewrite mulrC mul1r. qed.

  lemma nosmt mulrDr: right_distributive ( * ) (+).
  proof. by move=> x y z; rewrite mulrC mulrDl !@(mulrC _ x). qed.

  lemma nosmt mul0r: left_zero zeror ( * ).
  proof. by move=> x; apply: @(addIr (oner * x)); rewrite -mulrDl !add0r mul1r. qed.

  lemma nosmt mulr0: right_zero zeror ( * ).
  proof. by move=> x; apply: @(addIr (x * oner)); rewrite -mulrDr !add0r mulr1. qed.

  lemma nosmt mulrN (x y : t): x * (- y) = - (x * y).
  proof. by apply: @(addrI (x * y)); rewrite -mulrDr !addrN mulr0. qed.

  lemma nosmt mulNr (x y : t): (- x) * y = - (x * y).
  proof. by apply: @(addrI (x * y)); rewrite -mulrDl !addrN mul0r. qed.

  lemma nosmt mulrNN (x y : t): (- x) * (- y) = x * y.
  proof. by rewrite mulrN mulNr opprK. qed.

  lemma nosmt mulN1r (x : t): (-oner) * x = -x.
  proof. by rewrite mulNr mul1r. qed.

  lemma nosmt mulrN1 x: x * -oner = -x.
  proof. by rewrite mulrN mulr1. qed.

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

  (* FIXME: have := can_inj _ _ (mulKr _ Ux) *)
  lemma nosmt mulrI: right_injective_in unit ( * ).
  proof. by move=> x Ux; have /can_inj h := mulKr _ Ux. qed.

  lemma nosmt mulIr: left_injective_in unit ( * ).
  proof. by move=> x /mulrI h y1 y2; rewrite !@(mulrC _ x) => /h. qed.

  lemma nosmt unitrE (x : t): unit x <=> (x / x = oner).
  proof.
    split=> [Ux|xx1]; 1: by apply/divrr.
    by apply/unitrP; exists (invr x); rewrite mulrC -divrE.
  qed.

  lemma invrK: involutive invr.
  proof.
    move=> x; case: (unit x)=> Ux; 2: by rewrite !invr_out.
    rewrite -(mulrK _ Ux (invr (invr x))) -mulrA.
    rewrite @(mulrC x) mulKr //; apply/unitrP.
    by exists x; rewrite mulrV.
  qed.

  lemma nosmt invr_inj: injective invr.
  proof. by apply: (can_inj invrK). qed.

  lemma nosmt unitrV x: unit (invr x) <=> unit x.
  proof. by rewrite !unitrE !divrE invrK mulrC. qed.

  lemma nosmt unitr1: unit oner.
  proof. by apply/unitrP; exists oner; rewrite mulr1. qed.

  lemma invr1: invr oner = oner.
  proof. by rewrite -{2}(mulVr _ unitr1) mulr1. qed.

  lemma div1r x: oner / x = invr x.
  proof. by rewrite divrE mul1r. qed.

  lemma divr1 x: x / oner = x.
  proof. by rewrite divrE invr1 mulr1. qed.

  lemma nosmt unitr0: !unit zeror.
  proof. by apply/negP=> /unitrP [y]; rewrite mulr0 eq_sym oner_neq0. qed.

  lemma invr0: invr zeror = zeror.
  proof. by rewrite invr_out ?unitr0. qed.

  lemma nosmt unitrN1: unit (-oner).
  proof. by apply/unitrP; exists (-oner); rewrite mulrNN mulr1. qed.

  lemma nosmt invrN1: invr (-oner) = -oner.
  proof. by rewrite -{2}(divrr unitrN1) divrE mulN1r opprK. qed.

  op ofint n = intmul oner n.

  lemma ofint0: ofint 0 = zeror.
  proof. by apply/intmul0. qed.

  lemma ofint1: ofint 1 = oner.
  proof. by apply/intmul1. qed.

  lemma ofintS (i : int): 0 <= i => ofint (i+1) = oner + ofint i.
  proof. by apply/intmulS. qed.

  lemma ofintN (i : int): ofint (-i) = - (ofint i).
  proof. by apply/intmulN. qed.

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
    by elim: i=> /= [|i ge0_i ih]; 2: smt; rewrite expr0 expr1 mulr1.
  qed.

  lemma exprN (x : t) (i : int): exp x (-i) = invr (exp x i).
  proof. case: (i = 0); smt. qed.
end ComRing.

(* -------------------------------------------------------------------- *)
abstract theory BoolRing.
  type t.

  clone include ComRing with type t <- t.

  axiom mulrr : forall (x : t), x * x = x.

  lemma nosmt addrr (x : t): x + x = zeror.
  proof.
    apply @(addrI (x + x)); rewrite addr0 -{1 2 3 4}mulrr.
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
  proof. admit. qed.

  lemma mulIf x: x <> zeror => injective (fun y => y * x).
  proof. by move=> nz_x y z; rewrite -!@(mulrC x); exact: mulfI. qed.
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
    rewrite -{1}@(ZM1.opprK y) -ZM1.subrE raddfB raddfN.
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
