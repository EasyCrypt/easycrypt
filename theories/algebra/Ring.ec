(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

pragma +implicits.

(* -------------------------------------------------------------------- *)
require import Core Int.
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

  clear [AddMonoid.Axioms.*].

  abbrev ( - ) (x y : t) = x + -y.

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
  proof. by rewrite addrN. qed.

  lemma nosmt addKr: left_loop [-] (+).
  proof. by move=> x y; rewrite addrA addNr add0r. qed.

  lemma nosmt addNKr: rev_left_loop [-] (+).
  proof. by move=> x y; rewrite addrA addrN add0r. qed.

  lemma nosmt addrK: right_loop [-] (+).
  proof. by move=> x y; rewrite -addrA addrN addr0. qed.

  lemma nosmt addrNK: rev_right_loop [-] (+).
  proof. by move=> x y; rewrite -addrA addNr addr0. qed.

  lemma nosmt subrK x y: (x - y) + y = x.
  proof. by rewrite addrNK. qed.

  lemma nosmt addrI: right_injective (+).
  proof. by move=> x y z h; rewrite -(@addKr x z) -h addKr. qed.

  lemma nosmt addIr: left_injective (+).
  proof. by move=> x y z h; rewrite -(@addrK x z) -h addrK. qed.

  lemma nosmt opprK: involutive [-].
  proof. by move=> x; apply (@addIr (-x)); rewrite addNr addrN. qed.

  lemma oppr_inj : injective [-].
  proof. by move=> x y eq; apply/(addIr (-x)); rewrite subrr eq subrr. qed.

  lemma nosmt oppr0: -zeror = zeror.
  proof. by rewrite -(@addr0 (-zeror)) addNr. qed.

  lemma oppr_eq0 x : (- x = zeror) <=> (x = zeror).
  proof. by rewrite (inv_eq opprK) oppr0. qed.

  lemma nosmt subr0 (x : t): x - zeror = x.
  proof. by rewrite oppr0 addr0. qed.

  lemma nosmt sub0r (x : t): zeror - x = - x.
  proof. by rewrite add0r. qed.

  lemma nosmt opprD (x y : t): -(x + y) = -x + -y.
  proof. by apply (@addrI (x + y)); rewrite addrA addrN addrAC addrK addrN. qed.

  lemma nosmt opprB (x y : t): -(x - y) = y - x.
  proof. by rewrite opprD opprK addrC. qed.

  lemma nosmt subrACA: interchange (-) (+).
  proof. by move=> x y z t; rewrite addrACA opprD. qed.

  lemma nosmt subr_eq (x y z : t):
    (x - z = y) <=> (x = y + z).
  proof.
    move: (can2_eq (fun x, x - z) (fun x, x + z) _ _ x y) => //=.
    by move=> {x} x /=; rewrite addrNK.
    by move=> {x} x /=; rewrite addrK.
  qed.

  lemma nosmt subr_eq0 (x y : t): (x - y = zeror) <=> (x = y).
  proof. by rewrite subr_eq add0r. qed.

  lemma nosmt addr_eq0 (x y : t): (x + y = zeror) <=> (x = -y).
  proof. by rewrite -(@subr_eq0 x) opprK. qed.

  lemma nosmt eqr_opp (x y : t): (- x = - y) <=> (x = y).
  proof. by apply/(@can_eq _ _ opprK x y). qed.

  lemma eqr_oppLR x y : (- x = y) <=> (x = - y).
  proof. by apply/(@inv_eq _ opprK x y). qed.

  lemma nosmt eqr_sub (x y z t : t) : (x - y = z - t) <=> (x + t = z + y).
  proof.
  rewrite -{1}(addrK t x) -{1}(addrK y z) -!addrA.
  by rewrite (addrC (-t)) !addrA; split=> [/addIr /addIr|->//].
  qed.

  lemma subr_add2r (z x y : t): (x + z) - (y + z) = x - y.
  proof. by rewrite opprD addrACA addrN addr0. qed.

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

  lemma mulNrz x n : intmul (- x) n = - (intmul x n).
  proof.
  elim/intwlog: n => [n h| | n ge0_n ih].
  + by rewrite -(@oppzK n) !(@mulrNz _ (- n)) h.
  + by rewrite !mulr0z oppr0.
  + by rewrite !mulrS // ih opprD.
  qed.

  lemma mulNrNz x (n : int) : intmul (-x) (-n) = intmul x n.
  proof. by rewrite mulNrz mulrNz opprK. qed.

  lemma mulrSz x n : intmul x (n + 1) = x + intmul x n.
  proof.
  case: (0 <= n) => [/mulrS ->//|]; rewrite -ltzNge => gt0_n.
  case: (n = -1) => [->/=|]; 1: by rewrite mulrNz mulr1z mulr0z subrr.
  move=> neq_n_N1; rewrite -!(@mulNrNz x).
  rewrite (_ : -n = -(n+1) + 1) 1:/# mulrS 1:/#.
  by rewrite addrA subrr add0r.
  qed.

  lemma mulrDz (x : t) (n m : int) : intmul x (n + m) = intmul x n + intmul x m.
  proof.
  wlog: n m / 0 <= m => [wlog|].
  + case: (0 <= m) => [/wlog|]; first by apply.
    rewrite -ltzNge => lt0_m; rewrite (_ : n + m = -(-m - n)) 1:/#.
    by rewrite mulrNz addzC wlog 1:/# !mulrNz -opprD opprK.
  elim: m => /= [|m ge0_m ih]; first by rewrite mulr0z addr0.
  by rewrite addzA !mulrSz ih addrCA.
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

  abbrev ( / ) (x y : t) = x * (invr y).

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

  clear [MulMonoid.Axioms.*].

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
  proof. by move=> x y z; rewrite mulrDl !mulNr. qed.

  lemma nosmt mulrBr: right_distributive ( * ) (-).
  proof. by move=> x y z; rewrite mulrDr !mulrN. qed.

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
  proof. by apply/mulrV. qed.

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
    by apply/unitrP; exists (invr x); rewrite mulrC.
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
  proof. by rewrite !unitrE invrK mulrC. qed.

  lemma nosmt unitr1: unit oner.
  proof. by apply/unitrP; exists oner; rewrite mulr1. qed.

  lemma nosmt invr1: invr oner = oner.
  proof. by rewrite -{2}(mulVr _ unitr1) mulr1. qed.

  lemma nosmt div1r x: oner / x = invr x.
  proof. by rewrite mul1r. qed.

  lemma nosmt divr1 x: x / oner = x.
  proof. by rewrite invr1 mulr1. qed.

  lemma nosmt unitr0: !unit zeror.
  proof. by apply/negP=> /unitrP [y]; rewrite mulr0 eq_sym oner_neq0. qed.

  lemma nosmt invr0: invr zeror = zeror.
  proof. by rewrite invr_out ?unitr0. qed.

  lemma nosmt unitrN1: unit (-oner).
  proof. by apply/unitrP; exists (-oner); rewrite mulrNN mulr1. qed.

  lemma nosmt invrN1: invr (-oner) = -oner.
  proof. by rewrite -{2}(divrr unitrN1) mulN1r opprK. qed.

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

  lemma nosmt unitrM x y : unit (x * y) <=> (unit x /\ unit y).
  proof.
  case: (unit x) => /=; first by apply: unitrMr.
  apply: contra => /unitrP[z] zVE; apply/unitrP.
  by exists (y * z); rewrite mulrAC (@mulrC y) (@mulrC _ z).
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
    by case: (_ < _)%Int => //=; rewrite invrK.
  qed.

  lemma exprN1 (x : t) : exp x (-1) = invr x.
  proof. by rewrite exprN expr1. qed.

  lemma unitrX x m : unit x => unit (exp x m).
  proof.
  move=> invx; wlog: m / (0 <= m) => [wlog|].
  + (have [] : (0 <= m \/ 0 <= -m) by move=> /#); first by apply: wlog.    
    by move=> ?; rewrite -oppzK exprN unitrV &(wlog).
  elim: m => [|m ge0_m ih]; first by rewrite expr0 unitr1.
  by rewrite exprS // &(unitrMl).
  qed.

  lemma unitrX_neq0 x m : m <> 0 => unit (exp x m) => unit x.
  proof.
  wlog: m / (0 < m) => [wlog|].
  + case: (0 < m); [by apply: wlog | rewrite ltzNge /= => le0_m nz_m].
    by move=> h; (apply: (wlog (-m)); 1,2:smt()); rewrite exprN unitrV.
  by move=> gt0_m _; rewrite (_ : m = m - 1 + 1) // exprS 1:/# unitrM.
  qed.

  lemma exprV (x : t) (i : int): exp (invr x) i = exp x (-i).
  proof.
  wlog: i / (0 <= i) => [wlog|]; first by smt(exprN).
  elim: i => /= [|i ge0_i ih]; first by rewrite !expr0.
  case: (i = 0) => [->|] /=; first by rewrite exprN1 expr1.
  move=> nz_i; rewrite exprS // ih !exprN.
  case: (unit x) => [invx|invNx].
  + by rewrite -invrM ?unitrX // exprS // mulrC.
  rewrite !invr_out //; last by rewrite exprS.
  + by apply: contra invNx; apply: unitrX_neq0 => /#.
  + by apply: contra invNx; apply: unitrX_neq0 => /#.
  qed.

  lemma exprDn x (m n : int) : 0 <= m => 0 <= n =>
    exp x (m + n) = exp x m * exp x n.
  proof.
    move=> ge0_m ge0_n; elim: m ge0_m => [|m ge0_m ih].
      by rewrite expr0 mul1r.    
    by rewrite addzAC !exprS ?addz_ge0 // ih mulrA.
  qed.

  lemma exprDNz x (m n : int) : m <= 0 => n <= 0 =>
    exp x (m + n) = exp x m * exp x n.
  proof.
    move=> ge0_m ge0_n; rewrite -{2}(@oppzK m) -{2}(@oppzK n).
    by rewrite -!(@exprV _ (- _)%Int) -exprDn 1?exprV //#.
  qed.

  lemma exprD x (m n : int) : unit x => exp x (m + n) = exp x m * exp x n.
  proof.
  wlog: m n x / (0 <= m + n) => [wlog invx|].
  + case: (0 <= m + n); [by move=> ?; apply: wlog | rewrite lezNgt /=].
    move=> lt0_mDn; rewrite -(@oppzK (m + n)) -exprV.
    rewrite -{2}(@oppzK m) -{2}(@oppzK n) -!(@exprV _ (- _)%Int).
    by rewrite -wlog 1:/# ?unitrV //#.
  move=> ge0_mDn invx; wlog: m n ge0_mDn / (m <= n) => [wlog|le_mn].
  + by case: (m <= n); [apply: wlog | rewrite mulrC addzC /#].
  (have ge0_n: 0 <= n by move=> /#); elim: n ge0_n m le_mn ge0_mDn.
  + by move=> n _ _ /=; rewrite expr0 mulr1.
  move=> n ge0_n ih m le_m_Sn ge0_mDSn; move: ge0_mDSn.
  rewrite lez_eqVlt => -[?|]; first have->: n+1 = -m by move=> /#.
  + by rewrite subzz exprN expr0 divrr // unitrX.
  move=> gt0_mDSn; move: le_m_Sn; rewrite lez_eqVlt.
  case=> [->>|lt_m_Sn]; first by rewrite exprDn //#.
  by rewrite addzA exprS 1:/# ih 1,2:/# exprS // mulrCA.
  qed.

  lemma exprM x (m n : int) : 
    exp x (m * n) = exp (exp x m) n.
  proof.
  wlog : n / 0 <= n.
  + move=> h; case: (0 <= n) => hn; 1: by apply h.
    by rewrite -{1}(@oppzK n) (_: m * - -n = -(m * -n)) 1:/#
      exprN h 1:/# exprN invrK.
  wlog : m / 0 <= m.
  + move=> h; case: (0 <= m) => hm hn; 1: by apply h.
    rewrite -{1}(@oppzK m) (_: (- -m) * n = - (-m) * n) 1:/#.
    by rewrite exprN h 1:/# // exprN exprV exprN invrK.
  elim /natind: n; 1: smt (expr0).
  by move=> n hn ih hm _; rewrite mulzDr exprS //= mulrC exprDn 1:/# 1:// ih.
  qed.

  lemma expr0n n : 0 <= n => exp zeror n = if n = 0 then oner else zeror.
  proof.
  elim: n => [|n ge0_n _]; first by rewrite expr0.
  by rewrite exprS // mul0r addz1_neq0.
  qed.

  lemma expr0z z : exp zeror z = if z = 0 then oner else zeror.
  proof.
  case: (0 <= z) => [/expr0n // | /ltzNge lt0_z].
  rewrite -{1}(@oppzK z) exprN; have ->/=: z <> 0 by smt().
  rewrite invr_eq0 expr0n ?oppz_ge0 1:ltzW //.
  by have ->/=: -z <> 0 by smt().
  qed.

  lemma expr1z z : exp oner z = oner.
  proof.
  elim/intwlog: z.
  + by move=> n h; rewrite -(@oppzK n) exprN h invr1.
  + by rewrite expr0.
  + by move=> n ge0_n ih; rewrite exprS // mul1r ih.
  qed.

  lemma sqrrD x y :
    exp (x + y) 2 = exp x 2 + intmul (x * y) 2 + exp y 2.
  proof.
  by rewrite !expr2 mulrDl !mulrDr mulr2z !addrA (@mulrC y x).
  qed.

  lemma sqrrN x : exp (-x) 2 = exp x 2.
  proof. by rewrite !expr2 mulrNN. qed.

  lemma sqrrB x y :
    exp (x - y) 2 = exp x 2 - intmul (x * y) 2 + exp y 2.
  proof.   by rewrite sqrrD sqrrN mulrN mulNrz. qed.

  lemma signr_odd n : 0 <= n => exp (-oner) (b2i (odd n)) = exp (-oner) n.
  proof.
    elim: n => [|n ge0_nih]; first by rewrite odd0 expr0 expr0.
    rewrite !(iterS, oddS) // exprS // -/(odd _) => <-.
    by case: (odd _); rewrite /b2i /= !(expr0, expr1) mulN1r ?opprK.
  qed.

  lemma subr_sqr_1 x : exp x 2 - oner = (x - oner) * (x + oner).
  proof.
  rewrite mulrBl mulrDr !(mulr1, mul1r) expr2 -addrA.
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
  proof. by move=> nz_x nz_y; apply/negP; rewrite mulf_eq0; smt. qed.

  lemma expf_eq0 x n : (exp x n = zeror) <=> (n <> 0 /\ x = zeror).
  proof.
  elim/intwlog: n => [n| |n ge0_n ih].
  + by rewrite exprN invr_eq0 /#.
  + by rewrite expr0 oner_neq0.
  by rewrite exprS // mulf_eq0 ih addz1_neq0 ?andKb.
  qed.

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

  lemma nosmt invfM (x y : t) : invr (x * y) = invr x * invr y.
  proof.
  case: (x = zeror) => [->|nz_x]; first by rewrite !(mul0r, invr0).
  case: (y = zeror) => [->|nz_y]; first by rewrite !(mulr0, invr0).
  by rewrite invrM // mulrC.
  qed.

  lemma invf_div x y : invr (x / y) = y / x.
  proof. by rewrite invfM invrK mulrC. qed.

  lemma eqf_div (x1 y1 x2 y2 : t) : y1 <> zeror => y2 <> zeror =>
    (x1 / y1 = x2 / y2) <=> (x1 * y2 = x2 * y1).
  proof.                          (* FIXME: views *)
  move=> nz_y1 nz_y2; rewrite -{1}(@mulrK y2 _ x1) //.
  rewrite  -{1}(@mulrK y1 _ x2) // -!mulrA (@mulrC (invr y1)) !mulrA.
  split=> [|->] //;
    (have nz_Vy1: invr y1 <> zeror by rewrite invr_eq0);
    (have nz_Vy2: invr y2 <> zeror by rewrite invr_eq0).
  by move/(mulIf _ nz_Vy1)/(mulIf _ nz_Vy2).
  qed.

  lemma expfM x y n : exp (x * y) n = exp x n * exp y n.
  proof.
  elim/intwlog: n => [n h | | n ge0_n ih].
  + by rewrite -(@oppzK n) !(@exprN _ (-n)) h invfM.
  + by rewrite !expr0 mulr1.
  + by rewrite !exprS // mulrCA -!mulrA -ih mulrCA.
  qed.
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
  proof. by rewrite -{1}(@ZM1.opprK y) raddfB raddfN ZM2.opprK. qed.
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
  op   ( * ) <- Int.( * ),
  op   invr  <- (fun (z : int) => z)
  proof * by smt
  remove abbrev (-)
  remove abbrev (/)
  rename "ofint" as "ofint_id".

abbrev (^) = exp.

lemma intmulz z c : intmul z c = z * c.
proof.
have h: forall cp, 0 <= cp => intmul z cp = z * cp.
  elim=> /= [|cp ge0_cp ih].
    by rewrite mulr0z.
  by rewrite mulrS // ih mulrDr /= addrC.
case: (c < 0); 1: rewrite -opprK mulrNz opprK; smt.
qed.

lemma poddX n x : 0 < n => odd (exp x n) = odd x.
proof.
rewrite ltz_def => - [] + ge0_n; elim: n ge0_n => // + + _ _.
elim=> [|n ge0_n ih]; first by rewrite expr1.
by rewrite exprS ?addz_ge0 // oddM ih andbb.
qed.

lemma oddX n x : 0 <= n => odd (exp x n) = (odd x \/ n = 0).
proof.
rewrite lez_eqVlt; case: (n = 0) => [->// _|+ h].
+ by rewrite expr0 odd1.
+ by case: h => [<-//|] /poddX ->.
qed.
end IntID.
