pragma +implicits.

(* -------------------------------------------------------------------- *)
require import Core Int IntDiv.
require import TcMonoid.

(* ==================================================================== *)
(* Additive group: extends [addmonoid] with negation. Carrier of all
   ZModule lemmas in the original [theories/algebra/Ring.ec].           *)
(* ==================================================================== *)
type class addgroup <: addmonoid = {
  op [-] : addgroup -> addgroup

  axiom addrN : right_inverse zero<:addgroup> [-] (+)<:addgroup>
}.

(* -------------------------------------------------------------------- *)
section.
declare type t <: addgroup.

(* Re-export the inherited addmonoid axioms under the conventional
   ring-theoretic names. *)
lemma addrA: associative (+)<:t>.
proof. exact addmA. qed.

lemma addrC: commutative (+)<:t>.
proof. exact addmC. qed.

lemma add0r: left_id zero<:t> (+)<:t>.
proof. exact add0m. qed.

(* The original [Ring.ec] takes [addNr] as the additive group axiom and
   derives [addrN] from it; here we take [addrN] (right inverse) and
   derive [addNr] (left inverse) instead. *)
lemma addNr: left_inverse zero<:t> [-] (+)<:t>.
proof. by move=> x; rewrite addrC addrN. qed.

abbrev (-) (x y : t) = x + -y.

lemma addr0: right_id zero<:t> (+).
proof. exact addm0. qed.

lemma addrCA: left_commutative (+)<:t>.
proof. exact addmCA. qed.

lemma addrAC: right_commutative (+)<:t>.
proof. exact addmAC. qed.

lemma addrACA: interchange (+)<:t> (+).
proof. exact addmACA. qed.

lemma subrr (x : t): x - x = zero.
proof. by rewrite addrN. qed.

hint simplify subrr.

lemma addKr: left_loop ([-]<:t>) (+).
proof. by move=> x y; rewrite addrA addNr add0r. qed.

lemma addNKr: rev_left_loop ([-]<:t>) (+).
proof. by move=> x y; rewrite addrA addrN add0r. qed.

lemma addrK: right_loop ([-]<:t>) (+).
proof. by move=> x y; rewrite -addrA addrN addr0. qed.

lemma addrNK: rev_right_loop ([-]<:t>) (+).
proof. by move=> x y; rewrite -addrA addNr addr0. qed.

lemma subrK (x y : t): (x - y) + y = x.
proof. by rewrite addrNK. qed.

lemma addrI: right_injective (+)<:t>.
proof. by move=> x y z h; rewrite -(@addKr x z) -h addKr. qed.

lemma addIr: left_injective (+)<:t>.
proof. by move=> x y z h; rewrite -(@addrK x z) -h addrK. qed.

lemma opprK: involutive ([-]<:t>).
proof. by move=> x; apply (@addIr (-x)); rewrite addNr addrN. qed.

lemma oppr_inj : injective ([-]<:t>).
proof. by move=> x y eq; apply/(addIr (-x)); rewrite subrr eq subrr. qed.

lemma oppr0 : -zero<:t> = zero.
proof. by rewrite -(@addr0 (-zero)) addNr. qed.

lemma oppr_eq0 (x : t) : (- x = zero) <=> (x = zero).
proof. by rewrite (inv_eq opprK) oppr0. qed.

lemma subr0 (x : t): x - zero = x.
proof. by rewrite oppr0 addr0. qed.

lemma sub0r (x : t): zero - x = - x.
proof. by rewrite add0r. qed.

lemma opprD (x y : t): -(x + y) = -x + -y.
proof. by apply (@addrI (x + y)); rewrite addrA addrN addrAC addrK addrN. qed.

lemma opprB (x y : t): -(x - y) = y - x.
proof. by rewrite opprD opprK addrC. qed.

lemma subrACA: interchange (fun (x y : t) => x - y) (+).
proof. by move=> x y z u; rewrite addrACA opprD. qed.

lemma subr_eq (x y z : t):
  (x - z = y) <=> (x = y + z).
proof.
move: (can2_eq (fun x, x - z) (fun x, x + z) _ _ x y) => //=.
+ by move=> {x} x /=; rewrite addrNK.
+ by move=> {x} x /=; rewrite addrK.
qed.

lemma subr_eq0 (x y : t): (x - y = zero) <=> (x = y).
proof. by rewrite subr_eq add0r. qed.

lemma addr_eq0 (x y : t): (x + y = zero) <=> (x = -y).
proof. by rewrite -(@subr_eq0 x) opprK. qed.

lemma eqr_opp (x y : t): (- x = - y) <=> (x = y).
proof. by apply/(@can_eq _ _ opprK x y). qed.

lemma eqr_oppLR (x y : t) : (- x = y) <=> (x = - y).
proof. by apply/(@inv_eq _ opprK x y). qed.

lemma eqr_sub (x y z u : t) : (x - y = z - u) <=> (x + u = z + y).
proof.
rewrite -{1}(addrK u x) -{1}(addrK y z) -!addrA.
by rewrite (addrC (-u)) !addrA; split=> [/addIr /addIr|->//].
qed.

lemma subr_add2r (z x y : t): (x + z) - (y + z) = x - y.
proof. by rewrite opprD addrACA addrN addr0. qed.
end section.

(* -------------------------------------------------------------------- *)
(* [intmul x n] is [n] copies of [x] folded with [+]; for negative [n]
   it is [-(intmul x (-n))]. Foundational for [ofint] and for
   characterizing ring exponents.                                       *)
op intmul ['a <: addgroup] (x : 'a) (n : int) =
  if n < 0
  then -(iterop (-n) (+) x zero)
  else  (iterop   n  (+) x zero).

(* -------------------------------------------------------------------- *)
section.
declare type t <: addgroup.

lemma intmulpE (x : t) (c : int) : 0 <= c =>
  intmul x c = iterop c (+) x zero.
proof. by rewrite /intmul lezNgt => ->. qed.

lemma mulr0z (x : t): intmul x 0 = zero.
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
by rewrite !iteropE iterS.
qed.

lemma mulNrz (x : t) (n : int) : intmul (-x) n = - (intmul x n).
proof.
elim/intwlog: n => [n h| | n ge0_n ih].
+ by rewrite -(@oppzK n) !(@mulrNz _ (- n)) h.
+ by rewrite !mulr0z oppr0.
+ by rewrite !mulrS // ih opprD.
qed.

lemma mulNrNz (x : t) (n : int) : intmul (-x) (-n) = intmul x n.
proof. by rewrite mulNrz mulrNz opprK. qed.

lemma mulrSz (x : t) (n : int) : intmul x (n + 1) = x + intmul x n.
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
end section.

(* ==================================================================== *)
(* Commutative ring: addgroup + multiplicative commutative monoid +
   distributivity. Multi-parent factory inheritance: comring inherits
   from [addgroup] and from [mulmonoid] (with [idm := oner] and
   [(+) := ( * )]). The locally-declared [oner] / [( * )] are aliases
   for the inherited mulmonoid ops; the multiplicative
   associativity / commutativity / left-id axioms ([mulrA] / [mulrC]
   / [mul1r]) are kept as axioms in the class body so they're
   available under conventional ring-theoretic names downstream.      *)
(* ==================================================================== *)
type class comring <: addgroup & mulmonoid = {
  (* Additive structure inherited from [addgroup -> addmonoid ->
     (monoid with idm = zero, mop = (+))].
     Multiplicative structure inherited from
     [mulmonoid -> (monoid with idm = oner, mop = ( * ))].
     The monoid axioms [mopA] / [mopC] / [mop0] are obligations of
     BOTH chain paths; at instance-declaration time discharge them
     twice with label-disambiguated [proof mopA<:addmonoid>] and
     [proof mopA<:mulmonoid>] clauses. *)
  op invr  : comring -> comring
  op unit  : comring -> bool

  axiom oner_neq0 : oner <> zero<:comring>
  axiom mulrDl    : left_distributive ( * ) (+)<:comring>
  axiom mulVr     : left_inverse_in unit oner invr ( * )
  axiom unitP     : forall (x y : comring), y * x = oner => unit x
  axiom unitout   : forall (x : comring), !unit x => invr x = x
}.

(* -------------------------------------------------------------------- *)
section.
declare type t <: comring.

abbrev (/) (x y : t) = x * (invr y).

(* Re-export the inherited mulmonoid-view monoid lemmas under
   the conventional ring-theoretic names. Going through
   [mulm*] (defined at `'a <: mulmonoid`) avoids the comring-level
   ambiguity between the addmonoid and mulmonoid views. *)
lemma mulrA: associative ( * )<:t>.
proof. by apply: mulmA. qed.

lemma mulrC: commutative ( * )<:t>.
proof. by apply: mulmC. qed.

lemma mul1r: left_id oner<:t> ( * )<:t>.
proof. by apply: mul1m. qed.

lemma mulr1: right_id oner<:t> ( * ).
proof. by move=> x; rewrite mulrC mul1r. qed.

lemma mulrCA: left_commutative ( * )<:t>.
proof. by move=> x y z; rewrite !mulrA (@mulrC x y). qed.

lemma mulrAC: right_commutative ( * )<:t>.
proof. by move=> x y z; rewrite -!mulrA (@mulrC y z). qed.

lemma mulrACA: interchange ( * )<:t> ( * ).
proof. by move=> x y z u; rewrite -!mulrA (mulrCA y). qed.

lemma mulrSl (x y : t) : (x + oner) * y = x * y + y.
proof. by rewrite mulrDl mul1r. qed.

lemma mulrDr: right_distributive ( * )<:t> (+).
proof. by move=> x y z; rewrite mulrC mulrDl !(@mulrC _ x). qed.

lemma mul0r: left_zero zero<:t> ( * ).
proof. by move=> x; apply: (@addIr (oner * x)); rewrite -mulrDl !add0r mul1r. qed.

lemma mulr0: right_zero zero<:t> ( * ).
proof. by move=> x; apply: (@addIr (x * oner)); rewrite -mulrDr !add0r mulr1. qed.

lemma mulrN (x y : t): x * (- y) = - (x * y).
proof. by apply: (@addrI (x * y)); rewrite -mulrDr !addrN mulr0. qed.

lemma mulNr (x y : t): (- x) * y = - (x * y).
proof. by apply: (@addrI (x * y)); rewrite -mulrDl !addrN mul0r. qed.

lemma mulrNN (x y : t): (- x) * (- y) = x * y.
proof. by rewrite mulrN mulNr opprK. qed.

lemma mulN1r (x : t): (-oner) * x = -x.
proof. by rewrite mulNr mul1r. qed.

lemma mulrN1 (x : t): x * -oner = -x.
proof. by rewrite mulrN mulr1. qed.

lemma mulrBl: left_distributive ( * )<:t> (fun (x y : t) => x - y).
proof. by move=> x y z; rewrite mulrDl !mulNr. qed.

lemma mulrBr: right_distributive ( * )<:t> (fun (x y : t) => x - y).
proof. by move=> x y z; rewrite mulrDr !mulrN. qed.

(* -------------------------------------------------------------------- *)
(* Multiplicative-inverse / unit theory.                                *)
(* -------------------------------------------------------------------- *)

lemma mulrV: right_inverse_in unit<:t> oner invr ( * ).
proof. by move=> x /mulVr; rewrite mulrC. qed.

lemma divrr (x : t): unit x => x / x = oner.
proof. by apply/mulrV. qed.

lemma invr_out (x : t): !unit x => invr x = x.
proof. by apply/unitout. qed.

lemma unitrP (x : t): unit x <=> (exists y, y * x = oner).
proof. by split=> [/mulVr<- |]; [exists (invr x) | case=> y /unitP]. qed.

lemma mulKr: left_loop_in unit<:t> invr ( * ).
proof. by move=> x un_x y; rewrite mulrA mulVr // mul1r. qed.

lemma mulrK: right_loop_in unit<:t> invr ( * ).
proof. by move=> y un_y x; rewrite -mulrA mulrV // mulr1. qed.

lemma mulVKr: rev_left_loop_in unit<:t> invr ( * ).
proof. by move=> x un_x y; rewrite mulrA mulrV // mul1r. qed.

lemma mulrVK: rev_right_loop_in unit<:t> invr ( * ).
proof. by move=> y nz_y x; rewrite -mulrA mulVr // mulr1. qed.

lemma mulrI: right_injective_in unit<:t> ( * ).
proof. by move=> x Ux; have /can_inj h := mulKr _ Ux. qed.

lemma mulIr: left_injective_in unit<:t> ( * ).
proof. by move=> x /mulrI h y1 y2; rewrite !(@mulrC _ x) => /h. qed.

lemma unitrE (x : t): unit x <=> (x / x = oner).
proof.
split=> [Ux|xx1]; 1: by apply/divrr.
by apply/unitrP; exists (invr x); rewrite mulrC.
qed.

lemma invrK: involutive invr<:t>.
proof.
move=> x; case: (unit x)=> Ux; 2: by rewrite !invr_out.
rewrite -(mulrK _ Ux (invr (invr x))) -mulrA.
rewrite (@mulrC x) mulKr //; apply/unitrP.
by exists x; rewrite mulrV.
qed.

lemma invr_inj: injective invr<:t>.
proof. by apply: (can_inj _ _ invrK). qed.

lemma unitrV (x : t): unit (invr x) <=> unit x.
proof. by rewrite !unitrE invrK mulrC. qed.

lemma unitr1: unit<:t> oner.
proof. by apply/unitrP; exists oner; rewrite mulr1. qed.

lemma invr1: invr oner<:t> = oner.
proof. by rewrite -{2}(mulVr _ unitr1) mulr1. qed.

lemma div1r (x : t) : oner / x = invr x.
proof. by rewrite mul1r. qed.

lemma divr1 (x : t) : x / oner = x.
proof. by rewrite invr1 mulr1. qed.

lemma unitr0: !unit zero<:t>.
proof. by apply/negP=> /unitrP [y]; rewrite mulr0 eq_sym oner_neq0. qed.

lemma invr0: invr zero<:t> = zero.
proof. by rewrite invr_out ?unitr0. qed.

lemma unitrN1: unit<:t> (-oner).
proof. by apply/unitrP; exists (-oner); rewrite mulrNN mulr1. qed.

lemma invrN1: invr<:t> (-oner) = -oner.
proof. by rewrite -{2}(divrr unitrN1) mulN1r opprK. qed.

lemma unitrMl (x y : t) : unit y => (unit (x * y) <=> unit x).
proof.
move=> uy; case: (unit x)=> /=; last first.
+ apply/contra=> uxy; apply/unitrP; exists (y * invr (x * y)).
  apply/(mulrI (invr y)); first by rewrite unitrV.
  rewrite !mulrA mulVr // mul1r; apply/(mulIr y)=> //.
  by rewrite -mulrA mulVr // mulr1 mulVr.
move=> ux; apply/unitrP; exists (invr y * invr x).
by rewrite -!mulrA mulKr // mulVr.
qed.

lemma unitrMr (x y : t) : unit x => (unit (x * y) <=> unit y).
proof.
move=> ux; split=> [uxy|uy]; last by rewrite unitrMl.
by rewrite -(mulKr _ ux y) unitrMl ?unitrV.
qed.

lemma unitrM (x y : t) : unit (x * y) <=> (unit x /\ unit y).
proof.
case: (unit x) => /=; first by apply: unitrMr.
apply: contra => /unitrP[z] zVE; apply/unitrP.
by exists (y * z); rewrite mulrAC (@mulrC y) (@mulrC _ z).
qed.

lemma unitrN (x : t) : unit (-x) <=> unit x.
proof. by rewrite -mulN1r unitrMr // unitrN1. qed.

lemma invrM (x y : t) : unit x => unit y => invr (x * y) = invr y * invr x.
proof.
move=> Ux Uy; have Uxy: unit (x * y) by rewrite unitrMl.
by apply: (mulrI _ Uxy); rewrite mulrV ?mulrA ?mulrK ?mulrV.
qed.

lemma invrN (x : t) : invr (- x) = - (invr x).
proof.
case: (unit x) => ux; last by rewrite !invr_out ?unitrN.
by rewrite -mulN1r invrM ?unitrN1 // invrN1 mulrN1.
qed.

lemma invr_neq0 (x : t) : x <> zero => invr x <> zero.
proof.
move=> nx0; case: (unit x)=> Ux; last by rewrite invr_out ?Ux.
by apply/negP=> x'0; move: Ux; rewrite -unitrV x'0 unitr0.
qed.

lemma invr_eq0 (x : t) : (invr x = zero) <=> (x = zero).
proof. by apply/iff_negb; split=> /invr_neq0; rewrite ?invrK. qed.

lemma invr_eq1 (x : t) : (invr x = oner) <=> (x = oner).
proof. by rewrite (inv_eq invrK) invr1. qed.

end section.

(* -------------------------------------------------------------------- *)
(* Embedding of [int] into a [comring]: [ofint n = intmul oner n].      *)
op ofint ['a <: comring] (n : int) : 'a = intmul oner n.

(* -------------------------------------------------------------------- *)
section.
declare type t <: comring.

lemma ofint0 : ofint<:t> 0 = zero.
proof. by apply/mulr0z. qed.

lemma ofint1 : ofint<:t> 1 = oner.
proof. by apply/mulr1z. qed.

lemma ofintS (i : int) : 0 <= i => ofint<:t> (i + 1) = oner + ofint i.
proof. by apply/mulrS. qed.

lemma ofintN (i : int) : ofint<:t> (-i) = - (ofint i).
proof. by apply/mulrNz. qed.

(* -------------------------------------------------------------------- *)
(* Interaction between additive [intmul] and multiplicative [( * )]. *)
lemma mulrnAl (x y : t) (n : int) : 0 <= n =>
  (intmul x n) * y = intmul (x * y) n.
proof.
elim: n => [|n ge0n ih]; rewrite !(mulr0z, mulrS) ?mul0r //.
by rewrite mulrDl ih.
qed.

lemma mulrnAr (x y : t) (n : int) : 0 <= n =>
  x * (intmul y n) = intmul (x * y) n.
proof.
elim: n => [|n ge0n ih]; rewrite !(mulr0z, mulrS) ?mulr0 //.
by rewrite mulrDr ih.
qed.

lemma mulrzAl (x y : t) (z : int) : (intmul x z) * y = intmul (x * y) z.
proof.
case: (lezWP 0 z)=> [|_] le; first by rewrite mulrnAl.
by rewrite -oppzK mulrNz mulNr mulrnAl -?mulrNz // oppz_ge0.
qed.

lemma mulrzAr (x y : t) (z : int) : x * (intmul y z) = intmul (x * y) z.
proof.
case: (lezWP 0 z)=> [|_] le; first by rewrite mulrnAr.
by rewrite -oppzK mulrNz mulrN mulrnAr -?mulrNz // oppz_ge0.
qed.

lemma mul1r0z (x : t) : x * ofint 0 = zero.
proof. by rewrite ofint0 mulr0. qed.

lemma mul1r1z (x : t) : x * ofint 1 = x.
proof. by rewrite ofint1 mulr1. qed.

lemma mul1r2z (x : t) : x * ofint 2 = x + x.
proof. by rewrite /ofint mulr2z mulrDr mulr1. qed.

lemma mulr_intl (x : t) (z : int) : (ofint z) * x = intmul x z.
proof. by rewrite mulrzAl mul1r. qed.

lemma mulr_intr (x : t) (z : int) : x * (ofint z) = intmul x z.
proof. by rewrite mulrzAr mulr1. qed.
end section.

(* -------------------------------------------------------------------- *)
(* Multiplicative exponentiation. Mirrors [intmul] on the additive side
   but folds with [( * )] starting at [oner], inverting for negative
   exponents.                                                           *)
op exp ['a <: comring] (x : 'a) (n : int) =
  if   n < 0
  then invr (iterop (-n) ( * ) x oner)
  else iterop n ( * ) x oner.

(* -------------------------------------------------------------------- *)
section.
declare type t <: comring.

lemma expr0 (x : t) : exp x 0 = oner.
proof. by rewrite /exp /= iterop0. qed.

lemma expr1 (x : t) : exp x 1 = x.
proof. by rewrite /exp /= iterop1. qed.

(* Multiplicative analogue of [TcMonoid.iteropE], specialised for
   [( * )] / [oner] (i.e. [iterop] folded over the mulmonoid view). *)
lemma mul_iteropE (n : int) (x : t) :
  iterop n ( * ) x oner = iter n (( * ) x) oner.
proof.
elim/natcase n => [n le0_n|n ge0_n].
+ by rewrite ?(iter0, iterop0).
+ by rewrite iterSr // mulr1 iteropS.
qed.

lemma exprS (x : t) (i : int) : 0 <= i => exp x (i+1) = x * (exp x i).
proof.
move=> ge0i; rewrite /exp !ltzNge ge0i addz_ge0 //=.
by rewrite !mul_iteropE iterS.
qed.

lemma expr_pred (x : t) (i : int) : 0 < i => exp x i = x * (exp x (i - 1)).
proof. smt(exprS). qed.

lemma exprSr (x : t) (i : int) : 0 <= i => exp x (i+1) = (exp x i) * x.
proof. by move=> ge0_i; rewrite exprS // mulrC. qed.

lemma expr2 (x : t) : exp x 2 = x * x.
proof. by rewrite (@exprS _ 1) // expr1. qed.

lemma exprN (x : t) (i : int) : exp x (-i) = invr (exp x i).
proof.
case: (i = 0) => [->|]; first by rewrite oppz0 expr0 invr1.
rewrite /exp oppz_lt0 ltzNge lez_eqVlt oppzK=> -> /=.
by case: (_ < _)%Int => //=; rewrite invrK.
qed.

lemma exprN1 (x : t) : exp x (-1) = invr x.
proof. by rewrite exprN expr1. qed.

lemma unitrX (x : t) (m : int) : unit x => unit (exp x m).
proof.
move=> invx; wlog: m / (0 <= m) => [wlog|].
+ (have [] : (0 <= m \/ 0 <= -m) by move=> /#); first by apply: wlog.
  by move=> ?; rewrite -oppzK exprN unitrV &(wlog).
elim: m => [|m ge0_m ih]; first by rewrite expr0 unitr1.
by rewrite exprS // &(unitrMl).
qed.

lemma unitrX_neq0 (x : t) (m : int) : m <> 0 => unit (exp x m) => unit x.
proof.
wlog: m / (0 < m) => [wlog|].
+ case: (0 < m); [by apply: wlog | rewrite ltzNge /= => le0_m nz_m].
  by move=> h; (apply: (wlog (-m)); 1,2:smt()); rewrite exprN unitrV.
by move=> gt0_m _; rewrite (_ : m = m - 1 + 1) // exprS 1:/# unitrM.
qed.

lemma exprV (x : t) (i : int) : exp (invr x) i = exp x (-i).
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

lemma exprVn (x : t) (n : int) : 0 <= n => exp (invr x) n = invr (exp x n).
proof.
elim: n => [|n ge0_n ih]; first by rewrite !expr0 invr1.
case: (unit x) => ux.
- by rewrite exprSr -1:exprS // invrM ?unitrX // ih -invrM // unitrX.
- by rewrite !invr_out //; apply: contra ux; apply: unitrX_neq0 => /#.
qed.

lemma exprMn (x y : t) (n : int) : 0 <= n => exp (x * y) n = exp x n * exp y n.
proof.
elim: n => [|n ge0_n ih]; first by rewrite !expr0 mulr1.
by rewrite !exprS // mulrACA ih.
qed.

lemma exprD_nneg (x : t) (m n : int) : 0 <= m => 0 <= n =>
  exp x (m + n) = exp x m * exp x n.
proof.
move=> ge0_m ge0_n; elim: m ge0_m => [|m ge0_m ih].
+ by rewrite expr0 mul1r.
by rewrite addzAC !exprS ?addz_ge0 // ih mulrA.
qed.

lemma exprD (x : t) (m n : int) : unit x => exp x (m + n) = exp x m * exp x n.
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
case=> [->>|lt_m_Sn]; first by rewrite exprD_nneg //#.
by rewrite addzA exprS 1:/# ih 1,2:/# exprS // mulrCA.
qed.

lemma exprM (x : t) (m n : int) :
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
elim/natind: n => [|n hn ih hm _]; 1: smt (expr0).
by rewrite mulzDr exprS //= mulrC exprD_nneg 1:/# 1:// ih.
qed.

lemma expr0n (n : int) : 0 <= n => exp zero<:t> n = if n = 0 then oner else zero.
proof.
elim: n => [|n ge0_n _]; first by rewrite expr0.
by rewrite exprS // mul0r addz1_neq0.
qed.

lemma expr0z (z : int) : exp zero<:t> z = if z = 0 then oner else zero.
proof.
case: (0 <= z) => [/expr0n // | /ltzNge lt0_z].
rewrite -{1}(@oppzK z) exprN; have ->/=: z <> 0 by smt().
rewrite invr_eq0 expr0n ?oppz_ge0 1:ltzW //.
by have ->/=: -z <> 0 by smt().
qed.

lemma expr1z (z : int) : exp oner<:t> z = oner.
proof.
elim/intwlog: z.
+ by move=> n h; rewrite -(@oppzK n) exprN h invr1.
+ by rewrite expr0.
+ by move=> n ge0_n ih; rewrite exprS // mul1r ih.
qed.

(* -------------------------------------------------------------------- *)
(* Squaring identities. *)
lemma sqrrD (x y : t) :
  exp (x + y) 2 = exp x 2 + intmul (x * y) 2 + exp y 2.
proof.
by rewrite !expr2 mulrDl !mulrDr mulr2z !addrA (@mulrC y x).
qed.

lemma sqrrN (x : t) : exp (-x) 2 = exp x 2.
proof. by rewrite !expr2 mulrNN. qed.

lemma sqrrB (x y : t) :
  exp (x - y) 2 = exp x 2 - intmul (x * y) 2 + exp y 2.
proof. by rewrite sqrrD sqrrN mulrN mulNrz. qed.

lemma signr_odd (n : int) : 0 <= n =>
  exp (-oner<:t>) (b2i (odd n)) = exp (-oner) n.
proof.
elim: n => [|n ge0_nih]; first by rewrite odd0 expr0 expr0.
rewrite !(iterS, oddS) // exprS // -/(odd _) => <-.
by case: (odd _); rewrite /b2i /= !(expr0, expr1) mulN1r ?opprK.
qed.

lemma subr_sqr_1 (x : t) : exp x 2 - oner = (x - oner) * (x + oner).
proof.
rewrite mulrBl mulrDr !(mulr1, mul1r) expr2 -addrA.
by congr; rewrite opprD addrA addrN add0r.
qed.

(* -------------------------------------------------------------------- *)
(* Left regularity: [lreg x] iff multiplication by [x] on the left is
   injective. *)
op lreg ['a <: comring] (x : 'a) = injective (fun y => x * y).

lemma mulrI_eq0 (x y : t) : lreg x => (x * y = zero) <=> (y = zero).
proof. by move=> reg_x; rewrite -{1}(mulr0 x) (inj_eq reg_x). qed.

lemma lreg_neq0 (x : t) : lreg x => x <> zero.
proof.
apply/contraL=> ->; apply/negP => /(_ zero oner).
by rewrite (@eq_sym _ oner) oner_neq0 /= !mul0r.
qed.

lemma mulrI0_lreg (x : t) :
  (forall y, x * y = zero => y = zero) => lreg x.
proof.
by move=> reg_x y z eq; rewrite -subr_eq0 &(reg_x) mulrBr eq subrr.
qed.

lemma lregN (x : t) : lreg x => lreg (-x).
proof. by move=> reg_x y z; rewrite !mulNr => /oppr_inj /reg_x. qed.

lemma lreg1 : lreg oner<:t>.
proof. by move=> x y; rewrite !mul1r. qed.

lemma lregM (x y : t) : lreg x => lreg y => lreg (x * y).
proof. by move=> reg_x reg_y z t; rewrite -!mulrA => /reg_x /reg_y. qed.

lemma lregXn (x : t) (n : int) : 0 <= n => lreg x => lreg (exp x n).
proof.
move=> + reg_x; elim: n => [|n ge0_n ih].
- by rewrite expr0 &(lreg1).
- by rewrite exprS // &(lregM).
qed.

(* -------------------------------------------------------------------- *)
lemma fracrDE (n1 n2 d1 d2 : t) :
  unit d1 => unit d2 =>
    n1 / d1 + n2 / d2 = (n1 * d2 + n2 * d1) / (d1 * d2).
proof.
move=> inv_d1 inv_d2; rewrite mulrDl [n1 * d2]mulrC.
by rewrite !invrM //; congr; rewrite mulrACA divrr // ?(mul1r, mulr1).
qed.

(* -------------------------------------------------------------------- *)
(* If [x] has order dividing [k] (i.e. [x ^ k = 1]), then [x ^ n] only
   depends on [n %% k]. The [unit x] precondition makes the lemma work
   for negative [n] (via [exprN], which is well-behaved on units in
   any commutative ring). At [field] level [unit x ↔ x ≠ 0] so the
   precondition is automatic when [x ≠ 0].                              *)
lemma exp_mod_unit (x : t) (n k : int) :
  unit x => exp x k = oner => exp x n = exp x (n %% k).
proof.
move=> ux; case: (k = 0) => [->>|nz_k]; first by rewrite modz0.
move=> eq_xk.
have h: n = k * (n %/ k) + n %% k by smt(divz_eq).
rewrite {1}h exprD // exprM eq_xk expr1z mul1r //.
qed.

end section.
(* ==================================================================== *)
(* Boolean ring: commutative ring with idempotent multiplication. *)
(* ==================================================================== *)
type class boolring <: comring = {
  axiom mulrr : forall (x : boolring), x * x = x
}.

(* -------------------------------------------------------------------- *)
section.
declare type t <: boolring.

lemma addrr (x : t): x + x = zero.
proof.
apply (@addrI (x + x)); rewrite addr0 -{1 2 3 4}[x]mulrr.
by rewrite -mulrDr -mulrDl mulrr.
qed.

lemma oppr_id (x : t) : -x = x.
proof. by rewrite -[x]opprK -addr_eq0 opprK addrr. qed.

end section.

(* ==================================================================== *)
(* Integral domain: commutative ring with no zero divisors. *)
(* ==================================================================== *)
type class idomain <: comring = {
  axiom mulf_eq0 :
    forall (x y : idomain), x * y = zero<:idomain> <=> x = zero \/ y = zero
}.

(* -------------------------------------------------------------------- *)
section.
declare type t <: idomain.

lemma mulf_neq0 (x y : t) : x <> zero => y <> zero => x * y <> zero.
proof. by move=> nz_x nz_y; apply/negP; rewrite mulf_eq0 /#. qed.

lemma expf_eq0 (x : t) (n : int) :
  (exp x n = zero) <=> (n <> 0 /\ x = zero).
proof.
elim/intwlog: n => [n| |n ge0_n ih].
+ by rewrite exprN invr_eq0 /#.
+ by rewrite expr0 oner_neq0.
by rewrite exprS // mulf_eq0 ih addz1_neq0 ?andKb.
qed.

lemma mulfI (x : t) : x <> zero => injective (( * ) x).
proof.
move=> ne0_x y y'; rewrite -(opprK (x * y')) -mulrN -addr_eq0.
by rewrite -mulrDr mulf_eq0 ne0_x /= addr_eq0 opprK.
qed.

lemma mulIf (x : t) : x <> zero => injective (fun y => y * x).
proof. by move=> nz_x y z; rewrite -!(@mulrC x); exact: mulfI. qed.

lemma sqrf_eq1 (x : t) : (exp x 2 = oner) <=> (x = oner \/ x = -oner).
proof. by rewrite -subr_eq0 subr_sqr_1 mulf_eq0 subr_eq0 addr_eq0. qed.

lemma lregP (x : t) : lreg x <=> x <> zero.
proof. by split=> [/lreg_neq0//|/mulfI]. qed.

lemma eqr_div (x1 y1 x2 y2 : t) : unit y1 => unit y2 =>
  (x1 / y1 = x2 / y2) <=> (x1 * y2 = x2 * y1).
proof.
move=> Nut1 Nut2; rewrite -{1}(@mulrK y2 _ x1) //.
rewrite  -{1}(@mulrK y1 _ x2) // -!mulrA (@mulrC (invr y1)) !mulrA.
split=> [|->] //;
  (have nz_Vy1: unit (invr y1) by rewrite unitrV);
  (have nz_Vy2: unit (invr y2) by rewrite unitrV).
by move/(mulIr _ nz_Vy1)/(mulIr _ nz_Vy2).
qed.

end section.

(* ==================================================================== *)
(* Field: integral domain where every non-zero element is a unit.
   The original [Ring.ec] field redefines [unit] via clone-substitution
   (`pred unit x <= x <> zeror`); here we keep [unit] as the inherited
   predicate and add the equivalence as an axiom of [field].          *)
(* ==================================================================== *)
type class field <: idomain = {
  axiom unitfP : forall (x : field), unit x <=> x <> zero<:field>
}.

(* -------------------------------------------------------------------- *)
section.
declare type t <: field.

lemma mulfV (x : t) : x <> zero => x * (invr x) = oner.
proof. by move=> nz_x; apply/mulrV/unitfP. qed.

lemma mulVf (x : t) : x <> zero => (invr x) * x = oner.
proof. by move=> nz_x; apply/mulVr/unitfP. qed.

lemma divff (x : t) : x <> zero => x / x = oner.
proof. by move=> nz_x; apply/divrr/unitfP. qed.

lemma invfM (x y : t) : invr (x * y) = invr x * invr y.
proof.
case: (x = zero) => [->|nz_x]; first by rewrite !(mul0r, invr0).
case: (y = zero) => [->|nz_y]; first by rewrite !(mulr0, invr0).
by rewrite invrM ?unitfP // mulrC.
qed.

lemma invf_div (x y : t) : invr (x / y) = y / x.
proof. by rewrite invfM invrK mulrC. qed.

lemma eqf_div (x1 y1 x2 y2 : t) : y1 <> zero => y2 <> zero =>
  (x1 / y1 = x2 / y2) <=> (x1 * y2 = x2 * y1).
proof. by move=> nz_y1 nz_y2; apply: eqr_div; apply/unitfP. qed.

lemma expfM (x y : t) (n : int) : exp (x * y) n = exp x n * exp y n.
proof.
elim/intwlog: n => [n h | | n ge0_n ih].
+ by rewrite -(@oppzK n) !(@exprN _ (-n)) h invfM.
+ by rewrite !expr0 mulr1.
+ by rewrite !exprS // mulrCA -!mulrA -ih mulrCA.
qed.

end section.

(* ==================================================================== *)
(* Additive morphisms between two [addgroup]s.                          *)
(* ==================================================================== *)
pred additive ['a <: addgroup, 'b <: addgroup] (f : 'a -> 'b) =
  forall (x y : 'a), f (x - y) = f x - f y.

(* -------------------------------------------------------------------- *)
section.
declare type t1 <: addgroup.
declare type t2 <: addgroup.

declare op f : t1 -> t2.
declare axiom f_is_additive : additive f.

lemma raddfB (x y : t1) : f (x - y) = f x - f y.
proof. by apply/f_is_additive. qed.

lemma raddf0 : f zero<:t1> = zero<:t2>.
proof. by rewrite -(@subr0 zero<:t1>) raddfB subrr. qed.

lemma raddfN (x : t1) : f (- x) = - (f x).
proof. by rewrite -(@sub0r x) raddfB raddf0 sub0r. qed.

lemma raddfD (x y : t1) : f (x + y) = f x + f y.
proof. by rewrite -{1}(@opprK y) raddfB raddfN opprK. qed.
end section.

(* ==================================================================== *)
(* Multiplicative homomorphisms between two [comring]s.                 *)
(* ==================================================================== *)
pred multiplicative ['a <: comring, 'b <: comring] (f : 'a -> 'b) =
     f oner<:'a> = oner<:'b>
  /\ forall (x y : 'a), f (x * y) = f x * f y.

(* ==================================================================== *)
(* Convenience: [(^)] as multiplicative exponentiation on any comring.
   Mirrors the [abbrev (^) = exp] declaration in the original
   [theories/algebra/Ring.ec:IntID] but is published at top level so
   it works for any [comring] carrier (not just [int]).                 *)
(* ==================================================================== *)
abbrev (^) ['a <: comring] (x : 'a) (n : int) : 'a = exp x n.
