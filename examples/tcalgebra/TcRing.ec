pragma +implicits.

(* -------------------------------------------------------------------- *)
require import Core.
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

(* ==================================================================== *)
(* Commutative ring: addgroup + multiplicative commutative monoid +
   distributivity. Inherits both flavors of monoid; multi-parent.       *)
(* ==================================================================== *)
(* For now [comring] declares its multiplicative content directly
   rather than inheriting it from [mulmonoid]. The latter would let
   [bigM]/[\prod] fold transparently on a comring carrier, but
   requires TC inference to disambiguate between two monoid views
   on the same type — out of scope for this port.                     *)
type class comring <: addgroup = {
  op oner  : comring
  op ( * ) : comring -> comring -> comring
  op invr  : comring -> comring
  op unit  : comring -> bool

  axiom oner_neq0 : oner <> zero<:comring>
  axiom mulrA     : associative ( * )
  axiom mulrC     : commutative ( * )
  axiom mul1r     : left_id oner ( * )
  axiom mulrDl    : left_distributive ( * ) (+)<:comring>
  axiom mulVr     : left_inverse_in unit oner invr ( * )
  axiom unitP     : forall (x y : comring), y * x = oner => unit x
  axiom unitout   : forall (x : comring), !unit x => invr x = x
}.

(* -------------------------------------------------------------------- *)
section.
declare type t <: comring.

abbrev (/) (x y : t) = x * (invr y).

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
end section.

