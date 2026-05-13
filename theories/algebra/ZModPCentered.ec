(* ==================================================================== *)
require import AllCore IntDiv.
require import StdOrder.
(*---*) import IntOrder.
require ZModP.

(* ==================================================================== *)
(* Centered (signed) representation of elements of the ring Z/pZ.       *)
(*                                                                      *)
(* For p >= 2, the centered representative `crepr : zmod -> int' maps   *)
(* every element to the unique integer in the half-open centered        *)
(* interval [(p+1)/2 - p, (p+1)/2). For odd primes p > 2 this interval  *)
(* is exactly {-(p-1)/2, ..., (p-1)/2}, the standard "balanced"         *)
(* representation used in lattice-based cryptography.                   *)
(*                                                                      *)
(* Provides:                                                            *)
(*   - `to_crepr', `crepr' (centered representative on int and Zq)      *)
(*   - range, round-trip, equality lemmas                               *)
(*   - algebraic laws under +, *                                        *)
(*   - centered absolute value `"`|_|"' with triangle / product /       *)
(*     monotonicity inequalities                                        *)
(*                                                                      *)
(* The sub-theory `ZqCenteredField' adds prime-only lemmas:             *)
(*   - `creprN', `creprN2', `creprND' (negation symmetry)               *)
(*   - `abs_zpN'                                                        *)
(* ==================================================================== *)

(* ==================================================================== *)
abstract theory ZpCentered. 

clone import ZModP.ZModRing as ZMR.

(* -------------------------------------------------------------------- *)
(* Auxiliary congruence lemmas. *)

lemma zmodcgr_ceq a b :
     (p + 1) %/ 2 - p <= a < (p + 1) %/ 2
  => (p + 1) %/ 2 - p <= b < (p + 1) %/ 2
  => zmodcgr a b
  => a = b.
proof.
move=> Ha Hb Hcgr.
have Hp := ge2_p.
have Hdvd : p %| (a - b) by smt(zmodcgrP).
smt().
qed.

lemma zmodcgr_transitive b a c :
  zmodcgr a b => zmodcgr b c => zmodcgr a c.
proof. smt(). qed.

lemma zmodcgr_mp a : zmodcgr a (a - p) by smt().

lemma zmodcgr_refl a b : zmodcgr a b <=> zmodcgr b a by smt().

(* -------------------------------------------------------------------- *)
(* Centered representative on int.                                      *)
(*                                                                      *)
(* "Halfway" is rounded down: when 2 %| p the unique value with         *)
(* asint = p/2 maps to -p/2.  For odd p the choice is irrelevant.       *)

op to_crepr (x : int) : int =
  let y = x %% p in
  if (p + 1) %/ 2 <= y then y - p else y.

lemma to_crepr_idempotent : to_crepr \o to_crepr = to_crepr.
proof. by rewrite fun_ext /(\o) => x; smt(ge2_p). qed.

lemma rg_to_crepr x :
  (p + 1) %/ 2 - p <= to_crepr x < (p + 1) %/ 2.
proof. smt(ge2_p rg_asint). qed.

lemma to_crepr_zmodcgr x : zmodcgr x (to_crepr x).
proof.
rewrite /to_crepr /=; case ((p + 1) %/ 2 <= x %% p) => _.
- have -> : x %% p - p = x %% p + (-1) * p by ring.
  by rewrite /zmodcgr modzMDr modz_mod.
- by rewrite /zmodcgr modz_mod.
qed.

lemma to_crepr_id x :
  (p + 1) %/ 2 - p <= x < (p + 1) %/ 2 => to_crepr x = x.
proof.
move=> [Hl Hu]; rewrite /to_crepr /=.
have Hp := ge2_p.
case (0 <= x) => Hx.
- have -> : x %% p = x by apply modz_small; smt().
  by rewrite ifF /#.
- have Hxp : (x + p) %% p = x + p by apply modz_small; smt().
  have -> : x %% p = x + p by rewrite -(modzDr x) Hxp.
  by rewrite ifT 1:/# /#.
qed.

lemma to_crepr_eq x y : to_crepr x = to_crepr y <=> zmodcgr x y.
proof. rewrite /to_crepr /= /#. qed.

(* -------------------------------------------------------------------- *)
(* Centered representative on Zq.                                       *)

op crepr (x : zmod) : int =
  let y = asint x in
  if (p + 1) %/ 2 <= y then y - p else y.

lemma rg_crepr x :
  (p + 1) %/ 2 - p <= crepr x < (p + 1) %/ 2.
proof. smt(ge2_p rg_asint). qed.

lemma crepr_eq x y : crepr x = crepr y <=> x = y.
proof. smt(rg_asint asint_eq). qed.

lemma asint_crepr x : asint x = (crepr x) %% p.
proof.
rewrite /crepr /=.
case ((p + 1) %/ 2 <= asint x) => _.
- by rewrite -modzDr; smt(modz_small rg_asint).
- by smt(modz_small rg_asint).
qed.

lemma creprK (x : zmod) : inzmod (crepr x) = x.
proof.
rewrite /crepr /=.
case ((p + 1) %/ 2 <= asint x) => ?; last by exact asintK.
rewrite inzmod_mod.
suff : (asint x - p) %% p = asint x by smt(asintK).
smt(rg_asint).
qed.

lemma inzmodK_centered x :
     (p + 1) %/ 2 - p <= x
  => x < (p + 1) %/ 2
  => crepr (inzmod x) = x.
proof. by rewrite /crepr inzmodK /#. qed.

(* -------------------------------------------------------------------- *)
(* Algebraic laws under multiplication and addition.                    *)

lemma crepr_mulE x y :
  crepr (x * y) = to_crepr (crepr x * crepr y).
proof.
suff : zmodcgr (crepr (x * y)) (crepr x * crepr y).
+ move => *.
  have ? := to_crepr_zmodcgr (crepr x * crepr y).
  by have : zmodcgr (crepr (x * y)) (to_crepr (crepr x * crepr y));
     smt(to_crepr_zmodcgr rg_to_crepr rg_crepr zmodcgr_ceq).
rewrite /crepr /=.
case ((p + 1) %/ 2 <= asint (x * y)) => ?.
- case ((p + 1) %/ 2 <= asint x) => ?.
  + case ((p + 1) %/ 2 <= asint y) => ?.
    + rewrite -modzMm -(zmodcgr_mp (asint x)) -(zmodcgr_mp (asint y)).
      by rewrite -(zmodcgr_mp (asint (x * y))) mulE -modzMm modz_mod.
    + rewrite -modzMm -(zmodcgr_mp (asint x)) -(zmodcgr_mp (asint (x * y))).
      by rewrite mulE -modzMm modz_mod.
  + case ((p + 1) %/ 2 <= asint y) => ?.
    + rewrite -modzMm -(zmodcgr_mp (asint y)).
      by rewrite -(zmodcgr_mp (asint (x * y))) mulE -modzMm modz_mod.
    + rewrite -modzMm -(zmodcgr_mp (asint (x * y))).
      by rewrite mulE -modzMm modz_mod.
- case ((p + 1) %/ 2 <= asint x) => ?.
  + case ((p + 1) %/ 2 <= asint y) => ?.
    + rewrite -modzMm -(zmodcgr_mp (asint x)) -(zmodcgr_mp (asint y)).
      by rewrite mulE -modzMm modz_mod.
    + rewrite -modzMm -(zmodcgr_mp (asint x)).
      by rewrite mulE -modzMm modz_mod.
  + case ((p + 1) %/ 2 <= asint y) => ?.
    + rewrite -modzMm -(zmodcgr_mp (asint y)).
      by rewrite mulE -modzMm modz_mod.
    + rewrite -modzMm.
      by rewrite mulE -modzMm modz_mod.
qed.

lemma creprD (x y : zmod) :
  crepr (x + y) = to_crepr (crepr x + crepr y).
proof.
suff : zmodcgr (crepr (x + y)) (crepr x + crepr y).
+ move => *.
  have ? := to_crepr_zmodcgr (crepr x + crepr y).
  by have : zmodcgr (crepr (x + y)) (to_crepr (crepr x + crepr y));
     smt(to_crepr_zmodcgr rg_to_crepr rg_crepr zmodcgr_ceq).
rewrite /crepr addE /=.
apply (zmodcgr_transitive (asint x + asint y)).
- case ((p + 1) %/ 2 <= (asint x + asint y) %% p) => _.
  + have -> : (asint x + asint y) %% p - p
            = (asint x + asint y) %% p + (-1) * p by ring.
    by rewrite modzMDr modz_mod.
  + by rewrite modz_mod.
case ((p + 1) %/ 2 <= asint x) => _.
- case ((p + 1) %/ 2 <= asint y) => _.
  + have -> : asint x - p + (asint y - p)
            = asint x + asint y + (-2) * p by ring.
    by rewrite modzMDr.
  + have -> : asint x - p + asint y
            = asint x + asint y + (-1) * p by ring.
    by rewrite modzMDr.
- case ((p + 1) %/ 2 <= asint y) => _ //.
  have -> : asint x + (asint y - p)
          = asint x + asint y + (-1) * p by ring.
  by rewrite modzMDr.
qed.

(* -------------------------------------------------------------------- *)
(* Centered absolute value.                                             *)

op "`|_|" (x : zmod) : int = `| crepr x |.

lemma to_crepr_abs x : `|to_crepr x| <= `|x|.
proof. smt(rg_to_crepr). qed.

lemma abs_zp_small (x : int) :
  `|x| < p %/ 2 => `|inzmod x| = `|x|.
proof. by move=> ?; rewrite /"`|_|"; smt(ltr_norml inzmodK). qed.

lemma abs_zp_triangle (x y : zmod) :
  `|x + y| <= `|x| + `|y|.
proof.
rewrite /"`|_|" creprD.
have := to_crepr_abs (crepr x + crepr y).
smt().
qed.

lemma abs_zp_zero : `|zero| = 0.
proof. by rewrite /"`|_|" /crepr zeroE /=; smt(ge2_p). qed.

lemma abs_zp_one : `|one| = 1.
proof. by rewrite /"`|_|" /crepr /=; rewrite oneE; smt(ge2_p). qed.

lemma ge0_abs_zp (x : zmod) : 0 <= `|x|.
proof. smt(). qed.

lemma abs_zp_ub (x : zmod) : `|x| <= p %/ 2.
proof. smt(rg_asint). qed.

lemma abs_zp_prod (x y : zmod) :
  `|x * y| <= `|x| * `|y|.
proof. by rewrite /"`|_|" crepr_mulE; smt(to_crepr_abs). qed.

lemma abs_zpN (x : zmod) : `|x| = `|-x|.
proof.
rewrite /"`|_|" /crepr /=.
case (x = zero) => ?; first by smt(ZModpRing.oppr0).
have ? : asint x <> 0 by have := asint_inj x zero; smt(zeroE).
suff : asint (-x) = p - asint x by smt().
rewrite oppE -modzDl.
suff : (p - asint x) %% p = ((p - asint x) + p) %% p by smt(rg_asint).
by smt(modzDr).
qed.

end ZpCentered.

(* ==================================================================== *)
(* Field version: when p is prime, additionally provide negation        *)
(* symmetry for the centered representative.                            *)
(* ==================================================================== *)
abstract theory ZpCenteredField.

clone include ZpCentered.
import ZMR.
axiom prime_p : prime p.

(* prime_p is now in scope; ZqCentered's content is available. *)

lemma modz_small2 a :
  p <= a < 2 * p => a %% p = a - p
  by smt().

lemma zmodcgrN a :
  a <> zero =>
  (- asint a) %% p = - asint a %% p + p.
proof.
move => ?; have ? := rg_asint a.
have ? : asint a <> 0 by have := asint_inj a zero; smt(zeroE).
rewrite modNz; 1,2: by smt(prime_p).
rewrite -modzDm modNz //=; 1: smt(prime_p).
suff : (asint a %% p + (p - 1)) %% p = (asint a %% p + (p - 1)) - p by smt().
rewrite (modz_small (asint a) p) 1:/# /=.
by rewrite modz_small2 /#.
qed.

lemma creprN (a : zmod) :
  p <> 2 => crepr (-a) = -crepr a.
proof.
have ? := rg_asint a.
rewrite /crepr !oppE; case (a = zero).
+ by move => -> /=; rewrite zeroE /=; smt(prime_p).
move => ? /=; rewrite !zmodcgrN //.
have -> : (- asint a %% p) + p = p - asint a
  by smt(rg_asint modz_small edivzP).
have ? : asint a <> 0 by have := asint_inj a zero; smt(zeroE).
case ((p + 1) %/ 2 < asint a); 1: by smt().
case (asint a < (p + 1) %/ 2); 1: by smt().
move => *; have -> : asint a = (p + 1) %/ 2 by smt(rg_asint).
have ? : p + 1 = (p + 1) %/ 2 + (p + 1) %/ 2; last by smt().
have ? : p %% 2 <> 0.
+ have := prime_p.
  rewrite /prime => [#? Hmod].
  by have := Hmod 2 => /= /#.
  smt().
qed.

lemma creprN2 (a : zmod) :
  p = 2 => crepr (-a) = crepr a.
proof.
move => Hp.
have ? := rg_asint a.
rewrite /crepr !oppE; case (a = zero).
+ by move => -> /=; rewrite zeroE /=; smt(prime_p).
move => ? /=; rewrite !zmodcgrN /#.
qed.

lemma creprND (a b : zmod) :
  crepr (a - b) = to_crepr (crepr a - crepr b).
proof.
have ? := rg_asint a; have ? := rg_asint b.
case (p = 2); 2: by smt(creprD creprN).
by smt(creprD creprN2).
qed.

end ZpCenteredField.
