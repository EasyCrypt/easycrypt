(* -------------------------------------------------------------------- *)
require import AllCore List StdOrder.
require Quotient.
require import TcMonoid TcRing TcBigop TcBigalg TcInt.
(*---*) import IntOrder.

(* ==================================================================== *)
abstract theory TcIdealComRing.
type t <: comring.

(* -------------------------------------------------------------------- *)
abbrev "_.[_]" (xs : t list) (i : int) = nth zeror xs i.

(* -------------------------------------------------------------------- *)
op (%|) (x y : t) = (exists c, y = c * x).
op (%=) (x y : t) = (x %| y) /\ (y %| x).

(* -------------------------------------------------------------------- *)
lemma dvdrP x y : (x %| y) <=> (exists q, y = q * x).
proof. by rewrite /(%|). qed.

(* -------------------------------------------------------------------- *)
op ideal (I : t -> bool) =
     I zeror
  /\ (forall x y, I x => I y => I (x - y))
  /\ (forall a x, I x => I (a * x)).

lemma idealP (I : t -> bool) :
    I zeror
 => (forall x y, I x => I y => I (x - y))
 => (forall a x, I x => I (a * x))
 => ideal I.
proof. by move=> *; do! split. qed.

lemma idealW (P : (t -> bool) -> bool) :
  (forall I,
        I zeror
     => (forall (x y : t), I x => I y => I (x - y))
     => (forall a x, I x => I (a * x))
     => P I)
  => forall i, ideal i => P i.
proof. by move=> ih i [? [??]]; apply: ih. qed.

lemma ideal0 I : ideal I => I zeror.
proof. by case. qed.

lemma idealN I x : ideal I => I x => I (- x).
proof.
move=> ^iI [_ [+ _]] Ix - /(_ zeror x); rewrite sub0r.
by apply=> //; apply/ideal0.
qed.

lemma idealNP I (x : t) : ideal I => I (- x) = I x.
proof.
move=> iI; apply/eq_iff; split; last exact: idealN.
by rewrite -{2}(opprK x); apply: idealN.
qed.

lemma idealD I x y : ideal I => I x => I y => I (x + y).
proof.
move=> ^iI [_ [+ _] Ix Iy] - /(_ x (-y)); rewrite opprK.
by apply=> //; apply/idealN.
qed.

lemma ideal_sum ['a] I (P : 'a -> bool) (F : 'a -> t) s :
     ideal I
  => (forall x, P x => I (F x))
  => I (bigA P F s).
proof.
elim: s => [|x s ih] idI IF; first by rewrite big_nil ideal0.
rewrite big_cons; case: (P x) => Px; last by apply/ih.
by rewrite idealD -1:&(ih) // &(IF).
qed.

lemma idealB I x y : ideal I => I x => I y => I (x - y).
proof. by move=> iI Ix Iy; rewrite idealD -1:idealN. qed.

lemma idealMl I x y : ideal I => I y => I (x * y).
proof. by case=> _ [_ +]; apply. qed.

lemma idealMr I x y : ideal I => I x => I (x * y).
proof. by move=> iI Ix; rewrite mulrC; apply: idealMl. qed.

(* -------------------------------------------------------------------- *)
op id0 = pred1<:t> zeror.
op idT = predT<:t>.
op idI = predI<:t>.

op idD (I J : t -> bool) : t -> bool =
  fun x => exists i j, (I i /\ J j) /\ x = i + j.

op idR (I : t -> bool) : t -> bool =
  fun x => exists n, 0 <= n /\ I (exp<:t> x n).

(* -------------------------------------------------------------------- *)
lemma mem_id0 x : id0 x <=> x = zeror.
proof. by []. qed.

(* -------------------------------------------------------------------- *)
lemma ideal_id0 : ideal id0.
proof.
rewrite /id0 /pred1; apply/idealP => //.
- by move=> a x -> /=; rewrite mulr0.
qed.

(* -------------------------------------------------------------------- *)
lemma ideal_idT : ideal idT.
proof. by []. qed.

(* -------------------------------------------------------------------- *)
lemma ideal_idI I J : ideal I => ideal J => ideal (idI I J).
proof.
move=> iI iJ @/idI @/predI; apply/idealP => //=.
- by rewrite !ideal0.
- by move=> x y [Ix Jx] [Iy Jy]; rewrite !idealB.
- by move=> a x [Ix Jx]; rewrite !idealMl.
qed.

(* -------------------------------------------------------------------- *)
lemma ideal_idD I J : ideal I => ideal J => ideal (idD I J).
proof.
move=> iI iJ; apply/idealP.
- by exists zeror zeror; rewrite addr0 !ideal0.
- move=> _ _ [xi xj [[Ixi Jxj] ->]] [yi yj [[Iyi Jyj] ->]].
  by rewrite subrACA; exists (xi - yi) (xj - yj) => /=; rewrite !idealB.
- move=> a _ [i j [[Ii Jj] ->]]; rewrite mulrDr.
  by exists (a * i) (a * j) => /=; rewrite !idealMl.
qed.

(* -------------------------------------------------------------------- *)
lemma idDC I J : idD I J = idD J I.
proof.
apply/fun_ext=> x @/idD; apply: eq_iff; split;
  by case=> i j [? ->]; exists j i; rewrite addrC /= andbC.
qed.

(* -------------------------------------------------------------------- *)
lemma mem_idT x : idT x.
proof. by []. qed.

(* -------------------------------------------------------------------- *)
lemma mem_idDl I J x : I x => ideal J => (idD I J) x.
proof.
by move=> Ix iJ; exists x zeror; rewrite Ix addr0 ideal0.
qed.

lemma mem_idDr I J x : J x => ideal I => (idD I J) x.
proof.
by move=> Jx iI; rewrite idDC; apply: mem_idDl.
qed.

(* -------------------------------------------------------------------- *)
lemma ideal_eq1P I u : ideal I => unit u => I u <=> (I = idT).
proof.
move=> idI un_u; split => [Iu|->//]; apply/fun_ext=> x.
by rewrite mem_idT -(mulr1 x) idealMl // -(mulrV u) // idealMr.
qed.

(* -------------------------------------------------------------------- *)
op idgen (xs : t list) = fun (x : t) =>
  exists cs, x = bigiA<:t> predT (fun i => cs.[i] * xs.[i]) 0 (size xs).

lemma idgenP (xs : t list) (x : t) :
  idgen xs x => exists cs, size cs = size xs
    /\ x = bigiA<:t> predT (fun i => cs.[i] * xs.[i]) 0 (size xs).
proof.
case=> cs ->; exists (mkseq (fun i => cs.[i]) (size xs)); split.
- by rewrite size_mkseq ler_maxr // size_ge0.
rewrite !big_seq &(eq_bigr) /= => i /mem_range rg_i.
by rewrite nth_mkseq.
qed.

lemma ideal_idgen (xs : t list) : ideal (idgen xs).
proof. do! split.
- by exists []; rewrite big1 //= => i _; rewrite mul0r.
- move=> x y /idgenP[cxs [szx ->]] /idgenP[cys [szy ->]].
  rewrite sumrB /=; exists (mkseq (fun i => cxs.[i] - cys.[i]) (size xs)).
  rewrite !big_seq &(eq_bigr) /= => i /mem_range rg_i.
  by rewrite nth_mkseq //= mulrBl.
- move=> a x /idgenP[cs [sz ->]]; exists (mkseq (fun i => a * cs.[i]) (size xs)).
  rewrite mulr_sumr !big_seq &(eq_bigr) /=.
  by move=> i /mem_range rg_i; rewrite nth_mkseq //= mulrA.
qed.

hint exact : ideal_idgen.

lemma mem_idgen1 x a : idgen [x] a <=> exists b, a = b * x.
proof. split => [/idgenP /= [cs]|].
- by case=> [/size_eq1[c ->] ->]; exists c; rewrite big_int1.
- by case=> c ->; exists [c] => /=; rewrite big_int1.
qed.

lemma mem_idgen1_gen x : idgen [x] x.
proof.
by rewrite mem_idgen1; exists oner; rewrite mul1r.
qed.

(* -------------------------------------------------------------------- *)
lemma le_idDl (I1 I2 J : t -> bool) :
  ideal J => I1 <= J => I2 <= J => idD I1 I2 <= J.
proof.
move=> iJ le1 le2 x [x1 x2 [+ ->]].
by case=> [/le1 Jx1 /le2 Jx2]; apply: idealD.
qed.

(* -------------------------------------------------------------------- *)
op principal (I : t -> bool) =
  exists (a : t), forall x, (I x <=> exists b, x = b * a).

lemma principal_ideal I : principal I => ideal I.
proof.
case=> a inI; suff ->: I = idgen [a] by apply/ideal_idgen.
by apply/fun_ext=> x; rewrite inI -mem_idgen1.
qed.

lemma principal_idgen1 x : principal (idgen [x]).
proof. by exists x=> y; rewrite mem_idgen1. qed.

lemma idgen1_0 : idgen [zeror] = id0.
proof.
apply/fun_ext=> x; rewrite mem_id0 mem_idgen1.
apply/eq_iff; split=> [[b ->]|->].
- by rewrite mulr0.
- by exists zeror; rewrite mulr0.
qed.

lemma principalP I : principal I <=> exists d, I = idgen [d].
proof.
split=> [|[d ->]]; last by apply/principal_idgen1.
by case=> d IE; exists d; apply/fun_ext => x; rewrite IE mem_idgen1.
qed.

lemma principal_id0 : principal id0.
proof. by rewrite -idgen1_0 &(principal_idgen1). qed.

(* -------------------------------------------------------------------- *)
lemma mem_idgen1_dvd x y : idgen [x] y <=> x %| y.
proof. by rewrite mem_idgen1 -dvdrP. qed.

lemma le_idgen1_dvd x y : x %| y <=> idgen [y] <= idgen [x].
proof.
split=> [[c ->>] y /mem_idgen1_dvd [d ->]|].
- by rewrite mulrA mem_idgen1_dvd; exists (d * c).
- move/(_ y); rewrite !mem_idgen1_dvd; apply.
  by exists oner; rewrite mul1r.
qed.

lemma in_idgen_mem xs x : x \in xs => idgen xs x.
proof.
move => x_xs; pose n := index x xs; pose cs := rcons (nseq n zeror<:t>) oner.
have get_cs : forall i, cs.[i] = if i = n then oner else zeror.
- by move => i; rewrite nth_rcons size_nseq !ler_maxr ?index_ge0 nth_nseq_if /#.
exists cs; rewrite (bigD1 _ _ n) ?big1 ?range_uniq /=.
- by rewrite mem_range index_ge0 index_mem.
- by move => i Hi; rewrite get_cs ifF // mul0r.
- by rewrite get_cs /= mul1r addr0 nth_index.
qed.

(* -------------------------------------------------------------------- *)
lemma dvdrr x : x %| x.
proof. by rewrite -mem_idgen1_dvd mem_idgen1_gen. qed.

lemma dvdr_mull d x y : d %| y => d %| x * y.
proof.
rewrite -!mem_idgen1_dvd => ?; apply/(@idealMl (idgen [d])) => //.
by apply: ideal_idgen.
qed.

lemma dvdr_mulr d x y : d %| x => d %| x * y.
proof. by move=> dx; rewrite mulrC dvdr_mull. qed.

lemma dvdr_trans : transitive (%|).
proof.
move=> z x y; rewrite !le_idgen1_dvd => h1 h2.
by apply: (subpred_trans _ _ _ h2 h1).
qed.

lemma dvdr0 x : x %| zeror.
proof. by exists zeror; rewrite mul0r. qed.

lemma dvd0r x : (zeror %| x) <=> (x = zeror).
proof.
split=> [|->]; last by exists zeror; rewrite mulr0.
by case=> ?; rewrite mulr0.
qed.

lemma eqmodP x y : (exists u, unit u /\ x = u * y) => x %= y.
proof.
case=> u [invu ->]; rewrite /(%=) dvdr_mull 1:dvdrr /=.
by apply/dvdrP; exists (invr u); rewrite mulrA mulVr // mul1r.
qed.

lemma idgen_mulVl x y : unit x => idgen [x * y] = idgen [y].
proof.
move=> invx; apply/fun_ext=> z; apply/eq_iff.
apply: subpred_eqP z => /=; split.
- by apply/le_idgen1_dvd/dvdr_mull/dvdrr.
move=> z /mem_idgen1[c ->]; apply/mem_idgen1.
by exists (c * invr x); rewrite !mulrA mulrVK.
qed.

(* -------------------------------------------------------------------- *)
lemma eqp_refl x : x %= x.
proof. by rewrite /(%=) dvdrr. qed.

lemma eqp_sym x y : x %= y => y %= x.
proof. by rewrite /(%=) andbC. qed.

lemma eqp_trans y x z : x %= y => y %= z => x %= z.
proof. by case=> [xy yx] [yz zy]; split; apply: (dvdr_trans y). qed.

(* ==================================================================== *)
abstract theory RingQuotientBase.

(* -------------------------------------------------------------------- *)
op p : t -> bool.

theory IdealAxioms.
axiom ideal_p : ideal p.
axiom ideal_Ntriv : forall x, unit x => !p x.
end IdealAxioms.

import IdealAxioms.

hint exact : ideal_p.

op eqv (x y : t) = p (y - x).

lemma eqvxx : reflexive eqv.
proof. by move=> x @/eqv; rewrite subrr ideal0 ideal_p. qed.

lemma eqv_sym : symmetric eqv.
proof. by move=> x y @/eqv; rewrite -opprB idealNP // ideal_p. qed.

lemma eqv_trans : transitive eqv.
proof.
move=> y x z @/eqv hpyx hpzy.
have ->: z - x = (z - y) + (y - x).
- by rewrite addrACA !addrA addrK.
by apply/idealD => //; apply/ideal_p.
qed.

hint exact : eqvxx.

(* -------------------------------------------------------------------- *)
lemma eqv0r x : eqv x zeror <=> p x.
proof. by rewrite eqv_sym /eqv subr0. qed.

lemma eqv0l x : eqv zeror x <=> p x.
proof. by rewrite eqv_sym &(eqv0r). qed.

lemma eqvN x y : eqv x y => eqv (-x) (-y).
proof. by rewrite /eqv -idealNP 1:ideal_p opprD. qed.

lemma eqvD x1 x2 y1 y2 : eqv x1 x2 => eqv y1 y2 => eqv (x1 + y1) (x2 + y2).
proof. by rewrite /eqv subrACA &(idealD) ideal_p. qed.

lemma eqv_sum ['a] (P : 'a -> bool) (F1 F2 : 'a -> t) r :
     (forall x, P x => eqv (F1 x) (F2 x))
  => eqv (bigA P F1 r) (bigA P F2 r).
proof.
move=> heqv; elim: r => [|x r ih].
- by rewrite !big_nil eqvxx.
rewrite !big_cons; case: (P x) => // Px.
by apply: eqvD=> //; apply: heqv.
qed.

lemma eqvMl x y1 y2 : eqv y1 y2 => eqv (x * y1) (x * y2).
proof. by rewrite /eqv -mulrBr &(idealMl) ideal_p. qed.

lemma eqvMr x1 x2 y : eqv x1 x2 => eqv (x1 * y) (x2 * y).
proof. by rewrite !(mulrC _ y) &(eqvMl). qed.

lemma eqvX x y n : 0 <= n => eqv x y => eqv (exp x n) (exp y n).
proof.
move => ge0_n eqv_x_y.
elim: n ge0_n => [|n ge0_n IHn]; rewrite ?expr0 ?exprSr //.
by apply (eqv_trans (exp x n * y)); [exact eqvMl|exact eqvMr].
qed.

(* -------------------------------------------------------------------- *)
clone include Quotient.EquivQuotient
  with type T   <- t,
         op eqv <- eqv

   proof *.

realize EqvEquiv.eqv_refl  by apply: eqvxx.
realize EqvEquiv.eqv_sym   by apply: eqv_sym.
realize EqvEquiv.eqv_trans by apply: eqv_trans.

(* -------------------------------------------------------------------- *)
op zeror = pi zeror.
op oner  = pi oner.

op ( + ) (x y : qT) = pi (repr x + repr y).
op [ - ] (x   : qT) = pi (- repr x).
op ( * ) (x y : qT) = pi (repr x * repr y).

op   invr : qT -> qT.
pred unit : qT.

lemma addE x y : (pi x) + (pi y) = pi (x + y).
proof.
rewrite /(+) &(eqv_pi) /eqv subrACA.
by rewrite &(idealD) ?ideal_p // &(eqv_repr).
qed.

lemma oppE x : -(pi x) = pi (-x).
proof.
rewrite /([-]) &(eqv_pi) /eqv opprK addrC.
by rewrite -/(eqv _ _) eqv_sym &(eqv_repr).
qed.

lemma mulE x y : (pi x) * (pi y) = pi (x * y).
proof.
rewrite &(eqv_pi) /eqv; pose z := repr (pi x).
have ->: x = x - z + z by rewrite subrK.
rewrite mulrDl -addrA -mulrBr (mulrC _ y) {1}/z.
by rewrite &(idealD) ?ideal_p // idealMl ?ideal_p &(eqv_repr).
qed.

lemma addrA : associative (+).
proof.
elim/quotW=> x; elim/quotW=> y; elim/quotW=> z.
by rewrite !addE &(eqv_pi) !addrA !eqvD // 1:eqv_sym &(eqv_repr).
qed.

lemma addrC : commutative (+).
proof.
by elim/quotW=> x; elim/quotW=> y; rewrite !addE addrC.
qed.

lemma add0r : left_id zeror (+).
proof. by elim/quotW=> x; rewrite !addE add0r. qed.

lemma addNr : left_inverse zeror [-] (+).
proof.
elim/quotW=> x; rewrite !addE &(eqv_pi) addrC.
by apply/eqv0r/eqv_repr.
qed.

lemma addrN : right_inverse zeror [-] (+).
proof. by move=> x; rewrite addrC; apply: addNr. qed.

lemma oner_neq0 : oner <> zeror.
proof. by rewrite -eqv_pi eqv0r; apply/ideal_Ntriv/unitr1. qed.

lemma mulrA : associative ( * ).
proof.
elim/quotW=> x; elim/quotW=> y; elim/quotW=> z.
rewrite !mulE &(eqv_pi) !mulrA.
apply: (eqv_trans (x * (repr (pi y)) * z)).
- by apply/eqvMl/eqv_repr.
- by apply/eqvMr/eqvMr; rewrite eqv_sym &(eqv_repr).
qed.

lemma mulrC : commutative ( * ).
proof. by elim/quotW=> x; elim/quotW=> y; rewrite !mulE mulrC. qed.

lemma mul1r: left_id oner ( * ).
proof. by elim/quotW=> x; rewrite mulE mul1r. qed.

lemma mulrDl : left_distributive ( * ) ( + ).
proof.
elim/quotW=> x1; elim/quotW=> x2; elim/quotW=> y.
rewrite !(addE, mulE) &(eqv_pi) -mulrDl.
apply: (eqv_trans ((x1 + x2) * (repr (pi y)))).
- by apply/eqvMl; rewrite eqv_sym &(eqv_repr).
- by apply/eqvMr/eqvD; rewrite eqv_sym &(eqv_repr).
qed.

end RingQuotientBase.

(* ==================================================================== *)
abstract theory RingQuotientDflInv.
clone include RingQuotientBase.

(* choiceb-default inverse, mirroring [Ring.ComRingDflInv]. *)
op qunit (x : qT) : bool = exists y, y * x = oner.
op qinvr (x : qT) : qT = choiceb (fun y => y * x = oner) x.

instance comring with qT
  op zeror = zeror
  op (+)   = (+)
  op [-]   = [-]
  op oner  = oner
  op ( * ) = ( * )
  op invr  = qinvr
  op unit  = qunit.

realize mopA<:addmonoid> by exact: addrA.
realize mopC<:addmonoid> by exact: addrC.
realize mop0<:addmonoid> by exact: add0r.
realize addrN by exact: addrN.
realize oner_neq0 by exact: oner_neq0.
realize mopA<:mulmonoid> by exact: mulrA.
realize mopC<:mulmonoid> by exact: mulrC.
realize mop0<:mulmonoid> by exact: mul1r.
realize mulrDl by exact: mulrDl.

realize mulVr.
proof.
move=> x ^ un_x [y ^ -> <-] @/qinvr.
by have /= -> := choicebP _ x un_x.
qed.

realize unitP.
proof. by move=> x y eq; exists y. qed.

realize unitout.
proof.
by move=> x; rewrite /qunit /qinvr negb_exists => /choiceb_dfl /(_ x).
qed.

end RingQuotientDflInv.

(* ==================================================================== *)
abstract theory RingQuotient.
clone include RingQuotientBase.
axiom mulVr   : left_inverse_in unit oner invr ( * ).
axiom unitP   : forall (x y : qT), y * x = oner => unit x.
axiom unitout : forall (x : qT), !unit x => invr x = x.

instance comring with qT
  op zeror = zeror
  op (+)   = (+)
  op [-]   = [-]
  op oner  = oner
  op ( * ) = ( * )
  op invr  = invr
  op unit  = unit.

realize mopA<:addmonoid> by exact: addrA.
realize mopC<:addmonoid> by exact: addrC.
realize mop0<:addmonoid> by exact: add0r.
realize addrN by exact: addrN.
realize oner_neq0 by exact: oner_neq0.
realize mopA<:mulmonoid> by exact: mulrA.
realize mopC<:mulmonoid> by exact: mulrC.
realize mop0<:mulmonoid> by exact: mul1r.
realize mulrDl by exact: mulrDl.
realize mulVr by apply: mulVr.
realize unitP by apply: unitP.
realize unitout by apply: unitout.

end RingQuotient.

end TcIdealComRing.

(* ==================================================================== *)
abstract theory TcIdeal.
type t <: idomain.

clone include TcIdealComRing with type t <- t.

lemma eqmodfP x y : (x %= y) <=> (exists u, unit u /\ x = u * y).
proof.
split=> [[dxy dyx]|[u [invu ->]]]; last first.
- rewrite /(%=) dvdr_mull 1:dvdrr /=; apply/dvdrP.
  by exists (invr u); rewrite mulrA mulVr // mul1r.
case: (y = zeror) => [->>|nz_y].
- rewrite (_ : x = zeror) 1:-dvd0r //.
  by exists oner; rewrite mul1r /= unitr1.
case/dvdrP: dyx=> u xE; exists u; rewrite xE eq_refl /=.
apply/unitrP; case/dvdrP: dxy=> v yE; exists v.
by apply: (mulIf y) => //; rewrite mul1r -mulrA -xE yE.
qed.

(* -------------------------------------------------------------------- *)
lemma eqmodf_idP x y : (x %= y) <=> (idgen [x] = idgen [y]).
proof.
split; first by case/eqmodfP=> [u [invu ->]]; rewrite idgen_mulVl.
move=> eq; have: idgen[x] <= idgen[y] /\ idgen[y] <= idgen[x].
- by apply/subpred_eqP=> z; rewrite eq.
by case=> /le_idgen1_dvd dyx /le_idgen1_dvd dxy.
qed.

(* -------------------------------------------------------------------- *)
lemma eqpf0P x : (x %= zeror) <=> (x = zeror).
proof.
split=> [/eqmodfP[u [_ ->]]|]; first by rewrite mulr0.
by move=> ->; apply/eqp_refl.
qed.

end TcIdeal.
