(* -------------------------------------------------------------------- *)
require import AllCore List Ring StdOrder Quotient Bigalg Binomial.
(*---*) import IntOrder.

(* ==================================================================== *)
abstract theory IdealComRing.
(* -------------------------------------------------------------------- *)
type t.

clone import Ring.ComRing as IComRing with type t <- t.

clear [IComRing.* IComRing.AddMonoid.* IComRing.MulMonoid.*].

clone import Bigalg.BigComRing as BigDom with
  type  CR.t     <- t,
    op  CR.zeror <- IComRing.zeror,
    op  CR.oner  <- IComRing.oner,
    op  CR.(+)   <- IComRing.(+),
    op  CR.([-]) <- IComRing.([-]),
    op  CR.( * ) <- IComRing.( * ),
    op  CR.invr  <- IComRing.invr,
  pred  CR.unit  <- IComRing.unit
  proof CR.*

  remove abbrev CR.(-)
  remove abbrev CR.(/).

realize CR.addrA     by exact: IComRing.addrA    .
realize CR.addrC     by exact: IComRing.addrC    .
realize CR.add0r     by exact: IComRing.add0r    .
realize CR.addNr     by exact: IComRing.addNr    .
realize CR.oner_neq0 by exact: IComRing.oner_neq0.
realize CR.mulrA     by exact: IComRing.mulrA    .
realize CR.mulrC     by exact: IComRing.mulrC    .
realize CR.mul1r     by exact: IComRing.mul1r    .
realize CR.mulrDl    by exact: IComRing.mulrDl   .
realize CR.mulVr     by exact: IComRing.mulVr    .
realize CR.unitP     by exact: IComRing.unitP    .
realize CR.unitout   by exact: IComRing.unitout  .

clear [BigDom.* BigDom.CR.* BigDom.BAdd.* BigDom.BMul.*].

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

lemma ideal_sum ['a] I P F s :
     ideal I
  => (forall x, P x => I (F x))
  => I (BAdd.big<:'a> P F s).
proof.
elim: s => [|x s ih] idI IF; first by rewrite BAdd.big_nil ideal0.
rewrite BAdd.big_cons; case: (P x) => Px; last by apply/ih.
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
  fun x => exists n, 0 <= n /\ I (IComRing.exp x n).

(* -------------------------------------------------------------------- *)
lemma mem_id0 x : id0 x <=> x = zeror.
proof. by []. qed.

(* -------------------------------------------------------------------- *)
lemma ideal_id0 : ideal id0.
proof.
rewrite /id0 /pred1; apply/idealP => //.
- by move=> x y -> -> /=; rewrite subrr.
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
  exists cs, x = BAdd.bigi predT (fun i => cs.[i] * xs.[i]) 0 (size xs).

lemma idgenP (xs : t list) (x : t) :
  idgen xs x => exists cs, size cs = size xs
    /\ x = BAdd.bigi predT (fun i => cs.[i] * xs.[i]) 0 (size xs).
proof.
case=> cs ->; exists (mkseq (fun i => cs.[i]) (size xs)); split.
- by rewrite size_mkseq ler_maxr // size_ge0.
rewrite !BAdd.big_seq &(BAdd.eq_bigr) /= => i /mem_range rg_i.
by rewrite nth_mkseq.
qed.

lemma ideal_idgen (xs : t list) : ideal (idgen xs).
proof. do! split.
- by exists []; rewrite BAdd.big1 //= => i _; rewrite mul0r.
- move=> x y /idgenP[cxs [szx ->]] /idgenP[cys [szy ->]].
  rewrite BAdd.sumrB /=; exists (mkseq (fun i => cxs.[i] - cys.[i]) (size xs)).
  rewrite !BAdd.big_seq &(BAdd.eq_bigr) /= => i /mem_range rg_i.
  by rewrite nth_mkseq //= mulrBl.
- move=> a x /idgenP[cs [sz ->]]; exists (mkseq (fun i => a * cs.[i]) (size xs)).
  rewrite BAdd.mulr_sumr !BAdd.big_seq &(BAdd.eq_bigr) /=.
  by move=> i /mem_range rg_i; rewrite nth_mkseq //= mulrA.
qed.

hint exact : ideal_idgen.

lemma mem_idgen1 x a : idgen [x] a <=> exists b, a = b * x.
proof. split => [/idgenP /= [cs]|].
- by case=> [/size_eq1[c ->] ->]; exists c; rewrite BAdd.big_int1.
- by case=> c ->; exists [c] => /=; rewrite BAdd.big_int1.
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
  exists a : t, forall x, (I x <=> exists b, x = b * a).

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
admitted.

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
abstract theory RingQuotient.
type qT.

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
proof. by move=> x @/eqv; rewrite /eqv subrr ideal0 ideal_p. qed.

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

lemma eqv_sum ['a] P F1 F2 r :
     (forall x, P x => eqv (F1 x) (F2 x))
  => eqv (BAdd.big<:'a> P F1 r) (BAdd.big<:'a> P F2 r).
proof.
move=> heqv; elim: r => [|x r ih].
- by rewrite !BAdd.big_nil eqvxx.
rewrite !BAdd.big_cons; case: (P x) => // Px.
by apply: eqvD=> //; apply: heqv.
qed.

lemma eqvMl x y1 y2 : eqv y1 y2 => eqv (x * y1) (x * y2).
proof. by rewrite /eqv -mulrBr &(idealMl) ideal_p. qed.

lemma eqvMr x1 x2 y : eqv x1 x2 => eqv (x1 * y) (x2 * y).
proof. by rewrite !(mulrC _ y) &(eqvMl). qed.

lemma eqvX x y n : eqv x y => eqv (exp x n) (exp y n).
proof. admitted.

(* -------------------------------------------------------------------- *)
clone include Quotient.EquivQuotient
  with type T   <- t,
       type qT  <- qT,
         op eqv <- eqv

   proof EqvEquiv.*.

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
rewrite /(+) &(eqv_pi) /eqv; pose z := repr (pi x).
have ->: x = x - z + z by rewrite subrK.
rewrite mulrDl -addrA -mulrBr (mulrC _ y) {1}/z.
by rewrite &(idealD) ?ideal_p // idealMl ?ideal_p &(eqv_repr).
qed.

axiom mulVr   : left_inverse_in unit oner invr ( * ).
axiom unitP   : forall (x y : qT), y * x = oner => unit x.
axiom unitout : forall (x : qT), !unit x => invr x = x.

clone import ComRing with
  type t     <- qT   ,
  op   zeror <- zeror,
  op   ( + ) <- (+)  ,
  op   [ - ] <- [-]  ,
  op   oner  <- oner ,
  op   ( * ) <- ( * ),
  op   invr  <- invr ,
  pred unit  <- unit

  proof *.

realize addrA.
proof.
elim/quotW=> x; elim/quotW=> y; elim/quotW=> z.
by rewrite !addE &(eqv_pi) !addrA !eqvD // 1:eqv_sym &(eqv_repr).
qed.

realize addrC.
proof.
by elim/quotW=> x; elim/quotW=> y; rewrite !addE addrC.
qed.

realize add0r.
proof. by elim/quotW=> x; rewrite !addE add0r. qed.

realize addNr.
proof.
elim/quotW=> x; rewrite !addE &(eqv_pi) addrC.
by apply/eqv0r/eqv_repr.
qed.

realize oner_neq0.
proof. by rewrite -eqv_pi eqv0r; apply/ideal_Ntriv/unitr1. qed.

realize mulrA.
proof.
elim/quotW=> x; elim/quotW=> y; elim/quotW=> z.
rewrite !mulE &(eqv_pi) !mulrA.
apply: (eqv_trans (x * (repr (pi y)) * z)).
- by apply/eqvMl/eqv_repr.
- by apply/eqvMr/eqvMr; rewrite eqv_sym &(eqv_repr).
qed.

realize mulrC.
proof. by elim/quotW=> x; elim/quotW=> y; rewrite !mulE mulrC. qed.

realize mul1r.
proof. by elim/quotW=> x; rewrite mulE mul1r. qed.

realize mulrDl.
proof.
elim/quotW=> x1; elim/quotW=> x2; elim/quotW=> y.
rewrite !(addE, mulE) &(eqv_pi) -mulrDl.
apply: (eqv_trans ((x1 + x2) * (repr (pi y)))).
- by apply/eqvMl; rewrite eqv_sym &(eqv_repr).
- by apply/eqvMr/eqvD; rewrite eqv_sym &(eqv_repr).
qed.

realize mulVr   by apply: mulVr.
realize unitP   by apply: unitP.
realize unitout by apply: unitout.
end RingQuotient.
end IdealComRing.

(* ==================================================================== *)
abstract theory Ideal.
type t.

clone import IDomain with type t <- t.

clear [IDomain.* IDomain.AddMonoid.* IDomain.MulMonoid.*].

clone include IdealComRing with
  type t               <- t,
  pred IComRing.unit   <- IDomain.unit,
    op IComRing.zeror  <- IDomain.zeror,
    op IComRing.oner   <- IDomain.oner,
    op IComRing.( + )  <- IDomain.( + ),
    op IComRing.([-])  <- IDomain.([-]),
    op IComRing.( * )  <- IDomain.( * ),
    op IComRing.invr   <- IDomain.invr,
    op IComRing.intmul <- IDomain.intmul,
    op IComRing.ofint  <- IDomain.ofint,
    op IComRing.exp    <- IDomain.exp,
    op IComRing.lreg   <- IDomain.lreg

  proof IComRing.*

  remove abbrev IComRing.(-)
  remove abbrev IComRing.(/).

realize IComRing.addrA     by apply: IDomain.addrA    .
realize IComRing.addrC     by apply: IDomain.addrC    .
realize IComRing.add0r     by apply: IDomain.add0r    .
realize IComRing.addNr     by apply: IDomain.addNr    .
realize IComRing.oner_neq0 by apply: IDomain.oner_neq0.
realize IComRing.mulrA     by apply: IDomain.mulrA    .
realize IComRing.mulrC     by apply: IDomain.mulrC    .
realize IComRing.mul1r     by apply: IDomain.mul1r    .
realize IComRing.mulrDl    by apply: IDomain.mulrDl   .
realize IComRing.mulVr     by apply: IDomain.mulVr    .
realize IComRing.unitP     by apply: IDomain.unitP    .
realize IComRing.unitout   by apply: IDomain.unitout  .

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
end Ideal.
