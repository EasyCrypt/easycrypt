(* -------------------------------------------------------------------- *)
require import AllCore List Ring StdOrder Quotient Bigalg Binomial.
(*---*) import IntOrder.

(* ==================================================================== *)
abstract theory IdealRing.
(* -------------------------------------------------------------------- *)
type t.

clone import Ring.ComRing  as IComRing with type t <- t.

clear [IComRing.* IComRing.AddMonoid.* IComRing.MulMonoid.*].

clone import Bigalg.BigComRing as BigDom with
  type  CR.t      <- t,
    op  CR.zeror  <- IComRing.zeror,
    op  CR.oner   <- IComRing.oner,
    op  CR.(+)    <- IComRing.(+),
    op  CR.([-])  <- IComRing.([-]),
    op  CR.( * )  <- IComRing.( * ),
    op  CR.invr   <- IComRing.invr,
    op  CR.intmul <- IComRing.intmul,
    op  CR.ofint  <- IComRing.ofint,
    op  CR.exp    <- IComRing.exp,
    op  CR.lreg   <- IComRing.lreg,
  pred  CR.unit   <- IComRing.unit
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

clear [BigDom.* BigDom.BAdd.* BigDom.BMul.*].

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

lemma idealV I x : ideal I => I x => I (invr x).
proof.
move=> iI Ix; case: (unit x) => [/unitrE eq_|/invr_out -> //].
move: (idealMl _ (invr x * invr x) _ iI Ix).
by rewrite -mulrA (mulrC _ x) eq_ mulr1.
qed.

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
op prime_id I = ideal I /\ forall (a b : t) , I (a * b) => I a \/ I b.

(* -------------------------------------------------------------------- *)
op max_id I =
  ideal I /\
  I <> idT /\
  forall J , ideal J => J <> idT => (forall x , I x => J x) => I = J.

lemma max_prime_id I : max_id I => prime_id I.
proof.
case=> iI [] neqIT forall_; split=> // a b Iab.
move/(_ (idD I (idgen [a]))): forall_.
case: (I a) => //= NIa; case (I b) => //= NIb.
rewrite ideal_idD ?ideal_idgen //=.
rewrite !negb_imply (andbC _ (_ <> _)) ; do!split.
+ move: neqIT; apply/implybNN; rewrite !fun_ext => + c.
  move/(_ oner); rewrite !mem_idT !eqT.
  case => ? ? [] [] I_ /mem_idgen1 [d] ->>.
  rewrite -subr_eq => <<-.
  move: (idealD _ _ _ iI ((idealMl _ d _ iI Iab)) (idealMr _ _ b iI I_)).
  by rewrite mulrDl mulNr mul1r mulrA addrA addrAC subrr add0r.
+ apply/negP => /fun_ext /(_ a); rewrite NIa /= eq_sym neqF /=.
  by exists zeror a; rewrite ideal0 // mem_idgen1_gen add0r.
move=> c Ic; exists c zeror; rewrite Ic addr0 mem_idgen1 /=.
by exists zeror; rewrite mul0r.
qed.

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
move => x_xs; pose n := index x xs; pose cs := rcons (nseq n zeror) oner. 
have get_cs : forall i, cs.[i] = if i = n then oner else zeror. 
- by move => i; rewrite nth_rcons size_nseq !ler_maxr ?index_ge0 nth_nseq_if /#.
exists cs; rewrite (BAdd.bigD1 _ _ n) ?BAdd.big1 ?range_uniq /=.
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
abstract theory ComRingQuotient.
type qT.

(* -------------------------------------------------------------------- *)
op p : t -> bool.

theory IdealAxioms.
axiom ideal_p : ideal p.
axiom neq_p_idT : p <> idT.
end IdealAxioms.

lemma ideal_Ntriv x : unit x => !p x.
proof.
by move=> ux; rewrite (ideal_eq1P _ _ IdealAxioms.ideal_p ux) IdealAxioms.neq_p_idT.
qed.

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

lemma eqvM x1 x2 y1 y2 : eqv x1 x2 => eqv y1 y2 => eqv (x1 * y1) (x2 * y2).
proof. by move => eqvx eqvy; apply/(eqv_trans (x1 * y2)); [apply/eqvMl|apply/eqvMr]. qed.

lemma eqvUI x y :
  unit x =>
  unit y =>
  eqv x y =>
  eqv (invr x) (invr y).
proof.
  move => unitx unity; rewrite /eqv => pxy.
  move: (idealMl _ (- invr x * invr y) _ ideal_p pxy).
  rewrite mulNr -mulrN opprD opprK (addrC _ x) mulrDr.
  rewrite mulrAC (mulrC _ x) divrr // div1r mulrN.
  by rewrite -mulrA (mulrC _ y) divrr // mulr1.
qed.

lemma eqvNUI x y :
  !unit x =>
  !unit y =>
  eqv x y =>
  eqv (invr x) (invr y).
proof. by move => unitx unity eqvxy; rewrite !invr_out. qed.

lemma eqvUX x y n :
  unit x =>
  unit y =>
  eqv x y =>
  eqv (exp x n) (exp y n).
proof.
  move => unitx unity; wlog: n / 0 <= n => [wlog|].
  + move => eqvxy; case: (0 <= n) => [le0n|/ltzNge/oppr_gt0/ltzW le0Nn]; [by apply/wlog|].
    by rewrite -(oppzK n) exprN eqv_sym exprN eqv_sym; apply/eqvUI; rewrite ?unitrX //; apply/wlog.
  elim: n => [|n le0n IHn eqvxy]; [by rewrite !expr0 eqvxx|].
  by rewrite !exprS //; apply/eqvM => //; apply/IHn.
qed.

lemma eqvNUX x y n :
  !unit x =>
  !unit y =>
  eqv x y =>
  eqv (exp x n) (exp y n).
proof.
  move => unitx unity; wlog: n / 0 <= n => [wlog|].
  + move => eqvxy; case: (0 <= n) => [le0n|/ltzNge/oppr_gt0 lt0Nn]; [by apply/wlog|].
    rewrite -(oppzK n) exprN eqv_sym exprN eqv_sym; apply/eqvNUI.
    - by move: unitx; apply/contra/unitrX_neq0/gtr_eqF.
    - by move: unity; apply/contra/unitrX_neq0/gtr_eqF.
    by apply/wlog => //; apply/ltzW.
  elim: n => [|n le0n IHn eqvxy]; [by rewrite !expr0 eqvxx|].
  by rewrite !exprS //; apply/eqvM => //; apply/IHn.
qed.

lemma eqvX x y n : 0 <= n => eqv x y => eqv (exp x n) (exp y n).
proof. 
move => ge0_n eqv_x_y.
elim: n ge0_n => [|n ge0_n IHn]; rewrite ?expr0 ?exprSr //.
by apply (eqv_trans (exp x n * y)); [exact eqvMl|exact eqvMr].
qed.

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

clone import ComRing as CRQ with
  type t   <= qT,
  op zeror <= zeror,
  op oner  <= oner,
  op ( + ) <= ( + ),
  op [ - ] <= [ - ],
  op ( * ) <= ( * )
  proof addrA, addrC, add0r, addNr, oner_neq0, mulrA, mulrC, mul1r, mulrDl.


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

end ComRingQuotient.


abstract theory IDomainQuotient.

type qT.

op p : t -> bool.

theory PrimeIdealAxioms.
axiom ideal_p : ideal p.
axiom neq_p_idT : p <> idT.
axiom prime_p : prime_id p.
end PrimeIdealAxioms.

clone include ComRingQuotient with
  type qT <- qT,
  op p <- p,
  theory IdealAxioms <- PrimeIdealAxioms.

clone import IDomain as IDQ with
  type t     <= qT   ,
  op   zeror <= zeror,
  op   ( + ) <= (+)  ,
  op   [ - ] <= [-]  ,
  op   oner  <= oner ,
  op   ( * ) <= ( * ),
  op   invr  <= CRQ.invr ,
  pred unit  <= CRQ.unit
  proof *.

realize addrA by exact CRQ.addrA.
realize addrC by exact CRQ.addrC.
realize add0r by exact CRQ.add0r.
realize addNr by exact CRQ.addNr.
realize oner_neq0 by exact CRQ.oner_neq0.
realize mulrA by exact CRQ.mulrA.
realize mulrC by exact CRQ.mulrC.
realize mul1r by exact CRQ.mul1r.
realize mulrDl by exact CRQ.mulrDl.
realize mulVr   by exact CRQ.mulVr.
realize unitP   by exact CRQ.unitP.
realize unitout by exact CRQ.unitout.

realize mulf_eq0.
proof.
move=> x y; split; [|case=> ->>; [by rewrite mul0r|by rewrite mulr0]].
rewrite -(reprK x) -(reprK y) mulE -!eqv_pi !eqv0r.
by case: PrimeIdealAxioms.prime_p => _ /(_ (repr x) (repr y)).
qed.

clear [CRQ.AddMonoid.* CRQ.MulMonoid.* CRQ.*].

end IDomainQuotient.


abstract theory FieldQuotient.

type qT.

op p : t -> bool.

theory MaximalIdealAxioms.
axiom ideal_p : ideal p.
axiom neq_p_idT : p <> idT.
axiom max_p : max_id p.
lemma prime_p : prime_id p by apply/max_prime_id/max_p.
end MaximalIdealAxioms.

clone include IDomainQuotient with
  type qT <- qT,
  op p <- p,
  theory PrimeIdealAxioms <- MaximalIdealAxioms.

clone import Field as FQ with
  type t     <= qT   ,
  op   zeror <= zeror,
  op   ( + ) <= (+)  ,
  op   [ - ] <= [-]  ,
  op   oner  <= oner ,
  op   ( * ) <= ( * ),
  op   invr  <= CRQ.invr ,
  pred unit  <= CRQ.unit
  proof *.

realize addrA by exact IDQ.addrA.
realize addrC by exact IDQ.addrC.
realize add0r by exact IDQ.add0r.
realize addNr by exact IDQ.addNr.
realize oner_neq0 by exact IDQ.oner_neq0.
realize mulrA by exact IDQ.mulrA.
realize mulrC by exact IDQ.mulrC.
realize mul1r by exact IDQ.mul1r.
realize mulrDl by exact IDQ.mulrDl.
realize mulVr   by exact IDQ.mulVr.
realize unitP   by exact IDQ.unitP.
realize unitout by exact IDQ.unitout.
realize mulf_eq0 by exact IDQ.mulf_eq0.

realize unitfP.
proof.
move=> x; apply/contraR; rewrite unitrP negb_exists /= => forall_.
case: MaximalIdealAxioms.max_p => ip [] neqpT /(_ (idD p (idgen [repr x])) _ _ _).
+ by apply/ideal_idD => //; apply/ideal_idgen.
+ apply/negP => /fun_ext /(_ IComRing.oner); rewrite mem_idT eqT.
  case=> ? ? [] [] + /mem_idgen1 [a] ->>; rewrite -subr_eq => + <<-.
  by move/eqv_pi; rewrite -mulE reprK -/FQ.oner /=; apply/forall_.
+ move=> a pa; exists a IComRing.zeror; rewrite pa addr0 /=.
  by apply/mem_idgen1; exists IComRing.zeror; rewrite mul0r.
move/fun_ext/(_ (repr x)) => eq_; have: p (repr x).
+ move: eq_ => ->; exists IComRing.zeror (repr x).
  by rewrite ideal0 // mem_idgen1_gen add0r.
by rewrite -eqv0r eqv_pi reprK -/FQ.zeror.
qed.

clear [IDQ.AddMonoid.* IDQ.MulMonoid.* IDQ.*].

end FieldQuotient.

end IdealRing.

(* ==================================================================== *)
abstract theory Ideal.
type t.

clone import IDomain with type t <- t.

clear [IDomain.* IDomain.AddMonoid.* IDomain.MulMonoid.*].

clone include IdealRing with
  type t <- t,
  theory IComRing <- IDomain.

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

