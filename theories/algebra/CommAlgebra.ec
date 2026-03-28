(* -------------------------------------------------------------------- *)
require import AllCore StdOrder Finite IntDiv IntMin List Ring Bigalg.
require (*--*) Ideal.
(* - *) import IntOrder.

pragma +implicits.

(* -------------------------------------------------------------------- *)
clone import IDomain.

(* -------------------------------------------------------------------- *)
clone Ideal.Ideal as I with
  type t <- IDomain.t,
  theory IDomain <= IDomain.

(* -------------------------------------------------------------------- *)
abbrev (+) = I.idD.

(* -------------------------------------------------------------------- *)
clone BigComRing as BR
  with theory CR <= IDomain,
       op     BAdd.big ['a] <= I.BigDom.BAdd.big<:'a>,
       op     BMul.big ['a] <= I.BigDom.BMul.big<:'a>.

(* -------------------------------------------------------------------- *)
import I.

(* -------------------------------------------------------------------- *)
hint simplify [reduce] addr0, add0r.
hint simplify [reduce] mulr0, mul0r.
hint simplify [reduce] mulr1, mul1r.

hint simplify [reduce] andbb, orbb.

(* -------------------------------------------------------------------- *)
hint exact : dvdrr.
hint exact : ideal_idgen.

(* -------------------------------------------------------------------- *)
lemma eqmodf1P (x : t) : (unit x) <=> (x %= oner).
proof.
split; first by move=> unit_x; apply/eqmodfP; exists x.
by case/eqmodfP=> y [unit_y ->].
qed.

(* -------------------------------------------------------------------- *)
lemma dvdr_eqpL (x y z : t) : x %| z => x %= y => y %| z.
proof.
case=> [c ->>] /eqmodfP[u] [unit_u ->>].
by exists (c * u); rewrite mulrA.
qed.

(* -------------------------------------------------------------------- *)
lemma dvdr_eqpR (x y z : t) : x %| y => y %= z => x %| z.
proof.
case=> [c ->>] /eqp_sym /eqmodfP[u] [unit_u ->>].
by rewrite mulrA dvdr_mull dvdrr.
qed.

(* -------------------------------------------------------------------- *)
lemma dvdr_add (x y z : t) : x %| y => x %| z => x %| (y + z).
proof. by move=> [cy ->] [cz ->]; exists (cy + cz); rewrite mulrDl. qed.

(* -------------------------------------------------------------------- *)
lemma predeq_leP ['a] (p1 p2 : 'a -> bool) :
  (p1 <= p2 /\ p2 <= p1) <=> (p1 = p2).
proof. smt(). qed.

(* -------------------------------------------------------------------- *)
lemma le_idDrL (I J1 J2 : t -> bool) :
  ideal J2 => I <= J1 => I <= J1 + J2.
proof. by move=> idJ2 le_I_J2 x Ix; exists x zeror; do! split=> //#. qed.

(* -------------------------------------------------------------------- *)
lemma le_idDrR (I J1 J2 : t -> bool) :
  ideal J1 => I <= J2 => I <= J1 + J2.
proof. by move=> 2?; rewrite idDC; apply/le_idDrL. qed.

(* -------------------------------------------------------------------- *)
hint exact : ideal_idgen.
hint exact : mem_idgen1_gen.

hint simplify [reduce] mem_id0.

(* -------------------------------------------------------------------- *)
lemma addi0 (I : t -> bool) : I + id0 = I.
proof.
apply/fun_ext => x /=; apply/eq_iff; split.
- by case=> y z [#] Iy /mem_id0 -> ->.
- by move=> Ix; exists x zeror.
qed.

hint simplify [reduce] addi0.

(* -------------------------------------------------------------------- *)
op w : t -> int.

axiom ge0_w : forall x, 0 <= w x.
axiom eq0_wP : forall x, w x = 0 <=> x = zeror.
axiom dvdw : forall (x y : t), x %| y => w x <= w y.

axiom Euclide :
  forall x y, y <> zeror =>
    exists q r, x = y * q + r /\ w r < w y.

(* -------------------------------------------------------------------- *)
hint exact : ge0_w.

(* -------------------------------------------------------------------- *)
op coprime (x y : t) =
  forall a, a %| x => a %| y => unit a.

(* -------------------------------------------------------------------- *)
lemma coprimeC (x y : t) : coprime x y <=> coprime y x.
proof. smt(). qed.

(* -------------------------------------------------------------------- *)
lemma Ncoprime0 : coprime zeror zeror => false.
proof.
move/(_ zeror _ _); 1,2: by apply/dvdr0.
by apply/unitr0.
qed.

(* -------------------------------------------------------------------- *)
lemma idfunE ['a] (x : 'a) : idfun x = x.
proof. done. qed.

hint simplify idfunE.

(* -------------------------------------------------------------------- *)
lemma principal (I : t -> bool) : ideal I => principal I.
proof.
move=> idI; case: (I = pred1 zeror) => [->|nzI]; first by exists zeror.
have [x [Ix nz_x]]: exists a, I a /\ a <> zeror by apply: contraR nzI => /#.
pose P k := exists x, x <> zeror /\ I x /\ w x = k.
have := argminP_r<:int> idfun P (w x) _ _ => //=; ~-1: smt().
move: (argmin _ _) => n [# ge0_n [a [# nz_a Ia waE]] min_a].
exists a => y; split; last by case=> b ->; apply/idealMl.
move=> Iy; have [q r] [yE lt_w] := Euclide y a nz_a.
have rE: r = y - a * q by rewrite yE; ring.
have Ir: I r by rewrite rE; apply/idealB=> //; apply/idealMr.
case: (r = zeror) => [->>|nz_r].
- by exists q; rewrite yE mulrC addr0.
have: P (w r) by exists r; split=> //.
by rewrite min_a //; smt(ge0_w).
qed.

(* -------------------------------------------------------------------- *)
op isgcd (a b d : t) =
  if   a = zeror /\ b = zeror
  then d = zeror
  else d %| a /\ d %| b /\ (forall d', d' %| a => d' %| b => d' %| d).

(* -------------------------------------------------------------------- *)
lemma isgcdW (P : t -> t -> t -> bool) :
     P zeror zeror zeror
  => (forall a b d,
           a <> zeror \/ b <> zeror
        => d %| a
        => d %| b
        => (forall d', d' %| a => d' %| b => d' %| d)
        => P a b d)
  => forall a b d, isgcd a b d => P a b d.
proof. by move=> /#. qed.

(* -------------------------------------------------------------------- *)
lemma gcd (a b : t) : exists d, isgcd a b d.
proof.
rewrite /isgcd; case (a = zeror /\ b = zeror).
- by case=> ->> ->>; exists zeror.
move=> _; pose M := idgen [a] + idgen[b].
have /principal: ideal M by apply/ideal_idD; apply/ideal_idgen.
case=> d /= ME; exists d; do! split.
- by rewrite /(%|) -ME /M mem_idDl //; solve.
- by rewrite /(%|) -ME /M mem_idDr //; solve.
move=> d' [a' aE] [b' bE]; apply/dvdrP.
have: M d; first by rewrite ME; exists oner.
case=> xa xb [#] /mem_idgen1[ca ->>] /mem_idgen1[cb ->>] ->>.
by rewrite aE bE !mulrA -mulrDl /#.
qed.

(* -------------------------------------------------------------------- *)
lemma isgcd_nzP (a b d : t) : (a <> zeror \/ b <> zeror) =>
  isgcd a b d <=> (d %| a /\ d %| b /\ (forall d', d' %| a => d' %| b => d' %| d)).
proof. smt(). qed.

(* -------------------------------------------------------------------- *)
lemma isgcd0 : isgcd zeror zeror zeror.
proof. done. qed.

(* -------------------------------------------------------------------- *)
lemma isgcd_refl (x : t) : isgcd x x x.
proof. by case: (x = zeror) => [->>//|nz_x]; apply/isgcd_nzP. qed.

(* -------------------------------------------------------------------- *)
lemma isgcd_sym (x y d : t) : isgcd x y d  => isgcd y x d.
proof.
move: x y d; apply: isgcdW => //= a b d nz dvda dvdb mind.
by apply/isgcd_nzP => /#.
qed.

(* -------------------------------------------------------------------- *)
lemma idD_idgen (xs ys : t list) : idgen xs + idgen ys = idgen (xs ++ ys).
proof.
apply/predeq_leP; split=> z @/idD.
- case=> cx cy [+ ->] - [].
  case/idgenP=> csx [eqx ->]; case/idgenP=> csy [eqy ->].
  exists (csx ++ csy); rewrite size_cat &(eq_sym).
  rewrite (@BR.BAdd.big_cat_int (size xs)) ~-1:#smt:(size_ge0); congr.
  - by apply: BR.BAdd.eq_big_int => i [_ lti] /=; rewrite !nth_cat eqx lti.
  rewrite (@BR.BAdd.big_addn 0 _ (size xs)) addrAC /=.
  apply: BR.BAdd.eq_big_int => /= i [ge0i lti].
  by rewrite !nth_cat -!addrA /= eqx ltzNge lez_addr ge0i.
- case/idgenP=> cs [sz_cs ->].
  pose csx := take (size xs) cs; pose csy := drop (size xs) cs.
  pose x := BigDom.BAdd.bigi predT (fun (i : int) => csx.[i] * xs.[i]) 0 (size xs).
  pose y := BigDom.BAdd.bigi predT (fun (i : int) => csy.[i] * ys.[i]) 0 (size ys).
  exists x y; rewrite size_cat; split.
  - by split; [exists csx | exists csy].
  rewrite (@BR.BAdd.big_cat_int (size xs)) ~-1:#smt:(size_ge0); congr.
  - apply: BR.BAdd.eq_big_int => i [_ lti] /=; rewrite nth_cat lti /=.
    by rewrite /csx nth_take ?size_ge0.
  - rewrite (@BR.BAdd.big_addn 0 _ (size xs)) addrAC /=.
    apply: BR.BAdd.eq_big_int => i [ge0i lti] /=; rewrite nth_cat.
    rewrite ltzNge lez_addr ge0i /= -addrA /=.
    by rewrite /csy nth_drop ?size_ge0 // [size xs + i]addrC.
qed.

(* -------------------------------------------------------------------- *)
lemma big_int2 (F : int -> t) : BR.BAdd.bigi predT F 0 2 = F 0 + F 1.
proof.
by rewrite (@BR.BAdd.big_int_recr 1) // (@BR.BAdd.big_int_recr 0) // BR.BAdd.big_geq .
qed.

(* -------------------------------------------------------------------- *)
lemma mem_idgen2 (x y a : t) :
 idgen [x; y] a <=> exists (cx cy : t), a = cx * x + cy * y.
proof. split.
- by case=> cs -> /=; exists cs.[0] cs.[1]; rewrite big_int2.
- by case=> cx cy ->; exists [cx; cy]; rewrite big_int2.
qed.

(* -------------------------------------------------------------------- *)
lemma principalP (I : t -> bool) :
  principal I <=> exists x, I = idgen [x].
proof. split; case=> x h; exists x.
- by apply/fun_ext=> y; rewrite h -mem_idgen1.
- by move=> y; rewrite h -mem_idgen1.
qed.

(* -------------------------------------------------------------------- *)
lemma le_idgen_dvd (x : t) (ys : t list) :
  (forall y, y \in ys => x %| y) <=> idgen ys <= idgen [x].
proof.
split=> h; last first.
- by move=> y /in_idgen_mem /h /mem_idgen1_dvd.
move=> y /idgenP [cs] [eqsz ->]; rewrite mem_idgen1.
pose F y := choiceb (fun c => y = c * x) y.
pose ds := map (fun y => F y) ys.
pose d := BR.BAdd.bigi predT (fun i => cs.[i] * ds.[i]) 0 (size ys).
exists d => @/d; rewrite BR.BAdd.mulr_suml &(BR.BAdd.eq_big_int) /=.
move=> i [ge0i lti]; rewrite -mulrA; congr => @/ds.
rewrite (@nth_map zeror) //=.
have // := choicebP (fun c => ys.[i] = c * x) ys.[i] _ => /=.
have := h ys.[i] _; first by rewrite mem_nth.
by case/dvdrP=> q ->; exists q; rewrite mulrC.
qed.

(* -------------------------------------------------------------------- *)
hint simplify subpred_refl.

(* -------------------------------------------------------------------- *)
lemma isgcdP (a b d : t) :
  isgcd a b d => idgen [a] + idgen [b] = idgen [d].
proof.
move: a b d; apply/isgcdW => /=; first by rewrite idgen1_0.
move=> a b d nz dvda dvdb mind; apply: predeq_leP; split.
- by (apply: le_idDl; first by solve); apply/le_idgen1_dvd.
rewrite idD_idgen /=; have: ideal (idgen [a; b]) by apply/ideal_idgen.
case/principal/principalP=> y ^id_eq ->.
have := le_idgen_dvd y [a; b]; rewrite id_eq /= => dvdy.
by apply/le_idgen1_dvd/mind; apply/dvdy.
qed.

(* -------------------------------------------------------------------- *)
lemma uniq_gcd (a b d1 d2 : t) : isgcd a b d1 => isgcd a b d2 => d1 %= d2.
proof.
rewrite /isgcd; case: (_ /\ _) => //=.
move=> [# dvd_d1a dvd_d1b mind1] [# dvd_d2a dvd_d2b mind2].
by split; [apply mind2 | apply mind1].
qed.

(* -------------------------------------------------------------------- *)
lemma isgcdsim (a b d1 d2 : t) : isgcd a b d1 => d1 %= d2 => isgcd a b d2.
proof.
move=> h; move: a b d1 h d2; apply: isgcdW => /= => [d2 |a b d1].
- by move/eqp_sym=> /eqpf0P ->.
move=> nz dvda dvdb min_d1 d2 eqd; apply/isgcd_nzP => //; do! split.
- by apply/(dvdr_eqpL _ dvda). - by apply/(dvdr_eqpL _ dvdb).
by move=> d' dvda' dvdb'; apply/(dvdr_eqpR _ _ eqd)/min_d1.
qed.

(* -------------------------------------------------------------------- *)
lemma Bezout (a b d : t) : isgcd a b d =>
  exists ca cb, ca * a + cb * b = d.
proof.
move/isgcdP=> eqid; have: idgen [d] d by apply/mem_idgen1_gen.
rewrite -eqid; case=> [ca cb] [#] + + ->>.
by move=> /mem_idgen1[ca' ->>] /mem_idgen1[cb' ->>]; exists ca' cb'.
qed.

(* -------------------------------------------------------------------- *)
lemma coprime_isgcdP (x y : t) : isgcd x y oner <=> coprime x y.
proof. split.
- case/Bezout=> [cx cy] eq z dvd_za dvd_zb.
  have: z %| oner by rewrite -eq dvdr_add dvdr_mull.
  by case=> zI /eq_sym /unitP.
- case: (x = zeror /\ y = zeror); first by case=> ->> ->> /Ncoprime0.
  move=> /negb_and nz; case: (gcd x y) => d ^hgcd /(isgcd_nzP _ _ _ nz).
  by move=> [#] dvdx dvdy _ /(_ d dvdx dvdy) /eqmodf1P /(isgcdsim _ _ _ _ hgcd).
qed.

(* -------------------------------------------------------------------- *)
lemma isgcd00 d : isgcd zeror zeror d => d = zeror.
proof. done. qed.

(* -------------------------------------------------------------------- *)
lemma dvdr_mul (a b a' b' : t) : a %| b => a' %| b' => a * a' %| b * b'.
proof.
move=> /dvdrP[d ->] /dvdrP[d' ->]; rewrite mulrACA.
by apply/dvdrP; exists (d * d').
qed.

(* -------------------------------------------------------------------- *)
lemma isgcd0r (a : t) : isgcd zeror a a.
proof.
rewrite /isgcd /=; case: (a = zeror) => // _.
by rewrite dvdr0 dvdrr.
qed.

(* -------------------------------------------------------------------- *)
lemma isgcdr0 (a : t) : isgcd a zeror a.
proof. by rewrite isgcd_sym isgcd0r. qed.

(* -------------------------------------------------------------------- *)
hint exact : isgcd0r isgcdr0.

(* -------------------------------------------------------------------- *)
lemma isgcd0r_eqm (a b : t) : isgcd zeror a b <=> a %= b.
proof.
split.
- by have := isgcd0r a; apply: uniq_gcd.
- by have := isgcd0r a; apply: isgcdsim.
qed.

(* -------------------------------------------------------------------- *)
lemma isgcdr0_eqm (a b : t) : isgcd a zeror b <=> a %= b.
proof.
split.
- by move/isgcd_sym/isgcd0r_eqm.
- by move/isgcd0r_eqm/isgcd_sym.
qed.

(* -------------------------------------------------------------------- *)
lemma eqp_mulr (c a b : t) : a %= b => a * c %= b * c.
proof.
case/eqmodfP=> u [unit_u ->]; rewrite -mulrA.
by apply/eqmodfP; exists u.
qed.

(* -------------------------------------------------------------------- *)
lemma dvdr_isgcdl (a b d : t) : isgcd a b d => d %| a.
proof. by move: a b d; apply/isgcdW. qed.

(* -------------------------------------------------------------------- *)
lemma dvdr_isgcdr (a b d : t) : isgcd a b d => d %| b.
proof. by move: a b d; apply/isgcdW. qed.

(* -------------------------------------------------------------------- *)
lemma dvdrD (d a b : t) : d %| a => d %| b => d %| (a + b).
proof. by move=> /dvdrP[ca ->] /dvdrP[cb ->]; rewrite -mulrDl dvdr_mull. qed.

(* -------------------------------------------------------------------- *)
lemma isgcdMr (a b c : t) (da d : t) :
  isgcd (b * a) (c * a) da => isgcd b c d => da %= a * d.
proof.
case: (a = zeror) => [-> /= /isgcd00 ->//|nz_a].
case: (b = zeror /\ c = zeror).
- by case=> [-> ->] /= /isgcd00 -> /isgcd00 ->.
move=> nz_bAc hgcda hgcd; apply/eqp_sym/(uniq_gcd _ _ _ hgcda).
rewrite /isgcd iffalse ?mulf_eq0 1:/#; do! split.
- by rewrite [a*_]mulrC dvdr_mul //; apply: dvdr_isgcdl hgcd.
- by rewrite [a*_]mulrC dvdr_mul //; apply: dvdr_isgcdr hgcd.
move=> d' d'_ba d'_ca; case: (Bezout _ _ _ hgcd) => cb cc <-.
by rewrite mulrDr !(mulrCA a) ![a*_]mulrC dvdrD dvdr_mull.
qed.

(* -------------------------------------------------------------------- *)
lemma dvd_gcd (a b c d : t) :
  isgcd b c d => a %| b => a %| c => a %| d.
proof.
rewrite /isgcd; case: (_ /\ _) => /=.
- by move=> -> _ _; apply: dvdr0. - by move=> [#] _ _; apply.
qed.

(* -------------------------------------------------------------------- *)
lemma Gauss (a b c : t) : a %| b * c => coprime a b => a %| c.
proof.
move=> dvd_a_bc /coprime_isgcdP cop_ab.
have dvd_a_ac: a %| a * c by apply: dvdr_mulr.
have [d gcd_d] := gcd (a * c) (b * c).
have: d %= c by rewrite -[c]mulr1 &(isgcdMr _ _ gcd_d cop_ab).
by apply/dvdr_eqpR/(dvd_gcd _ _ gcd_d).
qed.

(* -------------------------------------------------------------------- *)
op isdecomp (x : t) (xs : t list) =
  x = BR.BMul.big predT idfun xs.

(* -------------------------------------------------------------------- *)
op irreducible (x : t) =
  (x <> zeror /\ !unit x) /\ forall y, y %| x => (unit y \/ x %= y).

(* -------------------------------------------------------------------- *)
lemma irdc_neq0 (x : t) : irreducible x => x <> zeror.
proof. by move=> [/#]. qed.

hint exact : irdc_neq0.

(* -------------------------------------------------------------------- *)
lemma irdc_Nunit (x : t) : irreducible x => !unit x.
proof. by move=> [/#]. qed.

(* -------------------------------------------------------------------- *)
lemma eqp_unit_mull (u x y : t) : unit u => (x %= u * y) <=> (x %= y).
proof.
move=> unit_u; split=> /eqmodfP[q [unit_q ->]].
- by apply/eqmodP; exists (q * u); rewrite mulrA /= unitrM.
- apply/eqmodP; exists (q * invr u); rewrite unitrM unitrV; split=> //.
  by rewrite -mulrA; congr; rewrite mulrA mulVr.
qed.

(* -------------------------------------------------------------------- *)
lemma irdc_Ml (x y : t) : unit x => irreducible (x * y) <=> irreducible y.
proof.
move=> unit_x @/irreducible; split; last first.
- move=> [# nz_y Nunit_y irry]; do! split.
  - by rewrite mulf_neq0 //; apply: contraL unit_x => ->; apply: unitr0.
  - by rewrite unitrM Nunit_y.
  move=> z dvdz; have: z %| y.
  - case/dvdrP: dvdz=> q /(congr1 (( * ) (invr x))).
    by rewrite !mulrA mulVr //= => ->; apply/dvdrP; exists (invr x * q).
  by case/irry=> [->//|eq_zy]; right; apply/eqp_sym/eqp_unit_mull/eqp_sym.
- move=> [# nz_xMy + irr]; rewrite unitrM unit_x /= => Nunit_y.
  do !split=> //; first by apply: contra nz_xMy => ->.
  move=> z dvd_zy; have := irr z _; first by apply: dvdr_mull.
  by case=> [->//|/eqp_sym /(eqp_unit_mull _ _ _ unit_x) /eqp_sym ?]; right.
qed.

(* -------------------------------------------------------------------- *)
lemma isdecomp_nil (x : t) : isdecomp x [] <=>  x = oner.
proof. by rewrite /isdecomp /BR.BMul.big BR.BMul.big_nil. qed. (* FIXME *)

(* -------------------------------------------------------------------- *)
lemma isdecompM (x : t) (y : t) (ys : t list) :
  isdecomp y ys => isdecomp (x * y) (x :: ys).
proof.
by move=> -> @/isdecomp; rewrite /BR.BMul.big BR.BMul.big_consT. (* FIXME *)
qed.

(* -------------------------------------------------------------------- *)
lemma isdecomp_cons (x : t) (y : t) (ys : t list) :
  isdecomp x (y :: ys) => exists z, x = y * z /\ isdecomp z ys.
proof.
move=> ->; pose z := BR.BMul.big predT idfun ys.
by exists z; rewrite /BR.BMul.big BR.BMul.big_consT. (* FIXME *)
qed.

(* -------------------------------------------------------------------- *)
lemma irdc_coprime (x y : t) :
  irreducible x => irreducible y => !(x %= y) => coprime x y.
proof.
move=> irr_x irr_y ne_xy a dvd_ax dvd_ay.
case: irr_x=> _ /(_ a dvd_ax); case: irr_y=> _ /(_ a dvd_ay).
by case: (unit a) => //=; smt(eqp_trans).
qed.

(* -------------------------------------------------------------------- *)
lemma isdecomp_irdcMl (x y : t) (xs : t list) :
  irreducible x => all irreducible xs => isdecomp (x * y) xs =>
    exists u ys,
         unit u
      /\ perm_eq xs ((u * x) :: ys)
      /\ isdecomp (invr u * y) ys.
proof.
move=> irr_x irr_xs hdecomp; suff: exists x', x' \in xs /\ x %= x'.
- case=> x' [x'_in_xs /eqmodfP [u] [unit_u ->>]].
  exists (invr u) (rem x' xs); rewrite mulrA mulVr //= invrK.
  rewrite unitrV unit_u /= perm_to_rem //=.
  move: hdecomp => @/isdecomp @/BR.BMul.big.
  rewrite (@BR.BMul.eq_big_perm _ _ _ _ (perm_to_rem x'_in_xs)). (* FIXME *)
  rewrite BR.BMul.big_consT /= -mulrA mulrCA &(mulfI).
  by apply: irdc_neq0; apply: irdc_Ml irr_x.
elim: xs x irr_x y irr_xs hdecomp => [|v vs ih] x irr_x y /=.
- by rewrite isdecomp_nil mulrC; apply/negP => /unitP; apply/irdc_Nunit.
case=> irr_v irr_vs hdecomp ; case: (x %= v)=> [eq_xv|ne_xv].
- by exists v.
have cop_xv: coprime x v by apply: irdc_coprime.
move: (hdecomp) => @/isdecomp; rewrite /BR.BMul.big.
rewrite BR.BMul.big_consT /=; pose z := BigDom.BMul.big _ _ _.
move=> eq; have [dvdx dvdv]: x %| v * z /\ v %| x * y.
- split; apply/dvdrP.
  - by exists y; rewrite [_*x]mulrC &(eq_sym).
  - by exists z; rewrite [_*v]mulrC.
have: v %| y by apply/(Gauss _ dvdv)/coprimeC.
case/dvdrP=> k ->>; move: eq; rewrite mulrA [v*z]mulrC.
have nz_v: v <> zeror by apply: irdc_neq0.
move/(mulIf v nz_v) => {hdecomp} hdecomp.
have /# := ih x irr_x k irr_vs hdecomp.
qed.

(* -------------------------------------------------------------------- *)
lemma unit_eqm (x y : t) : x %= y => unit x => unit y.
proof. by case/eqmodfP=> [u] [unit_u ->>] /(unitrMr _ _ unit_u). qed.

(* -------------------------------------------------------------------- *)
lemma unitrP_eqm (x : t) : unit x <=> exists y, y * x %= oner.
proof.
rewrite unitrP; split; case=> y; first by move=> <-; exists y.
case/eqmodfP=> [u] [unit_u /= eq]; exists (y * invr u).
by rewrite mulrAC eq divrr.
qed.

(* -------------------------------------------------------------------- *)
lemma perm_cons_eq ['a] (x y : 'a) (xs ys : 'a list) :
  x = y => perm_eq (x :: xs) (y :: ys) <=> perm_eq xs ys.
proof. by move=> ->; apply/perm_cons. qed.

(* -------------------------------------------------------------------- *)
lemma inj_bij_fin ['a] (f : 'a -> 'a) :
     is_finite (fun x => f x <> x)
  => injective f
  => bijective f.
proof.
case=> s [uq_s memsP] inj_f; have dom: perm_eq s (map f s).
- apply/perm_eq_sym/uniq_perm_eq_size => //.
  - by apply: map_inj_in_uniq => //#.
  - by rewrite size_map.
  by move=> x /mapP[y] [y_in_s ->]; smt().
pose g (y : 'a) :=
  if y \in map f s then nth y s (index y (map f s)) else y.
exists g; split.
- move=> x @/g; rewrite mem_map //; case: (x \in s).
  - by move=> ?; rewrite index_map // nth_index.
  - by rewrite memsP.
- move=> y @/g; case: (y \in map f s).
  - case/mapP=> [x] [x_in_s ->>]; rewrite index_map //.
    by rewrite nth_index //.
  - by rewrite -(perm_eq_mem dom) memsP.
qed.

(* -------------------------------------------------------------------- *)
op isperm (n : int) (f : int -> int) =
     (forall i, 0 <= i < n => 0 <= f i < n)
  /\ (forall i, !(0 <= i < n) => f i = i)
  /\ (forall i j, 0 <= i < n => 0 <= j < n => i <> j => f i <> f j).

(* -------------------------------------------------------------------- *)
lemma inj_isperm (n : int) (f : int -> int) : isperm n f => injective f.
proof. smt(). qed.

(* -------------------------------------------------------------------- *)
lemma bij_isperm (n : int) (f : int -> int) : isperm n f => bijective f.
proof.
move=> pf; apply/inj_bij_fin/(inj_isperm n) => //.
apply/finiteP; exists (iota_ 0 n) => /=.
by move=> x; rewrite mem_iota /#.
qed.

(* -------------------------------------------------------------------- *)
lemma isperm_idfun (n : int) : isperm n idfun.
proof. done. qed.

hint exact : isperm_idfun.

(* -------------------------------------------------------------------- *)
lemma isperm_comp (n : int) (f g : int -> int) :
  isperm n f => isperm n g => isperm n (f \o g).
proof. smt(). qed.

(* -------------------------------------------------------------------- *)
lemma ispermW (m n : int) (f : int -> int) :
  m <= n => isperm m f => isperm n f.
proof. smt(). qed.

(* -------------------------------------------------------------------- *)
op shift1 (f : int -> int) =
  fun i => if i = 0 then 0 else f (i - 1) + 1.

(* -------------------------------------------------------------------- *)
lemma isperm_shift1 (m : int) (f : int -> int) :
  isperm m f => isperm (m + 1) (shift1 f).
proof. smt(). qed.

(* -------------------------------------------------------------------- *)
lemma shift1_0E (f : int -> int) : shift1 f 0 = 0.
proof. done. qed.

hint simplify shift1_0E.

(* -------------------------------------------------------------------- *)
lemma shift1_nzE (f : int -> int) (i : int) :
  i <> 0 => shift1 f i = f (i - 1) + 1.
proof. by move=> @/shift1 ->. qed.

hint simplify shift1_0E.

(* -------------------------------------------------------------------- *)
op rol1 (m : int) =
  fun i => if 0 <= i < m then (i - 1) %% m else i.

(* -------------------------------------------------------------------- *)
lemma isperm_rol1 (m n : int) : m <= n => isperm n (rol1 m).
proof. smt(). qed.

(* -------------------------------------------------------------------- *)
lemma rol1_0E (m : int) : 0 <= m => rol1 (m+1) 0 = m.
proof. smt(). qed.

(* -------------------------------------------------------------------- *)
lemma rol1_psmallE (m i : int) : 0 < i <= m => rol1 (m+1) i = i-1.
proof. smt(). qed.

(* -------------------------------------------------------------------- *)
lemma rol1_bigE (m i : int) : 0 <= m => m < i => rol1 (m+1) i = i.
proof. smt(). qed.

(* -------------------------------------------------------------------- *)
hint simplify drop0.
hint simplify index_cons.

(* -------------------------------------------------------------------- *)
lemma rem_take_drop ['a] (x : 'a) (s : 'a list) : x \in s =>
  rem x s = take (index x s) s ++ drop (index x s + 1) s.
proof.
elim: s => //= y s ih; case: (x = y) => [<<-|ne_xy] //=.
move/ih => ->; rewrite [y=x]eq_sym ne_xy /=.
by rewrite !iffalse; ~-1:smt(index_ge0).
qed.

(* -------------------------------------------------------------------- *)
lemma nth_rem ['a] (x0 : 'a) (x : 'a) (s : 'a list) (i : int) :
  nth x0 (rem x s) i =
    if i < index x s then nth x0 s i else nth x0 s (i+1).
proof.
case: (i < 0) => [lt0i|/lezNgt ge0_i].
- by rewrite iftrue ?nth_neg //; smt(index_ge0).
elim: s i ge0_i => //= y s ih i ge0_i; rewrite [y=x]eq_sym.
case: (x = y) => [<<-|ne_xy]; first by smt().
case: (i = 0) => [->>|nz_i] /=.
- by rewrite iftrue //; smt(index_ge0).
- by rewrite ih //#.
qed.

(* -------------------------------------------------------------------- *)
lemma perm_eq_reindex ['a] (x0 : 'a) (s1 s2 : 'a list) :
  perm_eq s1 s2 => exists (f : int -> int),
       isperm (size s1) f
    /\ (forall i, 0 <= i < size s1 => nth x0 s1 i = nth x0 s2 (f i)).
proof.
elim: s1 s2 => [|x1 s1 ih] s2.
- by move/perm_eq_size => /= /eq_sym /size_eq0 => -> /=; exists idfun.
move=> heq; have x1_in_s2: x1 \in s2 by move/perm_eq_mem: heq; apply.
have /= /eq_sym sz_s2 := perm_eq_size _ _ heq.
move/perm_to_rem/(perm_eq_trans _ _ _ heq)/perm_cons: (x1_in_s2).
case/ih=> f [permf eqnth]; pose j := index x1 s2.
pose g := rol1 (j+1) \o shift1 f; exists g; split.
- apply/isperm_comp.
  - by apply: isperm_rol1; smt(index_mem).
  - by rewrite addrC &(isperm_shift1).
move=> i [ge0i lti] @/g @/(\o) /=; case: (i = 0) => [->>|nz_i] /=.
- by rewrite rol1_0E 1:&(index_ge0) nth_index.
rewrite /shift1 nz_i /=; rewrite eqnth 1://# nth_rem -/j.
case: (f (i - 1) < j) => [lt_fPi_j|].
- by rewrite rol1_psmallE 1:/#.
- by move=> ?; rewrite rol1_bigE ?index_ge0 //#.
qed.

(* -------------------------------------------------------------------- *)
lemma perm_eq_of_perm ['a] (x0 : 'a) (f : int -> int) (s : 'a list) :
  isperm (size s) f => perm_eq s (mkseq (fun i => nth x0 s (f i)) (size s)).
proof.
move=> pf; rewrite -{1}[s](@mkseq_nth x0).
rewrite -(@map_mkseq (fun i => nth x0 s i) f) /=.
apply: perm_eq_map => @/mkseq; move: (size s) pf => {s} n pf.
apply: uniq_perm_eq.
- by apply: iota_uniq.
- apply: map_inj_in_uniq.
  - by move=> ??  _ _; apply: (inj_isperm _ _ pf).
  by apply: iota_uniq.
move=> x; rewrite mem_iota /=; split; last first.
- by case/mapP=> y [/mem_iota /= rgy ->] /#.
- move=> rgx; apply/mapP; have := bij_isperm _ _ pf.
  case=> g [can_fg can_gf]; exists (g x).
  by rewrite mem_iota //#.
qed.

(* -------------------------------------------------------------------- *)
lemma decomp_uniq (z1 z2 : t) (xs1 xs2 : t list) :
     all irreducible xs1
  => all irreducible xs2
  => isdecomp z1 xs1
  => isdecomp z2 xs2
  => z1 %= z2
  => exists cs,
          size cs = size xs2
       /\ all unit cs
       /\ perm_eq xs1 (mkseq (fun i => cs.[i] * xs2.[i]) (size xs2)).
proof.
elim: xs1 z1 z2 xs2 => [|x1 xs1 ih] z1 z2 xs2 /=.
- move=> irdc_xs2 eq1x dcp2 eqz; have ->>: z1 = oner.
  - by rewrite eq1x /(BR.BMul.big) BR.BMul.big_nil.
  suff -> /=: xs2 = [] by exists [] => /=; rewrite mkseq0.
  case: xs2 irdc_xs2 dcp2 => //= x2 xs2; case=> + _.
  move/irdc_Nunit; apply: contra => /isdecomp_cons.
  case=> [z] [/eq_sym eq _]; apply/unitrP_eqm.
  by exists z; rewrite mulrC eq eqp_sym.
case=> irdc_x1 irdc_xs1 irdc_xs2 /isdecomp_cons [x'] [->> dcp_xs1] dcp_xs2.
case/eqmodfP=> [w] [unit_w]; move/(congr1 (( * ) (invr w))).
rewrite !mulrA mulVr //= => <<-.
have := isdecomp_irdcMl (invr w * x1) x' xs2 _ irdc_xs2 dcp_xs2.
- by apply/(irdc_Ml _); first by apply/unitrV.
case=> [u ys] [# unit_u eq_xs2 dcp_ys].
wlog: xs2 irdc_xs2 dcp_xs2 eq_xs2 / (xs2 = (u * (invr w * x1)) :: ys).
- move=> /(_ ((u * (invr w * x1)) :: ys) _ _ _ _) => //.
  - apply/allP=> z /=; case=> [->|].
    - by do! apply/irdc_Ml => //; apply/unitrV.
    move=> ?; move/allP: irdc_xs2; apply.
    by move/perm_eq_mem: eq_xs2 => -> /=; right.
  - rewrite /isdecomp /(BR.BMul.big) BR.BMul.big_consT /=.
    apply/(mulrI (w * invr u) _).
    - by apply/unitrM; split=> //; apply/unitrV.
    rewrite -[_ * BigDom.BMul.big _ _ _]mulrA; congr.
    rewrite [u*_]mulrC -!mulrA; do 2! congr.
    apply/(mulrI (invr u)); first by apply/unitrV.
    by rewrite mulrA dcp_ys mulrAC mulVr.
  - by apply: perm_eq_refl.
  case=> cs [# eq_sz unit_cs];
    move/perm_eq_size: (eq_xs2) eq_sz => /= <- eq_sz heq.
  case/(perm_eq_reindex zeror): eq_xs2 => f.
  move=> [# permf hreindex].
  pose ds := mkseq (fun i => cs.[f i]) (size xs2); exists ds.
  do 2? split.
  - by rewrite size_mkseq lez_maxr ?size_ge0.
  - apply/allP => x /mkseqP[i] [rgi /= ->].
    by move/allP: unit_cs => /(_ cs.[f i]); apply; apply/mem_nth => /#.
  move/perm_eqlE: heq => ->; pose s := mkseq _ _.
  have szsE: size s = size xs2.
  - by rewrite size_mkseq lez_maxr ?size_ge0.
  have := perm_eq_of_perm zeror f s _; first by rewrite szsE.
  move/perm_eqlE; apply; apply/perm_eq_refl_eq.
  rewrite szsE &(eq_in_mkseq) => /= i [ge0i lti].
  by rewrite !nth_mkseq ~-1:/# /= hreindex.
move=> {eq_xs2} ->> /=; move: irdc_xs2 => /= [_ irdc_ys].
have := ih x' (invr u * x') ys irdc_xs1 irdc_ys dcp_xs1 dcp_ys _.
- by apply/eqmodfP; exists u; rewrite mulrA divrr.
case=> cs [# eq_sz unit_cs eqp].
exists ((w * invr u) :: cs); do 2? split => //=.
- by rewrite eq_sz.
- by rewrite unit_cs /=; rewrite unitrM unitrV.
rewrite [1+_]addrC mkseqSr ?size_ge0 /= &(perm_cons_eq).
- by rewrite !mulrA [_ * u]mulrAC mulrK // divrr.
move/perm_eqlE: eqp; apply; apply/perm_eq_refl_eq/eq_in_mkseq.
by move=> @/(\o) /= i [ge0i lti]; rewrite add1z_neq0.
qed.

(* -------------------------------------------------------------------- *)
lemma Gauss_dvdr (a b c : t) : coprime a b => (a %| b * c) <=> (a %| c).
proof. by move=> cop_a_b; split; [move/Gauss; apply | apply: dvdr_mull]. qed.

(* -------------------------------------------------------------------- *)
lemma Gauss_dvdl (a b c : t) : coprime a c => (a %| b * c) <=> (a %| b).
proof. by move=> ?; rewrite mulrC; apply: Gauss_dvdr. qed.

(* -------------------------------------------------------------------- *)
lemma coprime_eqmr (a b b' : t) : coprime a b => b %= b' => coprime a b'.
proof.
move=> cop /eqp_sym eq x dvda dvdb'.
by apply: cop => //; apply: dvdr_eqpR eq.
qed.

(* -------------------------------------------------------------------- *)
lemma coprime_eqml (a a' b : t) : coprime a b => a %= a' => coprime a' b.
proof. by rewrite ![coprime _ b]coprimeC; apply: coprime_eqmr. qed.

(* -------------------------------------------------------------------- *)
lemma dvdr1 (a : t) : a %| oner <=> a %= oner.
proof. by rewrite -eqmodf1P unitrP /#. qed.

(* -------------------------------------------------------------------- *)
lemma coprime1r (a : t) : coprime oner a.
proof. by move=> x /dvdr1 /eqmodf1P. qed.

(* -------------------------------------------------------------------- *)
lemma coprimer1 (a : t) : coprime a oner.
proof. by rewrite coprimeC &(coprime1r). qed.

(* -------------------------------------------------------------------- *)
lemma coprime0r_unit (a : t) : coprime zeror a => unit a.
proof. by move=> /(_ a); apply=> //; apply: dvdr0. qed.

(* -------------------------------------------------------------------- *)
lemma coprimer0_unit (a : t) : coprime a zeror => unit a.
proof. by move/coprimeC/coprime0r_unit. qed.

(* -------------------------------------------------------------------- *)
lemma eqpC (x y : t) : (x %= y) <=> (y %= x).
proof. by split=> /eqp_sym. qed.

(* -------------------------------------------------------------------- *)
lemma dvd1r (a : t) : oner %| a.
proof. by exists a. qed.

(* -------------------------------------------------------------------- *)
lemma coprimeP (a b : t) :
  coprime a b <=> exists (u v : t), u * a + v * b = oner.
proof.
split; first by move=> /coprime_isgcdP /Bezout.
case=> u v eq; apply/coprime_isgcdP => @/isgcd; do! split => /=.
- by case=> ->> ->>; move: eq => /= => ->.
move=> nz_aAb; rewrite !dvd1r /= => d' dvda dvdb.
by rewrite -eq dvdrD dvdr_mull.
qed.

(* -------------------------------------------------------------------- *)
lemma Gauss_gcdr (c a b d : t) :
  coprime c a => isgcd c (a * b) d <=> isgcd c b d.
proof.
case: (c = zeror) => [->|nz_c].
- move/coprime0r_unit => unit_a; rewrite !isgcd0r_eqm.
  by rewrite ![_ %= d]eqpC eqp_unit_mull.
move=> cop_ca; split => @/isgcd; rewrite nz_c /=; last first.
- move=> [# dvd_c dvd_d mind]; do! split => //.
  - by rewrite dvdr_mull.
  - move=> d' dvd'_c dvd'_ab; apply: mind=> //.
    suff: coprime d' a by move/Gauss_dvdr; apply.
    case/coprimeP: cop_ca=> u v eq; apply/coprimeP.
    by case/dvdrP: dvd'_c => q ->>; exists (u*q) v; ring eq.
- move=> [# dvd_c dvd_ab mind]; do! split => //.
  - suff: coprime d a by move/Gauss_dvdr; apply.
    case/coprimeP: cop_ca=> u v eq; apply/coprimeP.
    by case/dvdrP: dvd_c => q ->>; exists (u*q) v; ring eq.
  - by move=> d' dvd'_c dvd'_b; apply: mind => //; apply: dvdr_mull.
qed.

(* -------------------------------------------------------------------- *)
lemma Gauss_gcdl (c a b d : t) :
  coprime c b => isgcd c (a * b) d <=> isgcd c a d.
proof. by move=> ?; rewrite mulrC &(Gauss_gcdr). qed.

(* -------------------------------------------------------------------- *)
lemma coprimeMr (c a b : t) :
  coprime c (a * b) <=> (coprime c a /\ coprime c b).
proof.
case: (coprime c a) => /= cop_c_a.
- by rewrite -!coprime_isgcdP Gauss_gcdr.
apply: contra cop_c_a => /coprimeP [u v] eq; apply/coprimeP.
by exists u (v * b); ring eq.
qed.

(* -------------------------------------------------------------------- *)
lemma coprimeMl (c a b : t) :
  coprime (a * b) c <=> (coprime a c /\ coprime b c).
proof. by rewrite coprimeC coprimeMr ![coprime c _]coprimeC. qed.

(* -------------------------------------------------------------------- *)
lemma coprime_prod ['a] (P : 'a -> bool) (F : 'a -> t) (c : t) (cs : 'a list) :
     (forall i, i \in cs => P i => coprime (F i) c)
  => coprime (BR.BMul.big P F cs) c.
proof.
move=> @/BR.BMul.big; elim: cs => /= [|x xs ih]. (* FIXME *)
- by rewrite BR.BMul.big_nil coprime1r.
move=> cop; rewrite BR.BMul.big_cons; case: (P x); last smt().
by move=> Px; apply/coprimeMl => /#.
qed.

(* -------------------------------------------------------------------- *)
lemma dvdr_sum ['a] (P : 'a -> bool) (F : 'a -> t) (cs : 'a list) (a : t) :
     (forall c, c \in cs => P c => a %| F c)
  => a %| BR.BAdd.big P F cs.
proof.
elim: cs => [|c cs ih] hdvd @/BR.BAdd.big //=. (* FIXME *)
- by rewrite BR.BAdd.big_nil dvdr0.
rewrite BR.BAdd.big_cons; case: (P c) => Pc /=; last first.
- by apply/ih=> *; apply/hdvd => //#.
- rewrite dvdrD; first by apply: hdvd.
  by apply/ih=> *; apply/hdvd => /#.
qed.

(* -------------------------------------------------------------------- *)
lemma dvdr_prod ['a] (P : 'a -> bool) (F : 'a -> t) (cs : 'a list) (a : t) (x : 'a) :
  x \in cs => P x => a %| F x => a %| BR.BMul.big P F cs.
proof.
move=> x_in_cs Px dvd_a_Fx @/BR.BMul.big.
move/perm_to_rem: x_in_cs => /BR.BMul.eq_big_perm ->.
by rewrite BR.BMul.big_cons Px /= dvdr_mulr.
qed.

(* -------------------------------------------------------------------- *)
lemma dvdrN (a b : t) : a %| b => a %| -b.
proof. by case=> c ->; exists (-c); rewrite mulNr. qed.

(* -------------------------------------------------------------------- *)
lemma dvdrB (d a b : t) : d %| a => d %| b => d %| (a - b).
proof. by move=> ??; apply/dvdrD/dvdrN. qed.

(* -------------------------------------------------------------------- *)
lemma crt (rs : (t * t) list) :
  (forall i j,
     0 <= i < size rs => 0 <= j < size rs => i <> j =>
       coprime (nth witness rs i).`2 (nth witness rs j).`2)
  => exists (x : t), all (fun (an : _ * _) => idgen [an.`2] (x - an.`1)) rs.
proof.
move=> hcop; pose k := size rs.
pose a i := (nth witness rs i).`1.
pose n i := (nth witness rs i).`2.
pose N i := BR.BMul.bigi ((<>) i) n 0 k.
have copN: forall i, 0 <= i < k => coprime (N i) (n i).
- move=> i rgi; apply: coprime_prod => j /mem_range /= [ge0_j ltj] ne_ij.
  by (have := hcop i j _ _ ne_ij; ~-1: done); rewrite coprimeC.
pose P i (Mm : _ * _) := Mm.`1 * N i + Mm.`2 * n i = oner.
pose B i := choiceb (P i) witness.
pose M i := (B i).`1; pose m i := (B i).`2.
have hsol: forall i, 0 <= i < k => M i * N i + m i * n i = oner.
- move=> i rgi @/M @/n @/B; have := choicebP (P i) witness _; last done.
  have := Bezout (N i) (n i) oner _; first by apply/coprime_isgcdP/copN.
  by case=> Mi mi ?; exists (Mi, mi).
pose x := BR.BAdd.bigi predT (fun i => a i * M i * N i) 0 k.
exists x; apply/(@all_nthP _ _ witness) => i rgi /=.
rewrite -/(n i) -/(a i) /x /BR.BAdd.big (@BR.BAdd.bigD1 _ _ i) /=.
- by rewrite mem_range. - by apply: range_uniq.
rewrite addrAC &(@idealD (idgen [n i])); 1: solve; last first. (* FIXME *)
- apply/mem_idgen1_dvd/dvdr_sum=> j /mem_range rgj @/predC1 ne_ji /=.
  by rewrite &(dvdr_mull) &(dvdr_prod i) ?mem_range.
have := hsol i rgi; move/(congr1 (( * ) (a i))) => /=.
rewrite mulrDr !mulrA eq_sym -subr_eq => <-.
by rewrite addrAC subrr /= mem_idgen1_dvd dvdrN dvdr_mull.
qed.

(* -------------------------------------------------------------------- *)
lemma dvdrMl_coprime (a1 a2 b : t) :
  coprime a1 a2 => a1 %| b => a2 %| b => a1 * a2 %| b.
proof.
move=> cop dvd1 dvd2; case/dvdrP: dvd1=> q ->>.
rewrite [_*a1]mulrC dvdr_mul //.
by move/coprimeC/Gauss_dvdl: cop => <-.
qed.

(* -------------------------------------------------------------------- *)
lemma dvdr_prodl_coprime ['a] (F : 'a -> t) (cs : 'a list) (a : t) :
     (forall i j, 0 <= i < size cs => 0 <= j < size cs => i <> j =>
        coprime (F (nth witness cs i)) (F (nth witness cs j)))
  => all (fun b => b %| a) (map F cs)
  => BR.BMul.big predT F cs %| a.
proof.
elim: cs => [|c cs ih] hcop hdvd /= @/BR.BMul.big.
- by rewrite BR.BMul.big_nil dvd1r.
rewrite BR.BMul.big_consT dvdrMl_coprime.
- apply/coprimeC/coprime_prod => b b_in_cs _.
  have := hcop (1 + index b cs) 0 _ _ _ => /=;
    ~-1: smt(index_ge0 size_ge0 index_mem).
  by rewrite add1z_neq0 ?index_ge0 /= nth_index.
- by move: hdvd => /= [+ _]; apply.
- apply: ih; last by move: hdvd=> /= [_]; apply.
  move=> i j rgi rgj ne_ij.
have /= := hcop (i + 1) (j + 1) _ _ _; ~-1: smt().
by rewrite ![_+1]addrC !add1z_neq0 //#.
qed.

(* -------------------------------------------------------------------- *)
lemma crt_uniq (rs : (t * t) list) (x1 x2 : t) :
     (forall i j,
        0 <= i < size rs => 0 <= j < size rs => i <> j =>
          coprime (nth witness rs i).`2 (nth witness rs j).`2)
  => all (fun (an : _ * _) => idgen [an.`2] (x1 - an.`1)) rs
  => all (fun (an : _ * _) => idgen [an.`2] (x2 - an.`1)) rs
  => idgen [BR.BMul.big predT (fun an : _ * _ => an.`2) rs] (x2 - x1).
proof.
move=> hcop sol1 sol2; rewrite mem_idgen1_dvd &(dvdr_prodl_coprime) //.
rewrite all_map /preim; apply/allP=> y y_rs /=.
have ->: x2 - x1 = x2 - y.`1 - (x1 - y.`1) by ring.
by apply/dvdrB; [
       move/allP/(_ _ y_rs): sol2 => /=
     | move/allP/(_ _ y_rs): sol1 => /=
   ]; move/mem_idgen1_dvd.
qed.

(* -------------------------------------------------------------------- *)
lemma neotherian (sI : int -> (t -> bool)) :
     (forall i j, 0 <= i <= j => sI i <= sI j)
  => (forall i, 0 <= i => ideal (sI i)) 
  => exists (k : int), 0 <= k /\ (forall i, k <= i => sI k = sI i).
proof.
move=> mono idI; pose I (x : t) := exists k, 0 <= k /\ sI k x.
have: ideal I by (do! split); smt().
move/principal/principalP=> [a] ^IE /fun_ext /(_ a).
rewrite mem_idgen1_gen eqT; case=> k [ge0k sIa].
exists k; split=> // i le_ki; apply/predeq_leP.
split; first by apply/mono => //#.
move=> x sIx; have: I x by exists i => //#.
rewrite IE => /mem_idgen1[b ->].
by apply: (@idealMl (sI k)) => //; apply: idI.
qed.

(* -------------------------------------------------------------------- *)
lemma dvdrW (P : t -> bool) :
  (forall (a : t), (forall (b : t), b %| a => !(a %= b) => P b) => P a)
    => forall a, P a.
proof.
suff hwf:
  forall (X : t -> bool), (exists x, X x) =>
    exists x, X x /\ (forall y, X y => y %| x => x %= y).
- move=> ih a; apply: contraT => NPa; pose X a := !P a.
  by have := hwf X _; [by exists a | smt()].
move=> X [a Xa]; apply: contraT; rewrite negb_exists /=; apply/negP=> Nwf.
pose Q b c := X c /\ c %| b /\ !(b %= c).
have {Nwf} Nwf: forall b, X b => exists c, Q b c by smt().
pose f x := choiceb (fun y => Q x y) witness.
pose s (i : int) := iter i f a.
have siS: forall i, 0 <= i => s (i + 1) = f (s i) by smt(iterS).
have: forall i, 0 <= i => X (s i).
- elim=> [|i ge0i ih] @/s /=; [by rewrite iter0 | rewrite iterS //].
  by have @/Q := choicebP (Q (iter i f a)) witness (Nwf _ ih).
move=> sX; (have: forall i, 0 <= i => Q (s i) (s (i + 1))) => [i ge0i|].
- have := choicebP (Q (s i)) witness (Nwf _ (sX _ ge0i)).
  by rewrite siS //; apply.
move=> {Nwf siS sX}; move: s => {f} s Qs.
(have := neotherian (fun i => idgen [s i]) _ _) => /=.
- move=> i j [ge0i ltij]; apply: le_idgen1_dvd.
  rewrite (_ : j = i + (j - i)) 1:#ring.
  have: 0 <= j - i by smt().
  elim: (j - i) => {j ltij} //= j ge0j ih.
  by rewrite addrA (dvdr_trans _ _ ih) /#.
- by move=> i _; apply: ideal_idgen.
apply/negP; case=> [k] [ge0k] /(_ (k+1) _); first smt().
by move/eqmodf_idP; have := Qs k; smt().
qed.

(* -------------------------------------------------------------------- *)
lemma irreducibleNP (x : t) : x <> zeror => !unit x => !irreducible x =>
  exists y z,
       (   (y <> zeror /\ !unit y)
        /\ (z <> zeror /\ !unit z))
    /\ (x = y * z).
proof.
move=> @/irreducible ^nz_x -> -> /=; rewrite negb_forall /=.
case=> a; case/negb_imply => dvd_ax /negb_or[Nunit_a ne_xa].
case/dvdrP: dvd_ax => b ->>; exists b a => //=.
rewrite Nunit_a /=; move: nz_x; rewrite mulf_eq0.
case/negb_or=> -> -> /=; apply: contraLR ne_xa => /=.
by move/eqp_unit_mull => h; apply/eqpC/h.
qed.

(* -------------------------------------------------------------------- *)
lemma isdecomp_cat (x y : t) (xs ys : t list) :
  isdecomp x xs => isdecomp y ys => isdecomp (x * y) (xs ++ ys).
proof.
move=> xsE ysE @/isdecomp @/BR.BMul.big. (* FIXME *)
by rewrite BR.BMul.big_cat xsE ysE.
qed.

(* -------------------------------------------------------------------- *)
lemma decomp (x : t) : x <> zeror => !unit x =>
  exists xs, all irreducible xs /\ isdecomp x xs.
proof.
elim/dvdrW: x => x ih; case: (irreducible x).
- by move=> irr_x _ _; exists [x].
move=> + nz_x Nunit_x - /(irreducibleNP x nz_x Nunit_x).
case=> y z [#] nz_y ? nz_z ? ->>.
have := ih y _ _ _ _ => //; first by rewrite dvdr_mulr.
- rewrite mulrC; apply/negP => /eqmodfP[u].
  by case=> [unit_u /(@mulIf _ nz_y) ->>].
have := ih z _ _ _ _ => //; first by rewrite dvdr_mull.
- by apply/negP => /eqmodfP[u] [unit_u /(@mulIf _ nz_z) ->>].
case=> [ys] [irr_ys ysE] [zs] [irr_zs zsE].
exists (zs ++ ys); rewrite all_cat !(irr_ys, irr_zs) /=.
by apply: isdecomp_cat.
qed.
