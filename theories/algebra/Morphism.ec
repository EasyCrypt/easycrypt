(* -------------------------------------------------------------------- *)
require import AllCore List Ring Int IntDiv Bigalg RingStruct FinType.
(*---*) import StdOrder.IntOrder.

(* ==================================================================== *)
theory Iso.
  type t1, t2.

  op f : t1 -> t2.

  axiom bij_f : bijective f.

  lemma inj_f : injective f.
  proof. by apply/bij_inj/bij_f. qed.

  lemma surj_f : surjective f.
  proof. by apply/bij_surj/bij_f. qed.

  op g = choiceb (fun (g : t2 -> t1) => f \o g = idfun /\ g \o f = idfun) (fun _ => witness).

  lemma canfg : cancel f g.
  proof.
    rewrite /g; pose P:= (fun g => _ _ g = _ /\ _ g _ = _).
    move: (choicebP P (fun _ => witness) _); rewrite /P => {P}.
    + case: bij_f => g [] canfg cangf; exists g; rewrite !fun_ext.
      by rewrite /(\o) /idfun; split=> x; [apply/cangf|apply/canfg].
    by rewrite -/g !fun_ext /(\o) /idfun; case=> _ + x /=; move=> ->.
  qed.

  lemma cangf : cancel g f.
  proof.
    rewrite /g; pose P:= (fun g => _ _ g = _ /\ _ g _ = _).
    move: (choicebP P (fun _ => witness) _); rewrite /P => {P}.
    + case: bij_f => g [] canfg cangf; exists g; rewrite !fun_ext.
      by rewrite /(\o) /idfun; split=> x; [apply/cangf|apply/canfg].
    by rewrite -/g !fun_ext /(\o) /idfun; case=> + _ x /=; move=> ->.
  qed.

  lemma bij_g : bijective g.
  proof. by move: canfg; apply/bij_can_bij/bij_f. qed.

  lemma inj_g : injective g.
  proof. by apply/bij_inj/bij_g. qed.

  lemma surj_g : surjective g.
  proof. by apply/bij_surj/bij_g. qed.
end Iso.

(* ==================================================================== *)
theory ZModuleIso_.
  type t1, t2.

  clone include Iso with
    type t1 <- t1,
    type t2 <- t2.

  clone import ZModuleStruct as ZMod1Str with
    type t <= t1.

  clone import ZModuleStruct as ZMod2Str with
    type t <= t2.

  import ZMod1Str ZMod2Str ZMod1Str.R ZMod2Str.R.

  axiom f0 : f ZMod1Str.R.zeror = ZMod2Str.R.zeror.

  axiom fD (x y : t1) : f (x + y) = f x + f y.

  lemma fN (x : t1) : f (-x) = - f x.
  proof.
    rewrite eq_sym -ZMod2Str.R.subr_eq0 -ZMod2Str.R.opprD -fD.
    by rewrite ZMod1Str.R.subrr f0 ZMod2Str.R.oppr0.
  qed.

  lemma fB (x y : t1) : f (x - y) = f x - f y.
  proof. by rewrite fD fN. qed.

  lemma fMz (x : t1) n : f (intmul x n) = intmul (f x) n.
  proof.
    wlog: n / 0 <= n => [wlog_|].
    + case (0 <= n) => [|/ltrNge/ltzW/ler_opp2] /wlog_ //.
      by rewrite ZMod1Str.R.mulrNz ZMod2Str.R.mulrNz fN; apply/ZMod2Str.R.oppr_inj.
    elim: n => [|n le0n IHn]; [by rewrite ZMod1Str.R.mulr0z ZMod2Str.R.mulr0z f0|].
   by rewrite ZMod1Str.R.mulrSz ZMod2Str.R.mulrSz fD IHn.
  qed.

  lemma g0 : g ZMod2Str.R.zeror = ZMod1Str.R.zeror.
  proof. by apply/inj_f; rewrite f0 cangf. qed.

  lemma gD (x y : t2) : g (x + y) = g x + g y.
  proof. by apply/inj_f; rewrite fD !cangf. qed.

  lemma gN (x : t2) : g (-x) = - g x.
  proof. by apply/inj_f; rewrite fN !cangf. qed.

  lemma gB (x y : t2) : g (x - y) = g x - g y.
  proof. by apply/inj_f; rewrite fB !cangf. qed.

  lemma gMz (x : t2) n : g (intmul x n) = intmul (g x) n.
  proof. by apply/inj_f; rewrite fMz !cangf. qed.

end ZModuleIso_.

(* -------------------------------------------------------------------- *)
theory ComRingIso_.
  type t1, t2.

  clone import ComRingStruct as CRng1Str with
    type t <= t1.

  clone import ComRingStruct as CRng2Str with
    type t <= t2.

  clone include ZModuleIso_ with
    type t1      <- t1,
    type t2      <- t2,
    theory ZMod1Str <- CRng1Str,
    theory ZMod2Str <- CRng2Str.

  import CRng1Str CRng2Str CRng1Str.R CRng2Str.R.

  axiom f1 : f CRng1Str.R.oner = CRng2Str.R.oner.

  axiom fM (x y : t1) : f (x * y) = f x * f y.

  lemma g1 : g CRng2Str.R.oner = CRng1Str.R.oner.
  proof. by apply/inj_f; rewrite f1 cangf. qed.

  lemma gM (x y : t2) : g (x * y) = g x * g y.
  proof. by apply/inj_f; rewrite fM !cangf. qed.

  lemma fU (x : t1) : unit (f x) = unit x.
  proof.
    apply/eq_iff; rewrite CRng1Str.R.unitrP CRng2Str.R.unitrP; split=> [[y]|[y]].
    + by move/(congr1 g); rewrite gM g1 canfg => <-; exists (g y).
    by rewrite -f1 => <-; exists (f y); rewrite fM.
  qed.

  lemma fV (x : t1) : f (invr x) = invr (f x).
  proof.
    case: (unit x) => [ux|Nux].
    + apply/(CRng2Str.R.mulIr (f x)); [by rewrite fU|].
      by rewrite -fM CRng1Str.R.mulVr // CRng2Str.R.mulVr ?f1 ?fU.
    by rewrite CRng1Str.R.unitout // CRng2Str.R.unitout // fU.
  qed.

  lemma fX (x : t1) n : f (exp x n) = exp (f x) n.
  proof.
    wlog: n / 0 <= n => [wlog_|].
    + case (0 <= n) => [|/ltrNge/ltzW/ler_opp2] /wlog_ //.
      by rewrite CRng1Str.R.exprN CRng2Str.R.exprN fV; apply/CRng2Str.R.invr_inj.
    elim: n => [|n le0n IHn]; [by rewrite CRng1Str.R.expr0 CRng2Str.R.expr0 f1|].
   by rewrite CRng1Str.R.exprS // CRng2Str.R.exprS // fM IHn.
  qed.

  lemma gU (x : t2) : unit (g x) = unit x.
  proof. by rewrite -fU cangf. qed.

  lemma gV (x : t2) : g (invr x) = invr (g x).
  proof. by apply/inj_f; rewrite fV !cangf. qed.

  lemma gX (x : t2) n : g (exp x n) = exp (g x) n.
  proof. by apply/inj_f; rewrite fX !cangf. qed.
end ComRingIso_.

(* -------------------------------------------------------------------- *)
theory IDomainIso_.
  type t1, t2.

  clone import IDomainStruct as IDom1Str with
    type t <= t1.

  clone import IDomainStruct as IDom2Str with
    type t <= t2.

  clone include ComRingIso_ with
    type t1       <- t1,
    type t2       <- t2,
    theory CRng1Str <- IDom1Str,
    theory CRng2Str <- IDom2Str.
end IDomainIso_.

(* -------------------------------------------------------------------- *)
theory FieldIso_.
  type t1, t2.

  clone import FieldStruct as Fld1Str with
    type t <= t1.

  clone import FieldStruct as Fld2Str with
    type t <= t2.

  clone include IDomainIso_ with
    type t1       <- t1,
    type t2       <- t2,
    theory IDom1Str <- Fld1Str,
    theory IDom2Str <- Fld2Str.
end FieldIso_.


(* ==================================================================== *)
theory ZModuleIso.
  clone include ZModuleIso_
    rename [theory] "ZMod1Str" as "R1Str"
           [theory] "ZMod2Str" as "R2Str".
end ZModuleIso.

(* -------------------------------------------------------------------- *)
theory ComRingIso.
  clone include ComRingIso_
    rename [theory] "CRng1Str" as "R1Str"
           [theory] "CRng2Str" as "R2Str".
end ComRingIso.

(* -------------------------------------------------------------------- *)
theory IDomainIso.
  clone include IDomainIso_
    rename [theory] "IDom1Str" as "R1Str"
           [theory] "IDom2Str" as "R2Str".
end IDomainIso.

(* -------------------------------------------------------------------- *)
theory FieldIso.
  clone include FieldIso_
    rename [theory] "Fld1Str" as "R1Str"
           [theory] "Fld2Str" as "R2Str".
end FieldIso.


(* ==================================================================== *)
theory FinIso.
  type t1, t2.

  clone import Iso with
    type t1 <= t1,
    type t2 <= t2.

  clone import FinType as Fin1 with
    type t <= t1.

  clone import FinType as Fin2 with
    type t <= t2.

  lemma f_enum : perm_eq (map f Fin1.enum) Fin2.enum.
  proof.
    apply/uniq_perm_eq => [| |x]; [|by apply/Fin2.enum_uniq|].
    + by apply/uniq_map_injective; [apply/inj_f|apply/Fin1.enum_uniq].
    by rewrite mapP Fin2.enumP /=; exists (g x); rewrite Fin1.enumP cangf.
  qed.

  lemma g_enum : perm_eq (map g Fin2.enum) Fin1.enum.
  proof.
    move/(perm_eq_map g)/perm_eq_sym: f_enum => eq_.
    apply/(perm_eq_trans _ _ _ eq_); rewrite -map_comp.
    rewrite (eq_map _ idfun) ?map_id ?perm_eq_refl //.
    by move=> ?; rewrite /(\o) /idfun canfg.
  qed.
end FinIso.


(* ==================================================================== *)
theory FinZModuleIso_.
  type t1, t2.

  clone import ZModuleIso as ZModIso with
    type t1 <= t1,
    type t2 <= t2.

  clone include FinIso with
    type t1 <- t1,
    type t2 <- t2.
end FinZModuleIso_.

(* -------------------------------------------------------------------- *)
theory FinComRingIso_.
  type t1, t2.

  clone import ComRingIso as CRngIso with
    type t1 <= t1,
    type t2 <= t2.

  clone include FinZModuleIso_ with
    type t1 <- t1,
    type t2 <- t2,
    theory ZModIso <- CRngIso.
end FinComRingIso_.

(* -------------------------------------------------------------------- *)
theory FinIDomainIso_.
  type t1, t2.

  clone import IDomainIso as IDomIso with
    type t1 <= t1,
    type t2 <= t2.

  clone include FinComRingIso_ with
    type t1 <- t1,
    type t2 <- t2,
    theory CRngIso <- IDomIso.
end FinIDomainIso_.

(* -------------------------------------------------------------------- *)
theory FinFieldIso_.
  type t1, t2.

  clone import FieldIso as FldIso with
    type t1 <= t1,
    type t2 <= t2.

  clone include FinIDomainIso_ with
    type t1 <- t1,
    type t2 <- t2,
    theory IDomIso <- FldIso.
end FinFieldIso_.


(* ==================================================================== *)
theory FinZModuleIso.
  clone include FinZModuleIso_
    rename [theory] "ZModIso" as "RIso".
end FinZModuleIso.

(* -------------------------------------------------------------------- *)
theory FinComRingIso.
  clone include FinComRingIso_
    rename [theory] "CRngIso" as "RIso".
end FinComRingIso.

(* -------------------------------------------------------------------- *)
theory FinIDomainIso.
  clone include FinIDomainIso_
    rename [theory] "IDomIso" as "RIso".
end FinIDomainIso.

(* -------------------------------------------------------------------- *)
theory FinFieldIso.
  clone include FinFieldIso_
    rename [theory] "FldIso" as "RIso".
end FinFieldIso.
