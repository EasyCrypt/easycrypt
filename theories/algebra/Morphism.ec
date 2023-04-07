(* -------------------------------------------------------------------- *)
require import AllCore List Ring Int IntDiv Bigalg RingStruct.
require (*--*) Subtype.
(*---*) import StdOrder.IntOrder.

(*
(* ==================================================================== *)
theory ZModuleIso.
  type t1, t2.

  clone import ZModule as ZMod1 with
    type t <= t1.

  clone import ZModule as ZMod2 with
    type t <= t2.

  op f : t1 -> t2.

  axiom bij_f : bijective f.

  axiom fD (x y : t1) : f (x + y) = f x + f y.

  axiom fN (x : t1) : f (-x) = - f x.

  lemma inj_f : injective f.
  proof. by apply/bij_inj/bij_f. qed.

  lemma surj_f : surjective f.
  proof. by apply/bij_surj/bij_f. qed.

  lemma fB (x y : t1) : f (x - y) = f x - f y.
  proof. by rewrite fD fN. qed.

  lemma f0 : f ZMod1.zeror = ZMod2.zeror.
  proof. by rewrite -(ZMod1.subrr ZMod1.zeror) fB ZMod2.subrr. qed.

  lemma fMz (x : t1) n : f (intmul x n) = intmul (f x) n.
  proof.
    wlog: n / 0 <= n => [wlog_|].
    + case (0 <= n) => [|/ltrNge/ltzW/ler_opp2] /wlog_ //.
      by rewrite ZMod1.mulrNz ZMod2.mulrNz fN; apply/ZMod2.oppr_inj.
    elim: n => [|n le0n IHn]; [by rewrite ZMod1.mulr0z ZMod2.mulr0z f0|].
   by rewrite ZMod1.mulrSz ZMod2.mulrSz fD IHn.
  qed.

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

  lemma g0 : g ZMod2.zeror = ZMod1.zeror.
  proof. by apply/inj_f; rewrite f0 cangf. qed.

  lemma gD (x y : t2) : g (x + y) = g x + g y.
  proof. by apply/inj_f; rewrite fD !cangf. qed.

  lemma gN (x : t2) : g (-x) = - g x.
  proof. by apply/inj_f; rewrite fN !cangf. qed.

  lemma gB (x y : t2) : g (x - y) = g x - g y.
  proof. by apply/inj_f; rewrite fB !cangf. qed.

  lemma gMz (x : t2) n : g (intmul x n) = intmul (g x) n.
  proof. by apply/inj_f; rewrite fMz !cangf. qed.

end ZModuleIso.

(* -------------------------------------------------------------------- *)
theory ComRingIso.
  type t1, t2.

  clone import ComRing as CR1 with
    type t <= t1.

  clone import ComRing as CR2 with
    type t <= t2.

  clone include ZModuleIso with
    type t1      <- t1,
    type t2      <- t2,
    theory ZMod1 <= CR1,
    theory ZMod2 <= CR2.

  axiom f1 : f CR1.oner = CR2.oner.

  axiom fM (x y : t1) : f (x * y) = f x * f y.

  axiom fV (x : t1) : f (invr x) = invr (f x).

  lemma fU (x : t1) : unit x <=> unit (f x).
  proof.
    rewrite CR1.unitrP CR2.unitrP; split=> [[y]|[y]].
    + by rewrite -f1 => <-; exists (f y); rewrite fM.
    move/(congr1 g); rewrite gM.
  qed.

  lemma fX (x : t1) n : f (exp x n) = exp (f x) n.
  proof.
    wlog: n / 0 <= n => [wlog_|].
    + case (0 <= n) => [|/ltrNge/ltzW/ler_opp2] /wlog_ //.
      by rewrite CR1.exprN CR2.exprN fV; apply/CR2.invr_inj.
    elim: n => [|n le0n IHn]; [by rewrite CR1.expr0 CR2.expr0 f1|].
   by rewrite CR1.exprS // CR2.exprS // fM IHn.
  qed.

  lemma g1 : g CR2.oner = CR1.oner.
  proof. by apply/inj_f; rewrite f1 cangf. qed.

  lemma gM (x y : t2) : g (x * y) = g x * g y.
  proof. by apply/inj_f; rewrite fM !cangf. qed.

  lemma gV (x : t2) : g (invr x) = invr (g x).
  proof. by apply/inj_f; rewrite fV !cangf. qed.

  lemma gX (x : t2) n : g (exp x n) = exp (g x) n.
  proof. by apply/inj_f; rewrite fX !cangf. qed.
end ComRingIso.

(* -------------------------------------------------------------------- *)
theory IDomainPred.
  type t.

  clone import IDomain as ID with
    type t <= t.

  clone include ComRingPred with
    type t    <- t,
    theory ZMod <= ID,
    theory CR <= ID.

  inductive idomainpred (p : t -> bool) =
  | IDomainPred of
        (comringpred p).

  lemma idomainpred_comring p : idomainpred p => comringpred p.
  proof. by case. qed.

  hint exact : idomainpred_comring.

  lemma idomain0 p : idomainpred p => p zeror.
  proof. by move/idomainpred_comring; exact: comring0. qed.

  lemma idomainD p x y : idomainpred p => p x => p y => p (x + y).
  proof. by move/idomainpred_comring; exact: comringD. qed.

  lemma idomainN p x : idomainpred p => p x => p (-x).
  proof. by move/idomainpred_comring; exact: comringN. qed.
  
  lemma idomainB p x y : idomainpred p => p x => p y => p (x - y).
  proof. by move/idomainpred_comring; exact: comringB. qed.

  lemma idomainMz p x n : idomainpred p => p x => p (intmul x n).
  proof. by move/idomainpred_comring; exact: comringMz. qed.

  lemma idomain1 p : idomainpred p => p oner.
  proof. by move/idomainpred_comring; exact: comring1. qed.
  
 lemma idomainM p x y : idomainpred p => p x => p y => p (x * y).
  proof. by move/idomainpred_comring; exact: comringM. qed.

  lemma idomainV p x : idomainpred p => p x => p (invr x).
  proof. by move/idomainpred_comring; exact: comringV. qed.

  lemma idomainX p x n : idomainpred p => p x => p (exp x n).
  proof. by move/idomainpred_comring; exact: comringX. qed.
end IDomainPred.

(* -------------------------------------------------------------------- *)
theory FieldPred.
  type t.

  clone import Field as F with
    type t <= t.

  clone include IDomainPred with
    type t    <- t,
    theory ZMod <= F,
    theory CR <= F,
    theory ID <= F.

  inductive fieldpred (p : t -> bool) =
  | FieldPred of
        (idomainpred p).

  lemma fieldpred_idomain p : fieldpred p => idomainpred p.
  proof. by case. qed.

  hint exact : fieldpred_idomain.

  lemma field0 p : fieldpred p => p zeror.
  proof. by move/fieldpred_idomain; exact: idomain0. qed.

  lemma fieldD p x y : fieldpred p => p x => p y => p (x + y).
  proof. by move/fieldpred_idomain; exact: idomainD. qed.

  lemma fieldidomainN p x : fieldpred p => p x => p (-x).
  proof. by move/fieldpred_idomain; exact: idomainN. qed.
  
  lemma fieldB p x y : fieldpred p => p x => p y => p (x - y).
  proof. by move/fieldpred_idomain; exact: idomainB. qed.

  lemma fieldMz p x n : fieldpred p => p x => p (intmul x n).
  proof. by move/fieldpred_idomain; exact: idomainMz. qed.

  lemma field1 p : fieldpred p => p oner.
  proof. by move/fieldpred_idomain; exact: idomain1. qed.
  
 lemma fieldM p x y : fieldpred p => p x => p y => p (x * y).
  proof. by move/fieldpred_idomain; exact: idomainM. qed.

  lemma fieldV p x : fieldpred p => p x => p (invr x).
  proof. by move/fieldpred_idomain; exact: idomainV. qed.

  lemma fieldX p x n : fieldpred p => p x => p (exp x n).
  proof. by move/fieldpred_idomain; exact: idomainX. qed.
end FieldPred.

*)
