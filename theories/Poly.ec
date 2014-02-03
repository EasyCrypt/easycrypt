(* -------------------------------------------------------------------- *)
require import Fun.
require import Pred.
require import Int.
require import NewList.

(* -------------------------------------------------------------------- *)
type R.
type poly.

clone import Ring.R with type ring <- R.

op ofseq : R list -> poly.
op toseq : poly   -> R list.

op norm_r (s : R list) =
  with s = "[]"      => []
  with s = (::) x s' =>
    if x = zeror then norm_r s' else s.

op norm (s : R list) = rev (norm_r (rev s)).

axiom ofseqK p: ofseq (toseq p) = p.
axiom toseqK s: toseq (ofseq s) = norm s.

axiom toseq_last p: last_ oner (toseq p) <> zeror.

axiom poly_eq p q:
  (forall x, nth zeror (toseq p) x = nth zeror (toseq q) x) => p = q.

lemma norm_nil: norm [] = [].
proof. by rewrite /norm rev_nil. qed.

lemma norm1 x: norm [x] = if x = zeror then [] else [x].
proof. by rewrite /norm rev1 /=; case (x = zeror). qed.

lemma nth_norm n s: nth zeror (norm s) n = nth zeror s n.
proof.
  case (n < 0) => [h|]; first by rewrite !nth_neg.
  rewrite -lezNgt; elim/last_ind s n => [|s x IHs] n ge0_n.
    by rewrite norm_nil.
  rewrite /norm rev_rcons /=; case (x = zeror) => [-> |].
    rewrite -/(norm _) IHs // nth_rcons; case (n < size s)=> //.
    by rewrite -lezNgt => h; rewrite nth_default.
  by move=> _; rewrite rev_cons revK.
qed.

(* -------------------------------------------------------------------- *)
op deg       (p : poly)   = size (toseq p) axiomatized by degE.
op coeff     (p : poly) n = nth zeror (toseq p) n axiomatized by coeffE.
op lead_coef (p : poly)   = coeff p (deg p - 1) axiomatized by lead_coefE.

(* -------------------------------------------------------------------- *)
op coefp n = fun p, coeff p n.

(* -------------------------------------------------------------------- *)
lemma poly_eqP p q: (forall x, coeff p x = coeff q x) <=> p = q.
proof. by rewrite coeffE /=; split => [| ->] // h; apply poly_eq. qed.

(* -------------------------------------------------------------------- *)
op polyC (c : R) = ofseq [c].

lemma polyseqC (c : R): toseq (polyC c) = if c = zeror then [] else [c].
proof. by rewrite /polyC toseqK norm1. qed.

lemma size_polyC c : deg (polyC c) = if c = zeror then 0 else 1.
proof. by rewrite degE /= polyseqC; case (c = zeror). qed.

lemma coefC c i: coeff (polyC c) i = if i = 0 then c else zeror.
proof.
  by rewrite coeffE /= polyseqC; case (c = zeror) => [-> | //]; case (i = 0).
qed.

lemma polyCK: cancel polyC (coefp 0).
proof. by move=> c; rewrite /coefp coefC. qed.

lemma polyC_inj: injective polyC.
proof.
  move=> c1 c2 eqc12; cut := coefC c2 0 => /=.
  by rewrite -eqc12 coefC.
qed.

lemma lead_coefC c: lead_coef (polyC c) = c.
proof.
  by rewrite lead_coefE degE coeffE /= !polyseqC; case (c = zeror).
qed.

(* -------------------------------------------------------------------- *)
lemma coef_ofseq s k: coeff (ofseq s) k = nth zeror s k.
proof. by rewrite coeffE /= toseqK nth_norm. qed.

lemma coef_neg p n: n < 0 => coeff p n = zeror.
proof. by move=> h; rewrite coeffE /= nth_neg. qed.

lemma coef_overdeg p k: deg p <= k => coeff p k = zeror.
proof. by rewrite degE coeffE /= => h; rewrite nth_default. qed.

(* -------------------------------------------------------------------- *)
op poly (E : int -> R) n = ofseq (mkseq E n).

lemma coef_poly n E k:
  coeff (poly E n) k = if 0 <= k < n then E k else zeror.
proof.
  rewrite lezNgt; case (k < 0) => /=.
    by move=> lt0_k; rewrite coef_neg.
  rewrite -lezNgt => ge0_k; case (k < n) => /=.
    by move=> lt_kn; rewrite /poly coef_ofseq nth_mkseq.
  rewrite -lezNgt => le_nk; rewrite /poly coef_ofseq.
  by rewrite nth_default // size_mkseq; smt.
qed.

lemma coefK p: poly (coeff p) (deg p) = p.
proof.
  apply poly_eqP=> x; rewrite coef_poly lezNgt; case (x < 0)=> /=.
    by move=> lt0_x; rewrite coef_neg.
  move=> _; rewrite coeffE degE /=; case (x < size (toseq p)) => //.
  by rewrite -lezNgt => _; rewrite nth_default.
qed.

(* -------------------------------------------------------------------- *)
op poly0 = polyC zeror axiomatized by poly0E.

theory ZModule.
  op (+) (p q : poly) =
    poly (fun i, coeff p i + coeff q i) (max (deg p) (deg q))
    axiomatized by add_polyE.

  op [-] (p : poly) =
    poly (fun i, -(coeff p i)) (deg p)
    axiomatized by opp_polyE.

  lemma coef_add_poly (p q : poly) i : coeff (p + q) i = coeff p i + coeff q i.
  proof.
    case (i < 0) => [lt0_i|]; first by rewrite !coef_neg // addr0.
    rewrite -lezNgt => ge0_i; rewrite add_polyE /= coef_poly ge0_i /=.
    case (i < max (deg p) (deg q)) => //; rewrite -lezNgt => h.
    rewrite !coef_overdeg ?add0r //; smt.
  qed.

  lemma coef_opp_poly (p : poly) i: coeff (-p) i = -(coeff p i).
  proof.
    case (i < 0) => [lt0_i|]; first by rewrite !coef_neg // oppr0.
    rewrite -lezNgt => ge0_i; rewrite opp_polyE /= coef_poly ge0_i /=.
    by case (i < deg p) => // h; rewrite coef_overdeg ?oppr0 // lezNgt.
  qed.

  lemma add_polyA: associative ZModule.(+).
  proof.
    by move=> p q r; rewrite -poly_eqP=> i; rewrite !coef_add_poly addrA.
  qed.

  lemma add_polyC: commutative ZModule.(+).
  proof.
    by move=> p q; rewrite -poly_eqP=> i; rewrite !coef_add_poly addrC.
  qed.

  lemma add_poly0 (p : poly): poly0 + p = p.
  proof.
    by rewrite -poly_eqP=> i; rewrite coef_add_poly poly0E coefC /= add0r.
  qed.

  lemma add_polyN (p : poly): -p + p = poly0.
  proof.
    rewrite -poly_eqP=> i; rewrite coef_add_poly coef_opp_poly.
    by rewrite poly0E coefC /= addNr.
  qed.
end ZModule.
