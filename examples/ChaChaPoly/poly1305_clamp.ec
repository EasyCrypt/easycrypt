(* -------------------------------------------------------------------- *)
(* Poly1305 key clamping and the probability that a clamped key is a    *)
(* root of the difference of two message polynomials.                   *)
(* RFC 8439, section 2.5.1: r[3], r[7], r[11], r[15] &= 15 and          *)
(* r[4], r[8], r[12] &= 252; 22 bits are cleared, so for r made of 16   *)
(* uniform bytes, each value of the clamped r has probability at most  *)
(* 2^-106.                                                              *)
require import AllCore List IntDiv Distr DList StdOrder StdBigop.
require import Poly1305_prime Poly1305_field Poly1305_msg.
import IntOrder Bigreal Bigreal.BRM Zp1305 P1305.

abstract theory Clamp.

clone include MacData.

op dbyte : byte distr.

axiom dbyte1E (b : byte) : mu1 dbyte b = 1%r / 256%r.

(* -------------------------------------------------------------------- *)
(* Indices of the bytes whose top 4 bits, resp. bottom 2 bits, are cleared. *)
op clampA (i : int) = i = 3 \/ i = 7 \/ i = 11 \/ i = 15.
op clampB (i : int) = i = 4 \/ i = 8 \/ i = 12.

op clamp_uint (i x : int) =
  if clampA i then x %% 16 else if clampB i then x - x %% 4 else x.

op clamp_byte (i : int) (b : byte) = of_uint (clamp_uint i (to_uint b)).

op clamp (bs : byte list) =
  mkseq (fun i => clamp_byte i (nth witness bs i)) 16.

op r_of (bs : byte list) = inzmod (le_int (clamp bs)).

op dr = dmap (dlist dbyte 16) r_of.

(* Number of bytes with a given clamped value.                          *)
op nfib (i : int) = if clampA i then 16 else if clampB i then 4 else 1.

op cand (i : int) (w : byte) (j : int) =
  if clampA i then 16 * j + to_uint w else to_uint w + j.

(* -------------------------------------------------------------------- *)
lemma to_uintK (b : byte) : of_uint (to_uint b) = b.
proof. by apply: to_uint_inj; rewrite of_uintK // to_uint_rg. qed.

lemma clamp_uint_rg (i x : int) : 0 <= x < 256 => 0 <= clamp_uint i x < 256.
proof. by rewrite /clamp_uint; smt(modz_ge0 ltz_pmod). qed.

lemma mu_clamp_byte (i : int) (w : byte) :
  mu dbyte (fun b => clamp_byte i b = w) <= (nfib i)%r / 256%r.
proof.
pose s := map (fun j => of_uint (cand i w j)) (range 0 (nfib i)).
apply: (RealOrder.ler_trans (mu dbyte (mem s))).
- apply: mu_le => b _ /= hb; apply/mapP.
  have hw : to_uint w = clamp_uint i (to_uint b).
  - by rewrite -hb /clamp_byte of_uintK // clamp_uint_rg to_uint_rg.
  have [ge0_b lt_b] := to_uint_rg b.
  move: hw; rewrite /cand /nfib /clamp_uint.
  case: (clampA i) => _ hw.
  - exists (to_uint b %/ 16); rewrite mem_range hw; split.
    + by rewrite divz_ge0 //= ltz_divLR.
    by rewrite -{1}(to_uintK b) {1}(divz_eq (to_uint b) 16) mulrC.
  move: hw; case: (clampB i) => _ hw.
  - exists (to_uint b %% 4); rewrite mem_range hw; split.
    + smt(modz_ge0 ltz_pmod).
    by rewrite subrK to_uintK.
  by exists 0; rewrite mem_range hw /= to_uintK.
apply: (RealOrder.ler_trans _ _ _ (mu_mem_le_mu1 dbyte s (1%r / 256%r) _)).
- by move=> x; rewrite dbyte1E.
rewrite size_map size_range ler_maxr; first by rewrite /nfib; smt().
smt().
qed.

lemma clamp_inj (bs1 bs2 : byte list) :
  r_of bs1 = r_of bs2 => clamp bs1 = clamp bs2.
proof.
have hp : 256 ^ 16 < p1305.
- by rewrite p1305E; cbv hint {expr0 expr_pred}.
have sz : forall bs, size (clamp bs) = 16 by move=> bs; rewrite size_mkseq.
have := le_int_rg (clamp bs1); have := le_int_rg (clamp bs2); rewrite !sz.
move=> rg2 rg1; rewrite /r_of -eq_inzmod => h; apply: le_int_inj.
- by rewrite !sz.
by move: h; rewrite !modz_small //; smt().
qed.

lemma prod_nfib :
  bigi predT (fun i => (nfib i)%r / 256%r) 0 16 = 1%r / (2 ^ 106)%r.
proof.
have -> : 2 ^ 106 = 81129638414606681695789005144064.
- by cbv hint {expr0 expr_pred}.
rewrite /nfib /clampA /clampB; do 16! (rewrite big_ltn 1:// /=).
by rewrite big_geq.
qed.

lemma dr1E (x : zmod) : mu1 dr x <= 1%r / (2 ^ 106)%r.
proof.
have h106 : 0 < 2 ^ 106 by rewrite expr_gt0.
rewrite /dr dmap1E /(\o) /pred1.
case: (exists bs0, r_of bs0 = x) => [[bs0 <<-]|nx]; last first.
- have -> : mu (dlist dbyte 16) (fun x0 => r_of x0 = x) = 0%r.
  + by apply: mu0_false => bs _; apply: contra nx => h; exists bs.
  by rewrite RField.div1r RealOrder.invr_ge0 le_fromint ltrW.
pose w := clamp bs0.
apply: (RealOrder.ler_trans (mu (dlist dbyte 16) (fun xs =>
  forall i, (0 <= i) && (i < 16) => clamp_byte i (nth witness xs i) = nth witness w i))).
- apply: mu_le => bs _ /= /clamp_inj h i [ge0_i lt_i].
  by rewrite /w -h /clamp nth_mkseq.
have /= -> := dlistE witness dbyte (fun i b => clamp_byte i b = nth witness w i) 16.
rewrite -RField.div1r -prod_nfib; apply: ler_prod => i _ /=; split.
- by apply: ge0_mu.
by move=> _; apply: mu_clamp_byte.
qed.

(* -------------------------------------------------------------------- *)
op nblocks (a c : byte list) = (size a + 15) %/ 16 + (size c + 15) %/ 16 + 1.

lemma pr_topol_diff (a1 c1 a2 c2 : byte list) (t : zmod) :
  valid_size a1 => valid_size c1 => valid_size a2 => valid_size c2 =>
  (a1, c1) <> (a2, c2) =>
  mu dr (fun r => peval (topol a2 c2) r - peval (topol a1 c1) r = t)
  <= (max (nblocks a1 c1) (nblocks a2 c2))%r / (2 ^ 106)%r.
proof.
move=> va1 vc1 va2 vc2 neq.
pose P := topol a2 c2 - topol a1 c1 - polyC t.
have neq_t : topol a1 c1 <> topol a2 c2.
- by apply: contra neq => /(topol_inj _ _ _ _ va1 vc1 va2 vc2) [-> ->].
have c0 : forall a c, (topol a c).[0] = zero by move=> a c; rewrite /topol polyLE.
have nz_P : P <> poly0.
- apply: contra neq_t => hP; apply/poly_eqP => k ge0_k.
  have := congr1 (fun p => p.[k]) _ _ hP => /=.
  rewrite /P !(polyDE, polyNE) polyCE poly0E.
  case: (k = 0) => [->> _|_]; first by rewrite !c0.
  by rewrite ZModpField.oppr0 ZModpField.addr0 ZModpField.subr_eq0 => ->.
have deg_P : deg P - 1 <= max (nblocks a1 c1) (nblocks a2 c2).
- rewrite /P; have := degB (topol a2 c2 - topol a1 c1) (polyC t).
  have := degB (topol a2 c2) (topol a1 c1).
  have := degC_le t; rewrite !deg_topol /nblocks.
  smt(divz_ge0 size_ge0).
rewrite (mu_eq _ _ (root P)) => [r /=|].
- by rewrite /P !pevalB pevalC ZModpField.subr_eq0.
apply: (RealOrder.ler_trans _ _ _ (mu_root_le dr P (1%r / (2 ^ 106)%r) nz_P dr1E)).
have h106 : 0%r < (2 ^ 106)%r by rewrite lt_fromint expr_gt0.
rewrite RField.div1r; apply: RealOrder.ler_wpmul2r.
- by rewrite RealOrder.invr_ge0 RealOrder.ltrW.
by rewrite le_fromint.
qed.

(* -------------------------------------------------------------------- *)
(* The Poly1305 tag keeps the low 128 bits of the evaluation, so tags   *)
(* are compared modulo 2^128. Two field elements x1, x2 have            *)
(* -p < x2 - x1 < p < 2^130, which leaves at most 8 differences in the  *)
(* field for a given difference modulo 2^128.                           *)
op hpoly (r : zmod) (a c : byte list) = asint (peval (topol a c) r).

lemma modz_diff_small (x y d q : int) :
  0 < q => 0 <= x < 4 * q => 0 <= y < 4 * q => (y - x) %% q = d %% q =>
  exists k, (-4 <= k < 4) /\ y - x = d %% q + k * q.
proof.
move=> gt0_q rgx rgy h; exists ((y - x) %/ q).
have := divz_eq (y - x) q; rewrite h => e; split; last by rewrite (addrC (d %% q)) -e.
pose k := (y - x) %/ q.
have h1 : k * q <= y - x by smt(modz_ge0).
have h2 : y - x < (k + 1) * q by smt(ltz_pmod).
split.
- by rewrite -(ler_pmul2r q) //; smt().
by rewrite -(ltr_pmul2r q) //; smt().
qed.

lemma pr_tag_diff (a1 c1 a2 c2 : byte list) (d : int) :
  valid_size a1 => valid_size c1 => valid_size a2 => valid_size c2 =>
  (a1, c1) <> (a2, c2) =>
  mu dr (fun r => (hpoly r a2 c2 - hpoly r a1 c1) %% 2 ^ 128 = d %% 2 ^ 128)
  <= (8 * max (nblocks a1 c1) (nblocks a2 c2))%r / (2 ^ 106)%r.
proof.
move=> va1 vc1 va2 vc2 neq.
have hq : 0 < 2 ^ 128 by rewrite expr_gt0.
have hp : p1305 <= 4 * 2 ^ 128.
- by rewrite p1305E; cbv hint {expr0 expr_pred}.
apply: (RealOrder.ler_trans (mu dr (fun r => has (fun k =>
  peval (topol a2 c2) r - peval (topol a1 c1) r = inzmod (d %% 2 ^ 128 + k * 2 ^ 128))
  (range (-4) 4)))).
- apply: mu_le => r _ /= h; apply/hasP.
  have := rg_asint (peval (topol a1 c1) r); have := rg_asint (peval (topol a2 c2) r).
  move=> rg2 rg1.
  have [k [rgk e]] := modz_diff_small _ _ d (2 ^ 128) hq _ _ h; 1,2: smt().
  by exists k; rewrite mem_range rgk /= -e inzmodB !asintK.
rewrite fromintM -RField.mulrA.
have := mu_has_leM (fun r k => peval (topol a2 c2) r - peval (topol a1 c1) r
  = inzmod (d %% 2 ^ 128 + k * 2 ^ 128)) dr (range (-4) 4)
  ((max (nblocks a1 c1) (nblocks a2 c2))%r / (2 ^ 106)%r) _.
- by move=> k _ /=; apply: pr_topol_diff.
by rewrite size_range.
qed.

end Clamp.
