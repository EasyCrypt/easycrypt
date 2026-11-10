(* -------------------------------------------------------------------- *)
(* The generic ChaCha20-Poly1305 proof instantiated with the Poly1305   *)
(* of RFC 8439.                                                         *)
require import AllCore List IntDiv Real Distr DList StdOrder.
require import Poly1305_prime Poly1305_field Poly1305_msg Poly1305_clamp.
require Chacha_poly.
import IntOrder Zp1305 P1305.

(* -------------------------------------------------------------------- *)
(* Bytes stay abstract, with their encoding into [0, 256).              *)
type byte.

op to_uint : byte -> int.
op of_uint : int -> byte.

axiom to_uint_rg (b : byte) : 0 <= to_uint b < 256.
axiom to_uint_inj : injective to_uint.
axiom of_uintK (n : int) : 0 <= n < 256 => to_uint (of_uint n) = n.

(* The uniform distribution on bytes, shared by the Poly1305 clamping   *)
(* (theory Clamp) and by the generic proof (theory Byte.Support below). *)
lemma to_uintK (b : byte) : of_uint (to_uint b) = b.
proof. by apply: to_uint_inj; rewrite of_uintK // to_uint_rg. qed.

clone MFinite as ByteFin with
  type t <- byte,
  op Support.enum = map of_uint (range 0 256)
  proof Support.enum_spec
  rename "dunifin" as "dbyte".

realize Support.enum_spec.
proof.
move=> b; rewrite count_uniq_mem.
- rewrite map_inj_in_uniq ?range_uniq // => x y /mem_range hx /mem_range hy eq.
  by rewrite -(of_uintK x hx) -(of_uintK y hy) eq.
by rewrite b2i_eq1; apply/mapP; exists (to_uint b); rewrite mem_range to_uint_rg to_uintK.
qed.

lemma card_byte : ByteFin.Support.card = 256.
proof. by rewrite /ByteFin.Support.card size_map size_range. qed.

clone Clamp as CL with
  type byte <- byte,
  op to_uint <- to_uint,
  op of_uint <- of_uint,
  op dbyte <- ByteFin.dbyte
proof to_uint_rg, to_uint_inj, of_uintK, dbyte1E.
realize to_uint_rg by exact: to_uint_rg.
realize to_uint_inj by exact: to_uint_inj.
realize of_uintK by exact: of_uintK.
realize dbyte1E.
proof. by move=> b; rewrite ByteFin.dbyte1E card_byte. qed.

(* -------------------------------------------------------------------- *)
(* The Poly1305 key r and the tag are 16 bytes long.                    *)
subtype poly_in as PolyIn = { l : byte list | size l = 16 }
  rename "poly_in_of_bytes", "bytes_of_poly_in".

realize inhabited.
proof. by exists (nseq 16 witness); rewrite size_nseq. qed.
import PolyIn.

subtype poly_out as PolyOut = { l : byte list | size l = 16 }
  rename "poly_out_of_bytes", "bytes_of_poly_out".

realize inhabited.
proof. by exists (nseq 16 witness); rewrite size_nseq. qed.
import PolyOut.

(* Tags are integers modulo 2^128, in little-endian.                    *)
op int_of_poly_out (t : poly_out) = CL.le_int (bytes_of_poly_out t).
op poly_out_of_int (n : int) = poly_out_of_bytesd (CL.le_bytes 16 (n %% 2 ^ 128)).

op poly_out_add (t1 t2 : poly_out) =
  poly_out_of_int (int_of_poly_out t1 + int_of_poly_out t2).

op poly_out_sub (t1 t2 : poly_out) =
  poly_out_of_int (int_of_poly_out t1 - int_of_poly_out t2).

lemma e128 : 256 ^ 16 = 2 ^ 128.
proof. by cbv hint {expr0 expr_pred}. qed.

lemma gt0_e128 : 0 < 2 ^ 128.
proof. by rewrite expr_gt0. qed.

lemma int_of_poly_out_rg (t : poly_out) : 0 <= int_of_poly_out t < 2 ^ 128.
proof. by have := CL.le_int_rg (bytes_of_poly_out t); rewrite bytes_of_poly_outP e128. qed.

lemma int_of_poly_out_inj : injective int_of_poly_out.
proof.
move=> t1 t2 h; apply: bytes_of_poly_out_inj; apply: CL.le_int_inj => //.
by rewrite !bytes_of_poly_outP.
qed.

lemma int_of_poly_outK (n : int) :
  int_of_poly_out (poly_out_of_int n) = n %% 2 ^ 128.
proof.
rewrite /int_of_poly_out /poly_out_of_int poly_out_of_bytesdK ?CL.size_le_bytes //.
by rewrite CL.le_bytesK // e128; smt(modz_ge0 ltz_pmod gt0_e128).
qed.

lemma poly_out_of_intK (t : poly_out) : poly_out_of_int (int_of_poly_out t) = t.
proof.
by apply: int_of_poly_out_inj; rewrite int_of_poly_outK modz_small; smt(int_of_poly_out_rg).
qed.

lemma eq_poly_out_of_int (n1 n2 : int) :
  poly_out_of_int n1 = poly_out_of_int n2 <=> n1 %% 2 ^ 128 = n2 %% 2 ^ 128.
proof.
split=> [h|h]; first by rewrite -!int_of_poly_outK h.
by rewrite /poly_out_of_int h.
qed.

lemma poly_out_subrK (t1 t2 : poly_out) :
  t1 = poly_out_add (poly_out_sub t1 t2) t2.
proof.
rewrite /poly_out_add /poly_out_sub int_of_poly_outK -{1}(poly_out_of_intK t1).
by rewrite eq_poly_out_of_int modzDml subrK.
qed.

lemma poly_out_addrK (t1 t2 : poly_out) :
  t1 = poly_out_sub (poly_out_add t1 t2) t2.
proof.
rewrite /poly_out_add /poly_out_sub int_of_poly_outK -{1}(poly_out_of_intK t1).
by rewrite eq_poly_out_of_int modzDml addrK.
qed.

lemma poly_out_addr_subrr (t1 t2 : poly_out) :
  t1 = poly_out_add t1 (poly_out_sub t2 t2).
proof.
rewrite /poly_out_add /poly_out_sub int_of_poly_outK -{1}(poly_out_of_intK t1).
by rewrite eq_poly_out_of_int modzDmr subrr addr0.
qed.

lemma poly_out_subr_addr (t t1 t2 : poly_out) :
  poly_out_add (poly_out_sub t t1) t2 = poly_out_add t (poly_out_sub t2 t1).
proof.
rewrite /poly_out_add /poly_out_sub !int_of_poly_outK eq_poly_out_of_int.
by rewrite modzDml modzDmr addrA addrAC.
qed.

(* The Poly1305 evaluation: the low 128 bits of m(r) with r clamped.    *)
op poly1305_eval (r : poly_in) (p : poly) =
  poly_out_of_int (asint (peval p (CL.r_of (bytes_of_poly_in r)))).

(* Maximal sizes of the associated data and of the ciphertext accepted  *)
(* in the security game, within the limits of RFC 8439. The bound of    *)
(* the final theorem grows linearly with them.                          *)
op max_ad : int.
op max_cipher : int.

axiom max_ad_rg : 0 <= max_ad <= 2 ^ 64 - 1.
axiom max_cipher_rg : 0 <= max_cipher <= (2 ^ 32 - 1) * 64.

(* Number of 16-byte blocks of the MAC input for maximal sizes.         *)
op max_nblocks = (max_ad + 15) %/ 16 + (max_cipher + 15) %/ 16 + 1.

op pr_zeropol = (8 * max_nblocks)%r / (2 ^ 106)%r.

lemma ge0_pr_zeropol : 0%r <= pr_zeropol.
proof.
rewrite /pr_zeropol RealOrder.divr_ge0 le_fromint; last by rewrite expr_ge0.
by rewrite /max_nblocks; smt(divz_ge0 max_ad_rg max_cipher_rg).
qed.

(* Sizes accepted in the security game.                                 *)
op valid_sizes (a c : byte list) =
  size a <= max_ad /\ size c <= max_cipher.

lemma valid_sizes_size (a c : byte list) :
  valid_sizes a c => CL.valid_size a /\ CL.valid_size c.
proof.
have e64 : 2 ^ 64 = 18446744073709551616 by cbv hint {expr0 expr_pred}.
have e32 : 2 ^ 32 = 4294967296 by cbv hint {expr0 expr_pred}.
by rewrite /valid_sizes /CL.valid_size e64; smt(max_ad_rg max_cipher_rg).
qed.

lemma nblocks_le (a c : byte list) : valid_sizes a c => CL.nblocks a c <= max_nblocks.
proof.
rewrite /valid_sizes /CL.nblocks /max_nblocks => -[ha hc].
by rewrite ler_add2r ler_add leq_div2r // ler_add2r.
qed.

lemma pr_tag_diff_rfc (a1 c1 a2 c2 : byte list) (t1 t2 : poly_out) :
  valid_sizes a1 c1 => valid_sizes a2 c2 =>
  CL.topol a2 c2 <> CL.topol a1 c1 =>
  mu (dmap (dlist ByteFin.dbyte 16) poly_in_of_bytesd)
     (fun r => t2 = poly_out_add t1 (poly_out_sub (poly1305_eval r (CL.topol a2 c2))
                                                 (poly1305_eval r (CL.topol a1 c1))))
  <= pr_zeropol.
proof.
move=> v1 v2 neq; have [va1 vc1] := valid_sizes_size _ _ v1.
have [va2 vc2] := valid_sizes_size _ _ v2.
have neq' : (a1, c1) <> (a2, c2) by apply: contra neq => -[-> ->].
pose d := int_of_poly_out t2 - int_of_poly_out t1.
apply: (RealOrder.ler_trans (mu CL.dr (fun r =>
  (CL.hpoly r a2 c2 - CL.hpoly r a1 c1) %% 2 ^ 128 = d %% 2 ^ 128))).
- rewrite dmapE /CL.dr dmapE; apply: mu_le => bs; rewrite supp_dlist // => -[sz _].
  rewrite /(\o) /= /poly_out_add /poly_out_sub /poly1305_eval poly_in_of_bytesdK //.
  rewrite !int_of_poly_outK -{1}(poly_out_of_intK t2) eq_poly_out_of_int /d /CL.hpoly.
  pose h2 := asint _; pose h1 := asint _; move=> eq_t.
  rewrite -(modzDml (int_of_poly_out t2)) eq_t modzDml addrAC subrr add0r.
  by rewrite modz_mod modzBm.
apply: (RealOrder.ler_trans _ _ _ (CL.pr_tag_diff a1 c1 a2 c2 d va1 vc1 va2 vc2 neq')).
rewrite /pr_zeropol RealOrder.ler_wpmul2r.
- by rewrite RealOrder.invr_ge0 le_fromint expr_ge0.
by rewrite le_fromint ler_wpmul2l // ler_maxrP !nblocks_le.
qed.

(* -------------------------------------------------------------------- *)
clone Chacha_poly as RFC8439 with
  type Byte.byte <- byte,
  theory Byte.Support <- ByteFin.Support,
  op Poly_in.poly_in_size <- 16,
  type Poly_in.poly_in <- poly_in,
  op Poly_in.poly_in_of_bytes <- poly_in_of_bytes,
  op Poly_in.bytes_of_poly_in <- bytes_of_poly_in,
  op Poly_out.poly_out_size <- 16,
  type Poly_out.poly_out <- poly_out,
  op Poly_out.poly_out_of_bytes <- poly_out_of_bytes,
  op Poly_out.bytes_of_poly_out <- bytes_of_poly_out,
  op Extra_block.extra_block_size <- 32,
  op C.max_counter <- 2 ^ 32 - 1,
  type polynomial <- poly,
  op topol <- CL.topol,
  op max_ad_size <- max_ad,
  op max_cipher_size <- max_cipher,
  op poly1305_eval <- poly1305_eval,
  op (+) <- poly_out_add,
  op (-) <- poly_out_sub,
  op pr_zeropol <- pr_zeropol,
  op w1 <- poly_out_of_int 0,
  op w2 <- poly_out_of_int 1
proof Poly_in.ge0_poly_in_size, Poly_out.ge0_poly_out_size,
  Extra_block.ge0_extra_block_size,
  Poly_in.poly_in_of_bytesN by exact: poly_in_of_bytesN,
  Poly_in.poly_in_of_bytesT by exact: poly_in_of_bytesT,
  Poly_in.bytes_of_poly_inP by exact: bytes_of_poly_inP,
  Poly_in.bytes_of_poly_inK by exact: bytes_of_poly_inK,
  Poly_out.poly_out_of_bytesN by exact: poly_out_of_bytesN,
  Poly_out.poly_out_of_bytesT by exact: poly_out_of_bytesT,
  Poly_out.bytes_of_poly_outP by exact: bytes_of_poly_outP,
  Poly_out.bytes_of_poly_outK by exact: bytes_of_poly_outK,
  C.gt0_max_counter, gt0_block_size, max_cipher_size_ok, topol_inj, poly_out_sub_add, poly_out_add_sub,
  poly_out_add_sub', poly_out_swap, ge0_pr_zeropol, pr_zeropol_spec.
realize Poly_in.ge0_poly_in_size by done.
realize Poly_out.ge0_poly_out_size by done.
realize Extra_block.ge0_extra_block_size by done.
realize C.gt0_max_counter by rewrite subr_gt0 exprn_egt1.
realize gt0_block_size by rewrite /Block.block_size.
realize max_cipher_size_ok by rewrite /Block.block_size; smt(max_cipher_rg).
realize topol_inj.
proof.
move=> a1 c1 a2 c2 /valid_sizes_size [va1 vc1] /valid_sizes_size [va2 vc2].
exact: CL.topol_inj.
qed.
realize poly_out_sub_add by exact: poly_out_subrK.
realize poly_out_add_sub by exact: poly_out_addrK.
realize poly_out_add_sub' by exact: poly_out_addr_subrr.
realize poly_out_swap by exact: poly_out_subr_addr.
realize ge0_pr_zeropol by exact: ge0_pr_zeropol.
realize pr_zeropol_spec.
proof.
move=> a1 a2 c1 c2 t1 t2 v1 v2 /=.
exact: pr_tag_diff_rfc.
qed.

(* -------------------------------------------------------------------- *)
lemma neq_w1_w2 : poly_out_of_int 0 <> poly_out_of_int 1.
proof.
by rewrite eq_poly_out_of_int mod0z modz_small //=; smt(expr_gt0 exprn_egt1).
qed.

lemma pr1_poly_outE : RFC8439.pr1_poly_out = 1%r / (2 ^ 128)%r.
proof.
rewrite /RFC8439.pr1_poly_out /RFC8439.Poly_out.dpoly_out.
rewrite (dmap1E_can _ _ bytes_of_poly_out) 1:bytes_of_poly_outKd.
- by move=> bs; rewrite supp_dlist // => -[sz _]; rewrite poly_out_of_bytesdK.
rewrite dlist1E // bytes_of_poly_outP /=.
rewrite (StdBigop.Bigreal.BRM.eq_big_seq _ (fun _ => 1%r / 256%r)) /=.
- by move=> b _; rewrite ByteFin.dbyte1E card_byte.
rewrite StdBigop.Bigreal.mulr_const bytes_of_poly_outP -e128.
by rewrite RField.exprVn // RField.fromintXn.
qed.

lemma pr1_poly_out_le : RFC8439.pr1_poly_out <= pr_zeropol.
proof.
have h106 : 0%r < (2 ^ 106)%r by rewrite lt_fromint expr_gt0.
have h22 : 1%r <= (2 ^ 22)%r by rewrite le_fromint exprn_ege1.
have hN : 1%r <= (8 * max_nblocks)%r.
- by rewrite le_fromint /max_nblocks; smt(divz_ge0 max_ad_rg max_cipher_rg).
rewrite pr1_poly_outE /pr_zeropol (_ : 2 ^ 128 = 2 ^ 106 * 2 ^ 22).
- by rewrite -exprD_nneg.
rewrite RealOrder.ler_pdivl_mulr // fromintM RField.div1r RField.invfM.
rewrite RField.mulrAC RField.mulVf 1:RealOrder.gtr_eqF // RField.mul1r.
apply: (RealOrder.ler_trans 1%r _ _ _ hN).
by rewrite RealOrder.invr_le1 //; smt().
qed.

(* -------------------------------------------------------------------- *)
(* The security of ChaCha20-Poly1305 (RFC 8439): a nonce-respecting     *)
(* adversary making at most qdec decryption queries, with associated    *)
(* data of at most max_ad bytes and ciphertexts of at most max_cipher   *)
(* bytes, distinguishes the real scheme from the ideal AEAD with        *)
(* advantage at most the distance of ChaCha20 from a random oracle plus *)
(* qdec * (8 * max_nblocks / 2^106 + 1 / 2^128), where max_nblocks is   *)
(* the number of 16-byte blocks of the MAC input for maximal sizes.     *)
section Security.

declare module A <: RFC8439.SKE_RND.CCA_Adv {-RFC8439.SKE_RND.Mem,
  -RFC8439.FullRO.RO, -RFC8439.FullRO.FRO, -RFC8439.IndBlock, -RFC8439.BNR}.

declare axiom A_ll (O <: RFC8439.SKE_RND.CCA_Oracles{-A}) :
  islossless O.enc => islossless O.dec => islossless A(O).main.

lemma chacha_poly_rfc_security &m :
  `|Pr[RFC8439.SKE_RND.CCA_game(RFC8439.BNR_Adv(A),
        RFC8439.SKE_RND.RealOrcls(RFC8439.ChaChaPoly)).main() @ &m : res] -
    Pr[RFC8439.SKE_RND.CCA_game(RFC8439.BNR_Adv(A),
        RFC8439.IdealAEAD).main() @ &m : res]| <=
    `|Pr[RFC8439.Indist.Distinguish(RFC8439.D(RFC8439.BNR_Adv(A)),
          RFC8439.IndBlock).game() @ &m : res] -
      Pr[RFC8439.Indist.Distinguish(RFC8439.D(RFC8439.BNR_Adv(A)),
          RFC8439.IndRO).game() @ &m : res]| +
    RFC8439.qdec%r * pr_zeropol +
    RFC8439.qdec%r / (2 ^ 128)%r.
proof.
have h := RFC8439.conclusion_ideal_abs A A_ll neq_w1_w2 &m.
have hm : RealOrder.maxr pr_zeropol RFC8439.pr1_poly_out = pr_zeropol.
- by rewrite RealOrder.maxrE pr1_poly_out_le.
by move: h; rewrite hm pr1_poly_outE RField.div1r.
qed.

end section Security.
