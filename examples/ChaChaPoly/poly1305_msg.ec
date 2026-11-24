(* -------------------------------------------------------------------- *)
(* The Poly1305 message polynomial of the ChaCha20-Poly1305 AEAD        *)
(* (RFC 8439, section 2.8): the MAC input                               *)
(*   a || pad16(a) || c || pad16(c) || le64(|a|) || le64(|c|)           *)
(* is cut into 16-byte blocks b_1, ..., b_q and gives the polynomial    *)
(*   sum_i (le(b_i) + 2^128) X^(q - i + 1)                               *)
(* over Z/(2^130 - 5). Different (a, c) give different polynomials.     *)
require import AllCore List IntDiv BitEncoding StdOrder.
require import Poly1305_prime Poly1305_field.
import IntOrder BitChunking Zp1305 P1305.

abstract theory MacData.

type byte.

op to_uint : byte -> int.
op of_uint : int -> byte.

axiom to_uint_rg b : 0 <= to_uint b < 256.
axiom to_uint_inj : injective to_uint.
axiom of_uintK n : 0 <= n < 256 => to_uint (of_uint n) = n.

(* -------------------------------------------------------------------- *)
(* Little-endian encoding.                                              *)
op le_int (bs : byte list) =
  foldr (fun b n => to_uint b + 256 * n) 0 bs.

op le_bytes (k n : int) =
  mkseq (fun i => of_uint (n %/ 256 ^ i %% 256)) k.

lemma le_int_nil : le_int [] = 0.
proof. by rewrite /le_int. qed.

lemma le_int_cons (b : byte) (bs : byte list) :
  le_int (b :: bs) = to_uint b + 256 * le_int bs.
proof. by rewrite /le_int. qed.

lemma le_int_rg (bs : byte list) : 0 <= le_int bs < 256 ^ size bs.
proof.
elim: bs => [|b bs [ge0 lt]]; first by rewrite le_int_nil expr0.
rewrite le_int_cons /= exprD_nneg ?size_ge0 // expr1.
smt(to_uint_rg).
qed.

lemma le_int_inj (b1 b2 : byte list) :
  size b1 = size b2 => le_int b1 = le_int b2 => b1 = b2.
proof.
elim: b1 b2 => [|x1 b1 ih] [|x2 b2] //=; 1,2: smt(size_ge0).
move=> eq_sz; rewrite !le_int_cons => h.
have [h1 h2] : to_uint x1 = to_uint x2 /\ le_int b1 = le_int b2.
- by smt(to_uint_rg).
by rewrite (to_uint_inj _ _ h1) (ih b2 _ h2) // /#.
qed.

lemma le_bytes_cons (k n : int) : 0 <= k =>
  le_bytes (k + 1) n = of_uint (n %% 256) :: le_bytes k (n %/ 256).
proof.
move=> ge0_k; rewrite /le_bytes mkseqSr //= expr0 divz1 /=.
apply: eq_in_mkseq => i [ge0_i _] /=.
by rewrite exprD_nneg // expr1 divzMr // expr_ge0.
qed.

lemma le_bytesK (k n : int) : 0 <= k => 0 <= n < 256 ^ k =>
  le_int (le_bytes k n) = n.
proof.
move=> ge0_k; elim: k ge0_k n => [|k ge0_k ih] n.
- by rewrite expr0 /le_bytes mkseq0 le_int_nil /#.
rewrite exprD_nneg // expr1 => -[ge0_n lt_n].
rewrite le_bytes_cons // le_int_cons of_uintK 1:/# ih; last by smt(divz_eq).
by rewrite divz_ge0 //= ltz_divLR // mulrC.
qed.

lemma size_le_bytes (k n : int) : 0 <= k => size (le_bytes k n) = k.
proof. by move=> ge0_k; rewrite /le_bytes size_mkseq /#. qed.

(* -------------------------------------------------------------------- *)
(* The MAC input.                                                       *)
op pad16 (bs : byte list) =
  nseq ((16 - size bs %% 16) %% 16) (of_uint 0).

op mac_data (a c : byte list) =
  a ++ pad16 a ++ c ++ pad16 c ++ le_bytes 8 (size a) ++ le_bytes 8 (size c).

op valid_size (bs : byte list) = size bs < 2 ^ 64.

lemma size_pad16 (bs : byte list) :
  size bs + size (pad16 bs) = 16 * ((size bs + 15) %/ 16).
proof.
rewrite /pad16 size_nseq ler_maxr; first by smt(modz_ge0).
have := divz_eq (size bs) 16; have := modz_ge0 (size bs) 16 _ => //.
have := ltz_pmod (size bs) 16 _ => //.
move: (size bs %% 16) (size bs %/ 16) => r q ge0_r lt_r ->.
case: (r = 0) => [->> /=|nz_r].
- by rewrite divzMDl // mulrC.
rewrite modz_small 1:/# (_ : q * 16 + r + 15 = (q + 1) * 16 + (r - 1)) 1:/#.
by rewrite divzMDl // (divz_small (r - 1)) 1:/#; ring.
qed.

lemma size_mac_data (a c : byte list) :
  size (mac_data a c) = 16 * ((size a + 15) %/ 16 + (size c + 15) %/ 16 + 1).
proof.
rewrite /mac_data !size_cat !size_le_bytes //.
smt(size_pad16).
qed.

lemma eqseq_catr (s1 s2 s3 s4 : 'a list) : size s3 = size s4 =>
  (s1 ++ s3 = s2 ++ s4) <=> (s1 = s2) /\ (s3 = s4).
proof.
move=> eq_sz; split=> [h|[-> ->] //]; apply/eqseq_cat => //.
by have := congr1 size _ _ h; rewrite !size_cat /#.
qed.

lemma le_bytes8_inj (n1 n2 : int) : 0 <= n1 < 2 ^ 64 => 0 <= n2 < 2 ^ 64 =>
  le_bytes 8 n1 = le_bytes 8 n2 => n1 = n2.
proof.
have e : 2 ^ 64 = 256 ^ 8 by cbv hint {expr0 expr_pred}.
rewrite e => h1 h2 h; rewrite -(le_bytesK 8 n1) // -(le_bytesK 8 n2) //.
by rewrite h.
qed.

lemma mac_data_inj (a1 c1 a2 c2 : byte list) :
  valid_size a1 => valid_size c1 => valid_size a2 => valid_size c2 =>
  mac_data a1 c1 = mac_data a2 c2 => a1 = a2 /\ c1 = c2.
proof.
rewrite /valid_size => va1 vc1 va2 vc2; rewrite /mac_data.
rewrite eqseq_catr ?size_le_bytes // => -[+ hc].
rewrite eqseq_catr ?size_le_bytes // => -[+ ha].
have eq_c : size c1 = size c2.
- by apply: (le_bytes8_inj _ _ _ _ hc); smt(size_ge0).
have eq_a : size a1 = size a2.
- by apply: (le_bytes8_inj _ _ _ _ ha); smt(size_ge0).
rewrite eqseq_catr ?(size_nseq, eq_c) // => -[+ _].
rewrite eqseq_catr // => -[+ ->]; by rewrite eqseq_catr ?(size_nseq, eq_a).
qed.

(* -------------------------------------------------------------------- *)
(* The message polynomial.                                              *)
op coef (b : byte list) = inzmod (le_int b + 2 ^ 128).

op blocks (a c : byte list) = chunk 16 (mac_data a c).

op topol (a c : byte list) =
  polyL (zero :: rev (map coef (blocks a c))).

lemma coef_rg (b : byte list) : size b = 16 =>
  asint (coef b) = le_int b + 2 ^ 128 /\ 2 ^ 128 <= asint (coef b).
proof.
move=> sz_b; have := le_int_rg b; rewrite sz_b.
have -> : 256 ^ 16 = 2 ^ 128 by cbv hint {expr0 expr_pred}.
have e128 : 2 ^ 128 = 340282366920938463463374607431768211456.
- by cbv hint {expr0 expr_pred}.
rewrite /coef inzmodK p1305E e128 => rg; rewrite modz_small /#.
qed.

lemma coef_inj (b1 b2 : byte list) : size b1 = 16 => size b2 = 16 =>
  coef b1 = coef b2 => b1 = b2.
proof.
move=> sz1 sz2 eq; apply: le_int_inj; 1: by rewrite sz1 sz2.
by have := coef_rg b1 sz1; have := coef_rg b2 sz2; rewrite eq /#.
qed.

lemma coef_neq0 (b : byte list) : size b = 16 => coef b <> zero.
proof.
move=> sz_b; rewrite -asint_eq zeroE; have [_] := coef_rg b sz_b.
by move=> h; have /# := expr_gt0 128 2.
qed.

lemma size_blocks (a c : byte list) :
  size (blocks a c) = (size a + 15) %/ 16 + (size c + 15) %/ 16 + 1.
proof. by rewrite /blocks size_chunk // size_mac_data mulKz. qed.

lemma size_in_blocks (a c b : byte list) : b \in blocks a c => size b = 16.
proof. by apply: in_chunk_size. qed.

lemma last_topol (a c : byte list) :
  last zero (zero :: rev (map coef (blocks a c))) <> zero.
proof.
have : 0 < size (blocks a c) by rewrite size_blocks; smt(divz_ge0 size_ge0).
have := size_in_blocks a c; case: (blocks a c) => //= b bs hb _.
by rewrite rev_cons last_rcons; apply: coef_neq0; apply: hb.
qed.

lemma deg_topol (a c : byte list) :
  deg (topol a c) = (size a + 15) %/ 16 + (size c + 15) %/ 16 + 2.
proof.
by rewrite /topol (degL _ (last_topol a c)) /= size_rev size_map size_blocks; ring.
qed.

lemma topol_inj (a1 c1 a2 c2 : byte list) :
  valid_size a1 => valid_size c1 => valid_size a2 => valid_size c2 =>
  topol a1 c1 = topol a2 c2 => a1 = a2 /\ c1 = c2.
proof.
move=> va1 vc1 va2 vc2 eq.
have eq_sz : size (zero :: rev (map coef (blocks a1 c1)))
           = size (zero :: rev (map coef (blocks a2 c2))).
- have := congr1 deg _ _ eq.
  by rewrite /topol (degL _ (last_topol a1 c1)) (degL _ (last_topol a2 c2)).
move: eq => /(inj_polyL _ _ eq_sz) /= /rev_inj.
move=> eq_m.
have eq_b : blocks a1 c1 = blocks a2 c2.
- apply: (in_inj_map coef (fun (b : byte list) => size b = 16) _ _ _ _ _ eq_m).
  + by move=> x y; apply: coef_inj.
  + by apply/allP => b /size_in_blocks.
  + by apply/allP => b /size_in_blocks.
apply: mac_data_inj => //.
have h1 := chunkK 16 (mac_data a1 c1) _ _ => //.
- by rewrite size_mac_data dvdz_mulr.
have h2 := chunkK 16 (mac_data a2 c2) _ _ => //.
- by rewrite size_mac_data dvdz_mulr.
by rewrite -h1 -h2; congr; apply: eq_b.
qed.

end MacData.
