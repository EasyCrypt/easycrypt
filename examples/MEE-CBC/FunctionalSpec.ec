require import Fun Pred Option Int IntExtra IntDiv List.
require import Ring StdRing ABitstring Distr.
require (*--*) AWord MAC_then_Pad_then_CBC.
(*---*) import IntID.

(** A type for octets and its structure **)
type octet.
(** WARNING: This clone implicitly assumes:
    - octet is finite,
    - |octet| = 2^8,
    - a bijection (to_int,from_int) between octet and [0..2^8 - 1],
    - a bijection (to_bits,from_bits) between octet and {x \in {0,1}^* | |x| = 8},
    - the uniform distribution Octet.Dword.dword on octet.
    We should eventually replace it with an axiom-free version of the same. **)
clone import AWord as Octet with
  type word   <- octet,
  op   length <- 8
proof leq0_length by smt.

(** A type for blocks and its structure **)
type block.
(** WARNING: This clone implicitly assumes:
    - block is finite,
    - |block| = 2^128,
    - a bijection (to_int,from_int) between block and [0..2^128 - 1],
    - a bijection (to_bits,from_bits) between block and {x \in {0,1}^* | |x| = 128},
    - the uniform distribution Block.Dword.dword on block.
    We should eventually replace it with an axiom-free version of the same. **)
clone import AWord as Block with
  type word   <- block,
  op   length <- 128
proof leq0_length by smt.

lemma d_block_uffu: is_uniform_over Block.Dword.dword predT.
proof. by do !split; smt. qed.

(** A type for tags and its structure **)
type tag.
(** WARNING: This clone implicitly assumes:
    - tag is finite,
    - |tag| = 2^256,
    - a bijection (to_int,from_int) between tag and [0..2^256 - 1],
    - a bijection (to_bits,from_bits) between tag and {x \in {0,1}^* | |x| = 256}.
    We should eventually replace it with an axiom-free version of the same. **)
clone import AWord as Tag with
  type word   <- tag,
  op   length <- 256
proof leq0_length by smt.

(** Conversions **)
(* octet list <-> bitstring *)
(* WARNING: This is a (underspecified) fixpoint on nat, which we currently need to axiomatize *)
op bits2os (bs : bitstring): octet list.
axiom bits2os0 (bs : bitstring):
  `|bs| = 0 =>
  bits2os bs = [].
axiom bits2osS (bs : bitstring):
  0 < `|bs| =>
  `|bs| %% 8 = 0 =>
  bits2os bs = (Octet.from_bits (sub bs 0 8)) :: bits2os (sub bs 8 (`|bs| - 8)).

lemma size_bits2os (bs : bitstring):
  `|bs| %% 8 = 0 =>
  size (bits2os bs) = `|bs| %/ 8.
proof.
  move: {-1}(`|bs| %/ 8) (eq_refl (`|bs| %/ 8))=> n len_bs.
  have le0_n: 0 <= n by smt.
  elim n le0_n bs len_bs=> [bs bs_is_octets bs_is_empty
                                               |n le0_n ih bs bs_is_nonempty bs_is_octets].
    by rewrite bits2os0 1:smt.
  rewrite bits2osS 1:smt //=.
  have h_len:= length_sub bs 8 (`|bs| - 8) _ _ _ => //=; 1,2:smt.
  rewrite ih 3:addzC// h_len 1,2:smt.
qed.

op os2bits (os : octet list) =
  foldr (fun o bs => (Octet.to_bits o) || bs) (zeros 0) os.

lemma length_os2bits (os : octet list):
  `|os2bits os| = 8 * size os.
proof.
  elim os=> //= [|o os ih].
    by rewrite /os2bits /= length_zeros.
  by rewrite /os2bits /= length_app length_to_bits ih smt.
qed.

lemma bits2osK (os : octet list):
  bits2os (os2bits os) = os.
proof.
  elim os=> //= [|o os ih]; 1:smt.
  have /= := length_os2bits (o :: os).
  rewrite /os2bits /= -/(os2bits _)=> h_len. (* FIXME *)
  rewrite bits2osS /=.
    by rewrite h_len smt.
    by rewrite h_len -(add0z (8 * (1 + size os))) addzC /= modzMr //.
  rewrite -(Octet.length_to_bits o); split.
    by rewrite sub_app_fst Octet.can_from_to.
    rewrite h_len {2}Octet.length_to_bits mulrDr //=.
    rewrite addzC addzA Ring.IntID.addrN addzC.
    by rewrite -length_os2bits sub_app_snd.
qed.

lemma os2bitsK (bs : bitstring):
  `|bs| %% 8 = 0 =>
  os2bits (bits2os bs) = bs.
proof.
  move: {-1}(`|bs| %/ 8) (eq_refl (`|bs| %/ 8))=> n len_bs.
  have le0_n: 0 <= n by smt.
  elim n le0_n bs len_bs=> [|n le0_n ih bs len_bs good_length].
    smt.
  have h_len: `|sub bs 8 (`|bs| - 8)| = `|bs| - 8.
    by rewrite length_sub // 1,2:smt.
  rewrite bits2osS //= 1:smt /os2bits /= -/(os2bits _) ih 1,2:h_len 1,2:smt.
  by rewrite Octet.pcan_to_from 1:smt app_sub //= smt.
qed.

(* block list <-> bitstring *)
(* WARNING: This is a (underspecified) fixpoint on nat - which we currently need to axiomatize *)
op bits2bs (bs : bitstring): block list.
axiom bits2bs0 (bs : bitstring):
  `|bs| = 0 =>
  bits2bs bs = [].
axiom bits2bsS (bs : bitstring):
  0 < `|bs| =>
  `|bs| %% 128 = 0 =>
  bits2bs bs = (Block.from_bits (sub bs 0 128)) :: bits2bs (sub bs 128 (`|bs| - 128)).

lemma size_bits2bs (bs : bitstring):
  `|bs| %% 128 = 0 =>
  size (bits2bs bs) = `|bs| %/ 128.
proof.
  move: {-1}(`|bs| %/ 128) (eq_refl (`|bs| %/ 128))=> n len_bs.
  have le0_n: 0 <= n by smt.
  elim n le0_n bs len_bs=> [bs bs_is_octets bs_is_empty
                                               |n le0_n ih bs bs_is_nonempty bs_is_octets].
    by rewrite bits2bs0 1:smt.
  rewrite bits2bsS 1:smt //=.
  have h_len:= length_sub bs 128 (`|bs| - 128) _ _ _ => //=; 1,2:smt.
  rewrite ih 3:addzC// h_len 1,2:smt.
qed.

op bs2bits (os : block list) =
  foldr (fun o bs => (Block.to_bits o) || bs) (zeros 0) os.

lemma length_bs2bits (bs : block list):
  `|bs2bits bs| = 128 * size bs.
proof.
  elim bs=> //= [|b bs ih].
    by rewrite /bs2bits /= length_zeros.
  by rewrite /bs2bits /= length_app length_to_bits ih smt.
qed.

lemma bits2bsK (bs : block list):
  bits2bs (bs2bits bs) = bs.
proof.
  elim bs=> //= [|b bs ih]; 1:smt.
  have /= := length_bs2bits (b :: bs).
  rewrite /bs2bits /= -/(bs2bits _)=> h_len. (* FIXME *)
  rewrite bits2bsS /=.
    by rewrite h_len smt.
    by rewrite h_len -(add0z (128 * (1 + size bs))) addzC /= modzMr.
  rewrite -(Block.length_to_bits b); split.
    by rewrite sub_app_fst Block.can_from_to.
    rewrite h_len {2}Block.length_to_bits mulrDr /=.
    rewrite addzC addzA Ring.IntID.addrN addzC.
    by rewrite -length_bs2bits sub_app_snd.
qed.

lemma bs2bitsK (bs : bitstring):
  `|bs| %% 128 = 0 =>
  bs2bits (bits2bs bs) = bs.
proof.
  move: {-1}(`|bs| %/ 128) (eq_refl (`|bs| %/ 128))=> n len_bs.
  have le0_n: 0 <= n by smt.
  elim n le0_n bs len_bs=> [|n le0_n ih bs len_bs good_length].
    smt.
  have h_len: `|sub bs 128 (`|bs| - 128)| = `|bs| - 128.
    by rewrite length_sub // 1,2:smt.
  rewrite bits2bsS //= 1:smt /bs2bits /= -/(bs2bits _) ih 1,2:h_len 1,2:smt.
  by rewrite Block.pcan_to_from 1:smt app_sub //= smt.
qed.

(* block list <-> octet list *)
op bs2os bs = bits2os (bs2bits bs).

lemma size_bs2os bs: size (bs2os bs) = 16 * size bs.
proof.
  rewrite /bs2os size_bits2os length_bs2bits.
    by rewrite (_ : 128 = 8 * 16) // -mulrA modzMr.
  rewrite -(mulr1 8) (_ : 128 = 8 * 16) // -mulrA.
  by rewrite divzMpl // divz1.
qed.

op os2bs os = bits2bs (os2bits os).

lemma size_os2bs os:
  size os %% 16 = 0 =>
  size (os2bs os) = size os %/ 16.
proof.
  case/dvdzP=> q ^qE ->; rewrite size_bits2bs length_os2bits.
    by rewrite qE (mulrC q) mulrA /= modzMr.
  by rewrite qE (_ : 128 = 8 * 16) // divzMpl.
qed.

lemma os2bsK bs: os2bs (bs2os bs) = bs.
proof.
  rewrite /os2bs /bs2os os2bitsK ?length_bs2bits ?bits2bsK //.
  by rewrite (_ : 128 = 8 * 16) // -mulrA modzMr.
qed.

lemma bs2osK os:
  size os %% 16 = 0 => bs2os (os2bs os) = os.
proof.
  case/dvdzP=> q qE; rewrite /os2bs /bs2os bs2bitsK ?bits2osK //.
  by rewrite length_os2bits qE mulrCA /= modzMl.
qed.

(* tag <-> octet list *)
op t2os t = bits2os (Tag.to_bits t).

lemma size_t2os t: size (t2os t) = 32.
proof. by rewrite /t2os size_bits2os length_to_bits smt. qed.

op os2t os = Tag.from_bits (os2bits os).

lemma os2tK t: os2t (t2os t) = t.
proof. by rewrite /os2t /t2os os2bitsK 1:length_to_bits 1:smt Tag.can_from_to. qed.

lemma t2osK os:
  size os = 32 =>
  t2os (os2t os) = os.
proof.
  move=> bs_is_tag.
  rewrite /os2t /t2os Tag.pcan_to_from 1:length_os2bits 1:bs_is_tag 1:smt.
  by rewrite bits2osK.
qed.

(* tag <-> block list *)
op t2bs t = os2bs (t2os t).

lemma size_t2bs t: size (t2bs t) = 2.
proof. rewrite /t2bs size_os2bs size_t2os smt. qed.

op bs2t bs = os2t (bs2os bs).

lemma bs2tK t: bs2t (t2bs t) = t.
proof. by rewrite /bs2t /t2bs bs2osK 2:os2tK// size_t2os smt. qed.

lemma t2bsK bs:
  size bs = 2 =>
  t2bs (bs2t bs) = bs.
proof.
  move=> bs_is_tag.
  by rewrite /bs2t /t2bs t2osK 2:os2bsK// size_bs2os bs_is_tag smt.
qed.

type msg = octet list.

(* -------------------------------------------------------------------- *)
(** Functional spec for CBC encryption and decryption with explicit IV **)
(* Definition *)
op cbc_enc (P : block -> block -> block) (k:block) (st:block) p =
  with p = []      => []
  with p = pi :: p => let ci = P k (st ^ pi) in ci::(cbc_enc P k ci p).

op cbc_dec (Pi : block -> block -> block) (k:block) (st:block) c =
  with c = []      => []
  with c = ci :: c => let pi = Pi k ci in (pi ^ st)::(cbc_dec Pi k ci c).

(* Alternative fold-based definition... Probably a lot more useful for
   program verification *)
op cbc_enc_block (P : block -> block -> block) k (stc:block * block list) pi =
  let (st,c) = stc in
  let ci = P k (st ^ pi) in
  (ci,rcons c ci).

op cbc_enc_fold P (k iv:block) p =
  (foldl (cbc_enc_block P k) (iv,[]) p).`2.

lemma cbc_enc_cbc_fold P k iv p:
  cbc_enc P k iv p = cbc_enc_fold P k iv p.
proof.
  rewrite /cbc_enc_fold /= -(cat0s (cbc_enc P k iv p)).
  elim p iv []=> //= [iv acc|pi p ih iv acc].
    by rewrite cats0.
  by rewrite -cat_rcons ih.
qed.

op cbc_dec_block (Pi : block -> block -> block) k (stp:block * block list) ci =
  let (st,p) = stp in
  let pi = Pi k ci in
  (ci,rcons p (pi ^ st)).

op cbc_dec_fold Pi (k iv:block) c =
  (foldl (cbc_dec_block Pi k) (iv,[]) c).`2.

lemma cbc_dec_cbc_fold Pi k iv c:
  cbc_dec Pi k iv c = cbc_dec_fold Pi k iv c.
proof.
  rewrite /cbc_dec_fold /= -(cat0s (cbc_dec Pi k iv c)).
  elim c iv []=> //= [iv acc|ci c ih iv acc].
    by rewrite cats0.
  by rewrite -cat_rcons ih.
qed.

(* Correctness *)
lemma cbc_correct P Pi k st p:
  cancel (P k) (Pi k) =>
  cbc_dec Pi k st (cbc_enc P k st p) = p.
proof.
  move=> PiK; elim p st=> //= pi p ih st.
  split; 2:by apply/ih.
  by rewrite PiK; smt.
qed.

(* Useful lemmas *)
lemma cbc_enc_rcons (P : block -> block -> block) k st (p:block list) pn:
  rcons (cbc_enc P k st p) (P k (nth witness (st :: cbc_enc P k st p) (size p) ^ pn))
  = cbc_enc P k st (rcons p pn).
proof.
  elim p st=> //=.
  move=> pi p ih st.
  have -> /=: 1 + size p <> 0 by smt.
  have ->: 1 + size p - 1 = size p by smt.
  by rewrite -ih.
qed.

lemma cbc_dec_rcons (Pi : block -> block -> block) k st (c:block list) cn:
  rcons (cbc_dec Pi k st c) ((Pi k cn) ^ (if 0 < size c then nth witness c (size c - 1) else st))
  = cbc_dec Pi k st (rcons c cn).
proof.
  elim c st=> //=.
  move=> ci c ih st //=.
  have -> /=: 0 < 1 + size c by smt.
  have ->: 1 + size c - 1 = size c by smt.
  by rewrite -ih; smt.
qed.

lemma size_cbc_enc P k iv p: size (cbc_enc P k iv p) = size p.
proof. by elim p iv=> //= p0 p ih iv; rewrite ih. qed.

(* -------------------------------------------------------------------- *)
(** Functional spec for padding a (msg * tag) pair into a block list   **)
(* Definition. TODO: Once we've moved to layered lists, things should
   be easier on the modular arithmetic side... *)
(** TODO: Clean up this entire section, whether or not we've moved
    to better libraries **)
op pad_length (m : msg) = 16 - size m %% 16.

op padding (l : int) =
  mkseq (fun i => (Octet.from_int l)) l.

op pad (m : msg) (t : tag) =
  let p = padding (pad_length m) in
  os2bs (m ++ t2os t ++ p).

op unpad (bs : block list) =
  let os = bs2os bs in
  let l  = Octet.to_int (last witness os) in
  let m  = take (size os - l - 32) os in
  let t  = os2t (take 32 (drop (size os - l - 32) os)) in
  let p  = drop (size os - l) os in
  if   (1 <= l <= 16 /\ p = padding l)
  then Some (m,t)
  else None.

(* Proofs for instantiation *)
lemma size_padding m: size (padding (pad_length m)) = 16 - size m %% 16.
proof. by rewrite /padding /= size_mkseq smt. qed.

lemma last_padding x m: last x (padding (pad_length m)) = Octet.from_int (16 - size m %% 16).
proof.
  rewrite /padding /mkseq /= -(last_nonempty ((fun x => Octet.from_int (16 - size m %% 16)) witness<:int>)).
    case {-1}(iota_ 0 (16 - size m %% 16)) (eq_refl (iota_ 0 (16 - size m %% 16)))=> //=.
    by have:= size_iota 0 (16 - size m %% 16); smt.
  by rewrite last_map.
qed.

lemma size_padded m t:
  size (m ++ t2os t ++ padding (pad_length m))
  = 48 + (size m - size m %% 16).
proof. by rewrite !size_cat size_padding size_t2os smt. qed.

lemma padded_is_blocks m t:
  size (m ++ t2os t ++ padding (pad_length m)) %% 16 = 0.
proof.
  rewrite size_padded (_ : 48 = 16 * 3) // -modzDm modzMr //=.
  by rewrite modz_mod -divzE modzMl.
qed.

lemma size_pad m t:
  size (pad m t) (* this is in blocks of 16 octets *)
  = size m %/ 16 (* message *) + 2 (* tag *) + 1 (* padding *).
proof.
  rewrite /pad /= size_os2bs 1:padded_is_blocks // size_padded.
  by rewrite (_ : 48 = 3 * 16) ?divzMDl // -divzE -addrA addrC /= mulzK.
qed.

lemma unpad_pad m t: unpad (pad m t) = Some (m,t).
proof.
  rewrite /unpad.
  have -> /=: bs2os (pad m t)
              = m ++ t2os t ++ padding (pad_length m).
    by rewrite /pad /= bs2osK 1:padded_is_blocks.
  rewrite !last_cat last_padding Octet.from_to.
  rewrite (powS 7 2)// (powS 6 2)// (powS 5 2)// (powS 4 2)//
          (powS 3 2)// (powS 2 2)// (powS 1 2)// (powS 0 2)//
          (pow0 2) /=.
  have h: 0 < 16 - size m %% 16 <= 16 < 256 by smt.
  have ->: (16 - size m %% 16) %% 256 = 16 - size m %% 16 by smt.
  rewrite drop_size_cat.
    by rewrite !size_cat size_padding smt.
  rewrite {1}/pad_length /=.
  rewrite -catA take_size_cat //=.
    rewrite !size_cat size_padding 1:smt.
  rewrite drop_size_cat.
    rewrite !size_cat size_padding 1:smt.
  rewrite (_: 1 <= 16 - size m %% 16 <= 16) 1:smt /=.
  by rewrite take_size_cat 1:size_t2os// os2tK.
qed.

lemma leak_pad m t:
  size (pad m t)
  = size (pad (mkseq (fun (i : int) => Octet.zeros) (size m - size m %% 16)) t).
proof.
  rewrite /pad /=.
  do 2!rewrite size_os2bs 1:padded_is_blocks//.
  rewrite !size_cat !size_padding !size_mkseq.
  have ->: max 0 (size m - size m %% 16) = (size m - size m %% 16) by smt.
  by congr; ringeq; rewrite -divzE modzMl //.
qed.

(* -------------------------------------------------------------------- *)
(** Functional spec for MAC-then-Pad-then-Encrypt                      **)

(* We parameterize it with a (stateless deterministic) PRP (called AES) *)
theory AES.
  op AES : block -> block -> block.
  op AESi: block -> block -> block.

  axiom AES_correct (k : block):
       cancel (AES k) (AESi k)
    /\ cancel (AESi k) (AES k).
end AES.
import AES.

(* and a (stateless, deterministic) MAC (called HMAC_SHA256) *)
theory HMAC_SHA256.
  type mK.

  op d_mK: mK distr.
  axiom d_mK_uffu: is_uniform_over d_mK Pred.predT.

  op hmac_sha256: mK -> msg -> tag.
end HMAC_SHA256.
import HMAC_SHA256.

(* Definition. *)
op mee_enc (P : block -> block -> block) (M : mK -> msg -> tag)
           (ek : block) (mk : mK) (iv : block) (m : msg) =
  let t = M mk m in
  let p = pad m t in
  cbc_enc P ek iv p.

op mee_dec (Pi : block -> block -> block) (M : mK -> msg -> tag)
           (ek : block) (mk : mK) (iv : block) (c : block list) =
  let p = cbc_dec Pi ek iv c in
  let mt = unpad p in
  if   (mt <> None)
  then let (m,t) = oget mt in
       if   M mk m = t
       then Some m
       else None
  else None.

lemma mee_correct P Pi M ek mk iv m:
  cancel (P ek) (Pi ek) =>
  mee_dec Pi M ek mk iv (mee_enc P M ek mk iv m) = Some m.
proof.
  rewrite /mee_dec /mee_enc /= => /cbc_correct ->.
  by rewrite unpad_pad.
qed.

(* -------------------------------------------------------------------- *)
(** Final Instantiation: mee_enc and mee_dec are IND$-CPA and INT-PTXT **)
op q: {int | 0 < q  } as lt0_q.
op n: {int | 0 <= n } as le0_n.

clone import MAC_then_Pad_then_CBC as MEEt with
  (* PRP parameters and operations on the relevant types *)
  type eK                   <- block,
  type block                <- block,
  op   d_eK                 <- Block.Dword.dword,
  op   d_block              <- Block.Dword.dword,
  op   P                    <- AES,
  op   Pinv                 <- AESi,
  op   zeros                <- Block.zeros,
  op   (+)                  <- Block.(^),
  (* MAC parameters *)
  type mK                   <- mK,
  type msg                  <- msg,
  type tag                  <- tag,
  op   d_mK                 <- d_mK,
  op   mac                  <- hmac_sha256,
  (* pad parameters *)
  op   pad (mt : msg * tag) <- pad mt.`1 mt.`2,
  op   unpad                <- unpad,
  op   leak       (m : msg) <- mkseq (fun i => Octet.zeros) (size m - size m %% 16),
  op   valid_msg  (m : msg) <- size m %/ 16 < n,
  (* security parameters *)
  op   q                    <- q,
  op   n                    <- n + 3
proof * by smt.

(* -------------------------------------------------------------------- *)
(** We show that the pWhile programs on which we do the security proof
    fully and faithfully implement the operators used as functional
    specs for the C code... **)
import Dapply.

phoare mee_encrypt_correct _mk _ek _p _c:
  [MEEt.MEE(MEEt.PRPa.PRPr,MEEt.MAC).enc: key = (_ek,_mk) /\ p = _p
                                      ==> res = _c]
  =(mu (dapply (fun iv => iv :: mee_enc AES hmac_sha256 _ek _mk iv _p) Top.Block.Dword.dword) (pred1 _c)).
proof.
  rewrite -/(mu_x _ _) Dapply.mu_x_def /preim /pred1 /=.
  proc; inline MAC.tag PRPa.PRPr.f.
  swap 6 -5 => //=; alias 2 iv = s.
  while (   0 <= i <= size (pad _p (hmac_sha256 _mk _p))
         /\ ek = _ek
         /\ p' = pad _p (hmac_sha256 _mk _p)
         /\ s  = nth witness c i
         /\ size c = i + 1
         /\ c      = iv :: cbc_enc AES _ek iv (take i (pad _p (hmac_sha256 _mk _p))))
        (size (pad _p (hmac_sha256 _mk _p)) - i).
    by auto; smt.
  wp=> //=.
  conseq (_: _ ==> s :: mee_enc AES hmac_sha256 _ek _mk s _p = _c)=> //=.
    move=> &m [->>] ->> iv //=; split=> [[[le0_size _] h]|<<-].
      have -> //=:= h (iv :: mee_enc AES hmac_sha256 _ek _mk iv _p)
                      (nth witness (iv :: mee_enc AES hmac_sha256 _ek _mk iv _p)
                                   (size (pad _p (hmac_sha256 _mk _p))))
                      (size (pad _p (hmac_sha256 _mk _p))).
      split=> //=.
      split; 1:by rewrite /mee_enc /= size_cbc_enc addzC.
      by rewrite take_size.
    split=> [|c s0 n]; 1:by split; [rewrite size_ge0|rewrite take0].
    split=> [[[le0_n le_n_size] [s0_is_nth [size_c]]] c_is_enc|].
      by rewrite StdOrder.IntOrder.ler_subl_addr add0z=> /StdOrder.IntOrder.ler_gtF.
    rewrite -lezNgt=> le_size_n [[le0_n le_n_size]] [_] [_] ->.
    have [_ ->] //:= eqz_leq n (size (pad _p (hmac_sha256 _mk _p))).
    by rewrite take_size.
  by rnd.
qed.

phoare mee_decrypt_correct _mk _ek _c:
  [MEEt.MEE(MEEt.PRPa.PRPr,MEEt.MAC).dec: key = (_ek,_mk) /\ c = _c
                                      ==> res = mee_dec AESi hmac_sha256 _ek _mk (head witness _c) (behead _c)]
  =1%r.
proof.
  conseq (_: true ==> true) (_: _ ==> _)=> //=.
    proc; inline MAC.verify PRPa.PRPr.finv; wp.
    while (   0 <= i <= size c
           /\ ek = _ek
           /\ s  = (if 0 < i then nth witness c (i - 1) else head witness _c)
           /\ size padded = i
           /\ padded = cbc_dec AESi _ek (head witness _c) (take i c)).
      auto; progress; 1..4:smt.
      by rewrite (take_nth witness)// -cbc_dec_rcons cats1 -H1 smt.
    by auto; smt.
  by proc; inline *; wp; while true (size c - i); auto; smt.
qed.
