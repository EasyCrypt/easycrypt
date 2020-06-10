require import AllCore IntDiv List.
require import Ring StdRing StdOrder StdBigop Distr.
require import BitEncoding.
require (*--*) BitWord MAC_then_Pad_then_CBC.
(*---*) import BS2Int BitChunking IntID IntOrder Bigint BIA.

(** A type for octets and its structure **)
clone import BitWord as Octet with
  op n <- 8
rename "word" as "octet"
rename "Word" as "Octet"
proof gt0_n by done.

op o2int (o : octet) : int = bs2int (ofoctet o).
op int2o (i : int) : octet = mkoctet (int2bs 8 i).

lemma o2intK (o : octet): int2o (o2int o) = o.
proof.
by rewrite /int2o /o2int -(size_octet o) bs2intK mkoctetK.
qed.

lemma int2oK (i : int): 0 <= i < 2^8 => o2int (int2o i) = i.
proof.
move=> ge0_i_lt256; rewrite /o2int /int2o ofoctetK 1:size_int2bs //.
by rewrite int2bsK.
qed.

(** A type for blocks and its structure **)
clone import Word as Block with
  type Alphabet.t    <- octet,
  op   Alphabet.enum <- Octet.octets,
  op   n             <- 16
rename "word" as "block"
rename "Word" as "Block"
proof Alphabet.enum_spec, ge0_n by done.
realize Alphabet.enum_spec by exact/Octet.enum_spec.

abbrev dblock = DBlock.dunifin.

lemma dblock_uffu: is_lossless dblock /\ is_funiform dblock.
proof.
split; first by rewrite DBlock.dunifin_ll.
by rewrite DBlock.dunifin_funi.
qed.

(** Boolean ring structure **)
(* FIXME (PY): Throughout the following, pattern-matching can become
   really slow because of the fact that pretty much all defs have an
   "offun" at their head (with different types) *)
op zerob : block = Block.offun (fun _=> zerow).
op oneb  : block = Block.offun (fun _=> onew).
op oppb (b : block) = b.
op (+^) (b1 b2 : block) = Block.offun (fun i=> b1.[i] +^ b2.[i]).
op andb (b1 b2 : block) = Block.offun (fun i=> andw b1.[i] b2.[i]).

lemma oneb_neq0: oneb <> zerob.
proof.
rewrite blockP negb_forall /=; exists 0=> /=.
by rewrite !offunE // onew_neq0.
qed.

lemma xorbE (b1 b2 : block) i: 0 <= i < 16 =>
  (b1 +^ b2).[i] = b1.[i] +^ b2.[i].
proof. by move=> /offunE ->. qed.

lemma xorb0: right_id zerob (+^).
proof. by move=> b; apply/blockP=> i ge0_gti_n; rewrite !xorbE 2:offunE // xorw0. qed.

lemma xorbC: commutative (+^).
proof. by move=> b1 b2; apply/blockP=> i ge0_gti_n; rewrite !xorbE // xorwC. qed.

lemma xorbA: associative (+^).
proof. by move=> b1 b2 b3; apply/blockP=> i ge0_gti_n; rewrite !xorbE // xorwA. qed.

lemma xorbK (b : block): b +^ b = zerob.
proof. by apply/blockP=> i ge0_gti_n; rewrite !xorbE 2:offunE // !xorwK. qed.

lemma andbE (b1 b2 : block) i: 0 <= i < 16 =>
  (andb b1 b2).[i] = andw b1.[i] b2.[i].
proof. by move=> /offunE ->. qed.

lemma andb1: right_id oneb andb.
proof. by move=> b; apply/blockP=> i ge0_gti_n; rewrite !andbE 2:offunE // andw1. qed.

lemma andbC: commutative andb.
proof. by move=> b1 b2; apply/blockP=> i ge0_gti_n; rewrite !andbE // andwC. qed.

lemma andbA: associative andb.
proof. by move=> b1 b2 b3; apply/blockP=> i ge0_gti_n; rewrite !andbE // andwA. qed.

lemma andbK: idempotent andb.
proof. by move=> b; apply/blockP=> i get0_gti_n; rewrite !andbE // andwK. qed.

lemma andbDl: left_distributive andb (+^).
proof.
move=> b1 b2 b3; apply/blockP=> i ge0_gti_n.
(* In particular, here, try: rewrite !xorbE. *)
by rewrite andbE 2:xorbE // andwDl -?andbE -?xorbE.
qed.

instance bring with block
  op rzero = zerob
  op rone  = oneb
  op add   = Self.(+^)
  op mul   = Self.andb
  op opp   = Self.oppb

  proof oner_neq0 by apply/oneb_neq0
  proof addr0     by apply/xorb0
  proof addrA     by apply/xorbA
  proof addrC     by apply/xorbC
  proof addrK     by apply/xorbK
  proof mulr1     by apply/andb1
  proof mulrA     by apply/andbA
  proof mulrC     by apply/andbC
  proof mulrDl    by apply/andbDl
  proof mulrK     by apply/andbK
  proof oppr_id   by done.

(** A type for tags and its structure **)
clone import Word as Tag with
  type Alphabet.t    <- octet,
  op   Alphabet.enum <- Octet.octets,
  op   n             <- 32
rename "word" as "tag"
rename "Word" as "Tag"
proof Alphabet.enum_spec, ge0_n by done.
realize Alphabet.enum_spec by exact/Octet.enum_spec.

(** Messages are just octet lists **)
type msg = octet list.

(** Conversions **)
op bs2os (bs : block list) : octet list =
  flatten (map ofblock bs).

op os2bs (os : octet list) : block list =
  map mkblock (chunk 16 os).

lemma size_bs2os (bs : block list):
  size (bs2os bs) = 16 * size bs.
proof.
elim: bs=> //= [|x xs ih].
+ by rewrite /bs2os /flatten.
rewrite /bs2os /= flatten_cons size_cat size_block ih.
by algebra.
qed.

lemma size_os2bs (os : octet list):
  size (os2bs os) = size os %/ 16.
proof. by rewrite size_map size_chunk. qed.

lemma bs2osK (bs : block list):
  os2bs (bs2os bs) = bs.
proof.
rewrite /os2bs /bs2os flattenK //.
+ by move=> os /mapP [] b [] _ ->; rewrite size_block.
by rewrite -map_comp id_map // => x @/(\o); rewrite mkblockK.
qed.

lemma os2bsK (os : octet list):
  16 %| size os => bs2os (os2bs os) = os.
proof.
move=> sz_os; rewrite /os2bs /bs2os -map_comp.
pose F := _ \o _; have [+ _] - ->:= eq_in_map F (fun x=> x) (chunk 16 os).
+ move=> x in_chunk; rewrite /F /(\o) ofblockK //.
  by apply/(in_chunk_size _ _ _ _ in_chunk).
by rewrite id_map 2:chunkK.
qed.

op t2os (t : tag) : octet list = oftag t.

op os2t (os : octet list) : tag =
  mktag (head witness (chunk 32 os)).

lemma size_t2os (t : tag): size (t2os t) = 32.
proof. by rewrite /t2os size_tag. qed.

lemma t2osK (t : tag): os2t (t2os t) = t.
proof.
rewrite /os2t /t2os /chunk size_tag divzz /b2i /=.
rewrite /mkseq /= (iotaS _ 0) //= drop0.
by rewrite -(size_tag t) take_size mktagK.
qed.

lemma os2tK (os : octet list): size os = 32 => t2os (os2t os) = os.
proof.
move=> sz_os; rewrite /t2os /os2t /chunk sz_os divzz /b2i /=.
by rewrite /mkseq /= (iotaS _ 0) //= drop0 -sz_os take_size  oftagK.
qed.

(* -------------------------------------------------------------------- *)
(** Functional spec for CBC encryption and decryption with explicit IV **)
(* Definition *)
op cbc_enc (P : block -> block -> block) (k:block) (st:block) p =
  with p = []      => []
  with p = pi :: p => let ci = P k (st +^ pi) in ci::(cbc_enc P k ci p).

op cbc_dec (Pi : block -> block -> block) (k:block) (st:block) c =
  with c = []      => []
  with c = ci :: c => let pi = Pi k ci in (pi +^ st)::(cbc_dec Pi k ci c).

(* Alternative fold-based definition... Probably a lot more useful for
   program verification *)
op cbc_enc_block (P : block -> block -> block) k (stc:block * block list) pi =
  let (st,c) = stc in
  let ci = P k (st +^ pi) in
  (ci,rcons c ci).

op cbc_enc_fold P (k iv:block) p =
  (foldl (cbc_enc_block P k) (iv,[]) p).`2.

lemma cbc_enc_cbc_fold P k iv p:
  cbc_enc P k iv p = cbc_enc_fold P k iv p.
proof.
  rewrite /cbc_enc_fold /= -(cat0s (cbc_enc P k iv p)).
  elim: p iv []=> //= [iv|pi p ih iv acc].
    by rewrite cats0.
  by rewrite -cat_rcons ih.
qed.

op cbc_dec_block (Pi : block -> block -> block) k (stp:block * block list) ci =
  let (st,p) = stp in
  let pi = Pi k ci in
  (ci,rcons p (pi +^ st)).

op cbc_dec_fold Pi (k iv:block) c =
  (foldl (cbc_dec_block Pi k) (iv,[]) c).`2.

lemma cbc_dec_cbc_fold Pi k iv c:
  cbc_dec Pi k iv c = cbc_dec_fold Pi k iv c.
proof.
  rewrite /cbc_dec_fold /= -(cat0s (cbc_dec Pi k iv c)).
  elim: c iv []=> //= [iv|ci c ih iv acc].
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
  by rewrite PiK; algebra.
qed.

(* Useful lemmas *)
lemma cbc_enc_rcons (P : block -> block -> block) k st (p:block list) pn:
  rcons (cbc_enc P k st p) (P k (nth witness (st :: cbc_enc P k st p) (size p) +^ pn))
  = cbc_enc P k st (rcons p pn).
proof.
  elim p st=> //= pi p ih st /=.
  by rewrite add1z_neq0 1:size_ge0 /= addzC (addzC (-1)) -ih.
qed.

lemma cbc_dec_rcons (Pi : block -> block -> block) k st (c:block list) cn:
  rcons (cbc_dec Pi k st c) ((Pi k cn) +^ (if 0 < size c then nth witness c (size c - 1) else st))
  = cbc_dec Pi k st (rcons c cn).
proof.
  elim c st=> //= ci c ih st //=.
  rewrite -lez_add1r /= ler_addl size_ge0 /=.
  rewrite addzC -ih /=.
  by rewrite ltzNge lez_eqVlt negb_or ltzNge size_ge0 /= if_neg addzC.
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

op padding (l : int) = mkseq (fun i => (int2o l)) l.

op pad (m : msg) (t : tag) =
  let p = padding (pad_length m) in
  os2bs (m ++  (t2os t) ++ p).

op unpad (bs : block list) =
  let os = bs2os bs in
  let l  = o2int (last witness os) in
  let m  = take (size os - l - 32) os in
  let t  = os2t (take 32 (drop (size os - l - 32) os)) in
  let p  = drop (size os - l) os in
  if   (1 <= l <= 16 /\ p = padding l)
  then Some (m,t)
  else None.

(* Proofs for instantiation *)
lemma size_padding m: size (padding (pad_length m)) = 16 - size m %% 16.
proof. by rewrite /padding /= size_mkseq [smt (size_ge0 @IntDiv)]. qed.

lemma last_padding x m: last x (padding (pad_length m)) = int2o (16 - size m %% 16).
proof.
rewrite /padding /mkseq /= -(last_nonempty ((fun x => int2o (16 - size m %% 16)) witness<:int>)).
+ have h: 0 < 16 - size m %% 16 by rewrite subr_gt0 &(ltz_pmod).
  by apply/negP => /(congr1 size); rewrite size_map /= size_iota /#.
by rewrite last_map.
qed.

lemma size_padded m t:
  size (m ++ t2os t ++ padding (pad_length m))
  = 48 + (size m - size m %% 16).
proof.
by rewrite !size_cat size_padding size_t2os [smt (@IntDiv)].
qed.

lemma padded_is_blocks m t:
  size (m ++ t2os t ++ padding (pad_length m)) %% 16 = 0.
proof.
rewrite size_padded (_ : 48 = 16 * 3) // -modzDm modzMr //=.
by rewrite modz_mod -divzE modzMl.
qed.

lemma size_pad m t:
  size (pad m t) (* this is in blocks of 16 octets *)
  = size m %/ 16 (* message *) + 2 (* tag *) + 1 (* padding *).
proof. by rewrite /pad /= size_os2bs size_padded [smt (@IntDiv)]. qed.

lemma padK m t: unpad (pad m t) = Some (m,t).
proof.
rewrite /unpad.
have -> /=: bs2os (pad m t)
            = m ++ t2os t ++ padding (pad_length m).
+ by rewrite /pad /= os2bsK // size_padded [smt (@IntDiv)].
rewrite !last_cat last_padding int2oK.
+ split=> [|_]; first by smt (size_ge0 @IntDiv).
  by apply/(ler_lt_trans 16); [smt (size_ge0 @IntDiv)|smt (exprS expr0)].
rewrite drop_size_cat.
+ by rewrite !size_cat size_padding /#.
rewrite {1}/pad_length /=.
rewrite -catA take_size_cat //=.
+ by rewrite !size_cat size_padding 1:size_t2os /#.
rewrite drop_size_cat.
+ by rewrite !size_cat size_padding 1:size_t2os /#.
rewrite (_: 1 <= 16 - size m %% 16 <= 16) 1:[smt (@IntDiv)] /=.
+ by rewrite take_size_cat 1:size_t2os// t2osK.
qed.

lemma leak_pad m t:
  size (pad m t)
  = size (pad (mkseq (fun (i : int) => zerow) (size m - size m %% 16)) t).
proof.
rewrite /pad /= !size_os2bs !size_padded size_mkseq ler_maxr.
+ case: (size m < 16)=> [|/lezNgt] szm_16.
  + by rewrite modz_small 1:size_ge0.
  smt (@IntDiv).
by do 2! congr; ringeq; rewrite -divzE modzMl.
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
  axiom d_mK_uffu: is_lossless d_mK /\ is_funiform d_mK.

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
by rewrite padK.
qed.

(* -------------------------------------------------------------------- *)
(** Final Instantiation: mee_enc and mee_dec are IND$-CPA and INT-PTXT **)
op q: {int | 0 < q  } as gt0_q.
op n: {int | 0 <= n } as ge0_n.

clone import MAC_then_Pad_then_CBC as MEEt with
  (* PRP parameters and operations on the relevant types *)
  type eK                   <- block,
  type block                <- block,
  op   d_eK                 <- dblock,
  op   d_block              <- dblock,
  op   P                    <- AES,
  op   Pi                   <- AESi,
  op   zeros                <- zerob,
  op   (+)                  <- (+^),
  (* MAC parameters *)
  type mK                   <- mK,
  type msg                  <- msg,
  type tag                  <- tag,
  op   d_mK                 <- d_mK,
  op   mac                  <- hmac_sha256,
  (* pad parameters *)
  op   pad (mt : msg * tag) <- pad mt.`1 mt.`2,
  op   unpad                <- unpad,
  op   leak       (m : msg) <- mkseq (fun i => zerow) (size m - size m %% 16),
  op   valid_msg  (m : msg) <- size m %/ 16 < n,
  (* security parameters *)
  op   q                    <- q,
  op   n                    <- n + 3
proof *.
realize d_eK_uffu    by exact/dblock_uffu.
realize d_block_uffu by exact/dblock_uffu.
realize d_mK_uffu    by exact/d_mK_uffu.
realize bijectiveP   by move=> b _; exact/AES_correct.
realize add0b        by move=> b; rewrite xorbC xorb0.
realize addbA        by move=> y x z; exact/xorbA.
realize addbC        by exact/xorbC.
realize addbK        by exact/xorbK.
realize can_unpad    by move=> []; exact/padK.
realize pad_tag      by move=> m t0 t1 /=; rewrite !size_pad.
realize leak_pad     by move=> m t /=; rewrite leak_pad.
realize gt0_q        by exact/gt0_q.
realize gt1_n        by smt (ge0_n).
realize max_pad_n    by move=> m t szm /=; rewrite size_pad -addrA ltr_add2r.

(* -------------------------------------------------------------------- *)
(** We show that the pWhile programs on which we do the security proof
    fully and faithfully implement the operators used as functional
    specs for the C code... **)

phoare mee_encrypt_correct _mk _ek _p _c:
  [MEEt.MEE(MEEt.PRPc.PseudoRP,MEEt.MAC).enc: key = (_ek,_mk) /\ p = _p
                                      ==> res = _c]
  =(mu (dapply (fun iv => iv :: mee_enc AES hmac_sha256 _ek _mk iv _p) dblock) (pred1 _c)).
proof.
  have->: mu1 (dapply (fun iv=> iv :: mee_enc AES hmac_sha256 _ek _mk iv _p) dblock) _c
          = mu1 (dmap dblock (fun iv=> iv :: mee_enc AES hmac_sha256 _ek _mk iv _p)) _c by move.
  rewrite dmap1E /preim /pred1 /=.
  proc; inline MAC.tag PRPc.PseudoRP.f.
  swap 6 -5 => //=; alias 2 iv = s.
  while (   0 <= i <= size (pad _p (hmac_sha256 _mk _p))
         /\ ek = _ek
         /\ p' = pad _p (hmac_sha256 _mk _p)
         /\ s  = nth witness c i
         /\ size c = 1 + i
         /\ c      = iv :: cbc_enc AES _ek iv (take i (pad _p (hmac_sha256 _mk _p))))
        (size (pad _p (hmac_sha256 _mk _p)) - i).
    auto=> /> &hr le0_i _ /addzI szcbc_eq_i lti_szpadded.
    split; last by smt ().
    split; first by smt().
    split; last first.
      split; first by rewrite size_cat /= szcbc_eq_i.
      rewrite (take_nth witness) //= -cbc_enc_rcons -cats1 /=.
      by rewrite size_take // lti_szpadded.
    have -> /=: i{hr} + 1 <> 0 by smt ().
    by rewrite cats1 nth_rcons size_cbc_enc size_take // lti_szpadded /=.
  wp=> //=.
  conseq (_: _ ==> s :: mee_enc AES hmac_sha256 _ek _mk s _p = _c)=> //=.
    move=> &m [->>] ->> iv //=; split=> [[[le0_size _] h]|<<-].
      have -> //=:= h (iv :: mee_enc AES hmac_sha256 _ek _mk iv _p)
                      (size (pad _p (hmac_sha256 _mk _p)))
                      (nth witness (iv :: mee_enc AES hmac_sha256 _ek _mk iv _p)
                                   (size (pad _p (hmac_sha256 _mk _p)))).
      split=> //=.
      split; 1:by rewrite /mee_enc /= size_cbc_enc addzC.
      by rewrite take_size.
    split=> [|c n s0]; 1:by split; [rewrite size_ge0|rewrite take0].
    split=> [[[le0_n le_n_size] [s0_is_nth [size_c]]] c_is_enc|].
      by rewrite StdOrder.IntOrder.ler_subl_addr add0z=> /StdOrder.IntOrder.ler_gtF.
    rewrite -lezNgt=> le_size_n [[le0_n le_n_size]] [_] [_] ->.
    have [_ ->] //:= eqz_leq n (size (pad _p (hmac_sha256 _mk _p))).
    by rewrite take_size.
  by rnd.
qed.

phoare mee_decrypt_correct _mk _ek _c:
  [MEEt.MEE(MEEt.PRPc.PseudoRP,MEEt.MAC).dec: key = (_ek,_mk) /\ c = _c
                                      ==> res = mee_dec AESi hmac_sha256 _ek _mk (head witness _c) (behead _c)]
  =1%r.
proof.
conseq (_: true ==> true) (_: _ ==> _)=> //=.
+ proc; inline MAC.verify PRPc.PseudoRP.fi; wp.
  while (   0 <= i <= size c
         /\ ek = _ek
         /\ s  = (if 0 < i then nth witness c (i - 1) else head witness _c)
         /\ size padded = i
         /\ padded = cbc_dec AESi _ek (head witness _c) (take i c)).
    auto=> /> &hr le0_szpadded _ h lt_padded_c.
    split; first by smt ().
    split; first by smt (size_ge0).
    split; first by rewrite size_cat.
    rewrite (take_nth witness) // -cbc_dec_rcons -h cats1.
    by rewrite size_take // lt_padded_c /= nth_take // 1:/#; congr; algebra.
  auto=> /> &hr; split.
  + by rewrite size_ge0 take0.
  move=> p /lezNgt le_szc_p _ ge_szc_p.
  rewrite (ler_asym (size p) (size (behead c{hr})) _);
    rewrite ?ge_szc_p ?le_szc_p // take_size => p_def.
  split.
  + case: {-1}(unpad p) (eq_refl (unpad p))=> //= @/mee_cbc - [] m t.
    by rewrite /mee_dec /= -p_def=> -> /=.
  by rewrite /mee_dec -p_def /= => ->.
by proc; inline *; wp; while true (size c - i); auto=> &hr /#.
qed.
