require import AllCore FSet CoreMap SmtMap List.
require import Distr DList DJoin DMap StdOrder.
require import AEAD.
require (*--*) MRPKE.
require (*--*) ODH.
(*---*) import IntOrder.

pragma -implicits.
pragma +oldip.

(* an "eval safe" version of [dlet] *)
op dlet_locked ['a, 'b] = dlet<:'a, 'b> axiomatized by dlet_lockedE.

theory DHIES.

  clone import ODH with
    op   genRange <- gen,
    type range    <- K,
    op   q_ror    <- q_lor.

  clone GP.ZModE.ZModpField as ZPF.

  type group   = ODH.G.group.
  type exp     = ODH.GP.exp.
  abbrev dt    = ODH.FD.dt.
  abbrev g     = ODH.G.g.
  abbrev ( ^ ) = ODH.GP.( ^ ).

  type CTxt  = group * Cph.
  type PTxt  = Msg.
  type Pk    = group.
  type Sk    = exp.
  type Rand  = exp.
  type MPk   = Pk fset.
  type MCTxt = (Pk, CTxt) fmap.
  type Tag   = AData.

  (* DH keypair sampling distr *)
  op genDH : (Sk * Pk) distr =
    dmap dt (fun x => (x, g ^ x)).

  (* mrDHIES up to key derivation distr *)
  op mkeyDHIES (pkl : Pk list) : (Pk * (group * K)) list distr =
    dmap dt (fun x =>
               map (fun pk => (pk, (g ^ x, hash (pk ^ x)))) pkl).

  (* DHIES symmetric encryption part distr *)
  op encDHIES tag ptxt (kk: Pk * (group * K)) :
                       (Pk * (group * Cph)) distr =
    dmap (enc kk.`2.`2 tag ptxt) (fun c => (kk.`1, (kk.`2.`1, c))).

  (* mrDHIES symmetric encryption part distr *)
  op mencDHIES tag ptxt (kks: (Pk * (group * K)) list) =
    djoinmap (encDHIES tag ptxt) kks.

  (* mrDHIES encryption (list version) *)
  op menclist pkl tag ptxt : (Pk * CTxt) list distr =
    dlet (mkeyDHIES pkl) (mencDHIES tag ptxt).

  (* mrDHIES encryption (map version) *)
  op mencrypt pks tag ptxt =
    dapply ofassoc (menclist (elems pks) tag ptxt).

  (* DHIES decryption *)
  op decrypt (sk : Sk, tag : Tag, ctxt : CTxt) : PTxt option =
    dec (hash(ctxt.`1 ^ sk)) tag ctxt.`2.

  (* mrndDHIES up to key derivation, but random independent symmetric keys *)
  op mrndkeyDHIES (pkl: Pk list) : (Pk * (group * K)) list distr =
    dlet_locked dt (fun x =>
                      dmap (dlist gen (size pkl))
                           (fun ks =>
                              amap (fun pk k =>
                                   (g ^ x, k)) (zip pkl ks))).

  lemma mencDHIES_menc pkl (kk : (Pk * (group * K)) list) tag ptxt :
    pkl = map (snd \o snd) kk =>
    menc pkl tag ptxt = dmap (mencDHIES tag ptxt kk) (List.map (snd \o snd)).
  proof.
  rewrite /mencDHIES /menc /dlistmap /zipks /encDHIES /=.
  rewrite djoin_dmap.
  move=> ->; rewrite -map_comp /(\o) /=.
  congr; congr; apply fun_ext => x.
  by rewrite dmap_comp /(\o) /= dmap_id.
  qed.

  module DHIES = {
    proc gen () : (Sk * Pk) = {
      var y, gy;

      y  <$ dt;
      gy <- g ^ y;
      return (y, gy);
    }

    proc mencrypt (mpk : MPk, tag : Tag, ptxt : PTxt) : MCTxt = {
      var cphList,scph,x,gx,pkl,i;

      x       <$ dt;
      gx      <- g ^ x;
      pkl     <- map (fun pk => (pk,(gx, hash(pk ^ x)))) (elems mpk);
      i       <- size pkl-1;
      cphList <- [];
      while (0 <= i){
        scph    <$ enc (nth witness pkl i).`2.`2 tag ptxt;
        cphList <- ((nth witness pkl i).`1, ((nth witness pkl i).`2.`1, scph)) :: cphList;
        i <- i-1;
      }

      return SmtMap.ofassoc cphList;
    }

    proc decrypt (sk : Sk, tag : Tag, ctxt : CTxt) : PTxt option = {
      var ptxt;

      ptxt <- dec (hash (ctxt.`1 ^ sk)) tag ctxt.`2;

      return ptxt;
    }
  }.

  clone import MRPKE with
    type Pk <- Pk,
    type Sk <- Sk,
    type CTxt <- CTxt,
    type PTxt <- PTxt,
    type Tag <- Tag,
    op gen <- genDH,
    op mencrypt <- mencrypt,
    op decrypt <- decrypt,
    op q_gen <- q_gen,
    op q_lor <- q_lor,
    op q_maxpks <- q_maxn,
    op q_dec <- q_dec.

(*axiom bound : q_maxpks = q_maxn /\ MRPKE.q_dec = AEAD.q_dec.*)

  (* decomposing [mencrypt] *)

  module MEnc = {
    proc mencrypt (mpk : MPk, tag : Tag, ptxt : PTxt) : MCTxt = {
      var pkl, eph, keys, cphs, cph;
      pkl  <- elems mpk;
      (* keys : (Pk * (group * K)) list *)
      eph  <$ dt;
      keys <- map (fun pk => (pk, (g ^ eph, hash (pk ^ eph)))) pkl;
      (* cphs : (Pk * (group * Cph)) *)
      cphs <$ mencDHIES tag ptxt keys;
      cph  <- SmtMap.ofassoc cphs;
      return cph;
    }
    proc mencDHIES1(tag : AData, ptxt : Msg, kks : (Pk * (group * K)) list)
                : (Pk * (group * Cph)) list = {
      var mcph;
      mcph <$ mencDHIES tag ptxt kks;
      return mcph;
    }
    proc mencDHIES2(tag : AData, ptxt : Msg, kks : (Pk * (group * K)) list)
                : (Pk * (group * Cph)) list = {
      var skeys, cs, cphl;
      skeys <- map (snd \o snd) kks;
      cs    <$ menc skeys tag ptxt;
      cphl  <- map (fun x:(_*(_*_))*_ => (x.`1.`1, (x.`1.`2.`1,x.`2))) (zip kks cs);
      return cphl;
    }
    proc mrndkeys1 (pkl : Pk list) : (Pk * (group * K)) list = {
      var keys;
      keys <$ mrndkeyDHIES(pkl);
      return keys;
    }
    proc mrndkeys2 (pkl : Pk list) : (Pk * (group * K)) list = {
      var x, ks, keys;
      x    <$ dt;
      ks   <$ dlist gen (size pkl);
      keys <- amap (fun pk k => (g ^ x, k)) (zip pkl ks);
      return keys;
    }
  }.

  clone JoinMapSampling as MEncDHIES_loop
  with type ta <- (Pk * (group * K)),
       type tb <- (Pk * (group * Cph)).

  clone JoinMapSampling as MEnc_loop
  with type ta <- K,
       type tb <- Cph.

  clone import DMapSampling as EncDHIES_map
  with type t1 <- Cph,
       type t2 <- Pk * (group * Cph).

  lemma mencDHIES_eq : equiv [MEnc.mencDHIES1 ~ MEnc.mencDHIES2: ={tag,ptxt,kks} ==> ={res}].
  proof.
  proc.
  outline {1} [1] { mcph <@ MEncDHIES_loop.S.sample(encDHIES tag ptxt, kks); }.
  rewrite equiv[{1} 1 MEncDHIES_loop.Sample_Loop_eq].
  outline {2} [2] { cs <@ MEnc_loop.S.sample(fun k => enc k tag ptxt, skeys); }.
  rewrite equiv[{2} 2 MEnc_loop.Sample_Loop_eq].
  inline*; wp.
  while ( ={i,kks,tag,ptxt} /\
           (d = encDHIES tag ptxt /\ xs = kks /\ i < size kks){1} /\
           (d = (fun k => enc k tag ptxt) /\ xs = map (snd \o snd) kks){2} /\
           l{1} = map (fun x:(_*(_*_))*_ => (x.`1.`1, (x.`1.`2.`1, x.`2)))
                      (zip (drop (i+1) kks) l){2}).
  + wp.
    outline {1} [1] { r <@ EncDHIES_map.S.sample(enc (nth witness xs i).`2.`2 tag ptxt,
                                                         fun c => ((nth witness xs i).`1,
                                                                  ((nth witness xs i).`2.`1,c))); }.
    rewrite equiv[{1} 1 EncDHIES_map.sample].
    inline*; auto=> /> &m i_le_kks i_ge_0.
    rewrite (nth_map witness witness (snd \o snd)); 1: smt().
    rewrite (drop_nth witness i{m}) /#.
  by auto=> />; smt(drop_le0 size_map).
  qed.

  clone import DProd.DLetSampling as MRnd_let
  with type t <- exp,
       type u <- (Pk * (group * K)) list.

  clone import DMapSampling as MRnd_map
  with type t1 <- K list,
       type t2 <- (Pk * (group * K)) list.

  lemma mrndkeys_def : equiv [MEnc.mrndkeys1 ~ MEnc.mrndkeys2: ={pkl} ==> ={res}].
  proof.
  proc.
  outline {2} [2-3] { keys <@ MRnd_map.S.map(
                      dlist gen (size pkl),
                      fun (ks:K list) => amap (fun pk k => (g ^ x, k))
                                              (zip pkl ks)); }.
  rewrite equiv[{2} 2 -MRnd_map.sample].
  outline {2} [1-2] { keys <@ MRnd_let.SampleDep.sample(dt,
                      fun x => dmap (dlist gen (size pkl))
                                    (fun ks => amap (fun pk k => (g ^ x, k))
                                                    (zip pkl ks))); }.
  rewrite equiv[{2} 1 MRnd_let.SampleDepDLet].
  by inline*; auto; rewrite -dlet_lockedE.
  qed.

  clone import DMapSampling as MKey_map
  with type t1 <- exp,
       type t2 <- (Pk * (group * K)) list.

  clone import DMapSampling as MEncrypt_map
  with type t1 <- (Pk * (group * Cph)) list,
       type t2 <- (Pk, group * Cph) fmap.

  clone import DProd.DLetSampling as MEncDHIES_let
  with type t <- (Pk * (group * K)) list,
       type u <- (Pk * (group * Cph)) list.

  lemma mencrypt_def1: equiv [MEnc.mencrypt ~ Scheme.mencrypt: ={mpk, tag, ptxt} ==> ={res}].
  proof.
  symmetry; proc.
  outline {1} [1] { cph <@ MEncrypt_map.S.sample(
                       dlet_locked (mkeyDHIES (elems mpk))
                       (mencDHIES tag ptxt),
                       SmtMap.ofassoc <: Pk, group * Cph> ); }.
  + by inline*; auto; rewrite dlet_lockedE.
  rewrite equiv[{1} 1 MEncrypt_map.sample].
  inline*; swap{1} 2 1.
  outline {1} [1-2] {r1 <@ MEncDHIES_let.SampleDLet.sample(mkeyDHIES (elems mpk), mencDHIES tag ptxt); }.
  + by inline*; auto; rewrite dlet_lockedE.
  rewrite equiv[{1} 1 -MEncDHIES_let.SampleDepDLet].
  inline*; swap{1} 2 1. 
  outline {1} [1-2] {t <@ MKey_map.S.sample(
                            FD.dt,
                            (fun x =>
                               map (fun pk => (pk, (g ^ x, hash (pk ^ x))))
                                   (elems mpk))); }.
  rewrite equiv[{1} 1 MKey_map.sample].
  by inline*; auto.
  qed.

  clone import DMapSampling as Enc_map
  with type t1 <- Cph,
       type t2 <- (Pk * (group * Cph)).

  (* we axiomatize operators based on the above module *)
  lemma gendef: equiv [DHIES.gen ~ Scheme.gen : true ==>  ={res}].
  proof.
  proc; wp; rnd (fun x => (x, g ^ x)) (fun (x : exp * group)=> x.` 1); skip; progress.
    by move: H; rewrite /genDH supp_dmap; move => [x [Hx ->]].
   rewrite /genDH dmap1E /(\o) /=.
   move: H0; rewrite /genDH supp_dmap; move => [x [Hx ->]] /=.
   apply mu_eq => /= y.
   by rewrite /pred1 /= eqboolP; split.
  by rewrite /genDH supp_dmap; exists yL; split.
  qed.

  lemma mencryptdef: equiv [DHIES.mencrypt ~ Scheme.mencrypt : ={mpk, tag, ptxt} ==> ={res}].
  proof.
  proc*.
  rewrite equiv[{2} 1 -mencrypt_def1].
  inline.
  outline {2} [7] { cphs <@ MEncDHIES_loop.S.sample(encDHIES tag ptxt, keys); }.
  rewrite equiv[{2} 7 MEncDHIES_loop.Sample_Loop_eq].
  inline*; wp.
  while (={mpk0,tag0,ptxt0,i} /\ pkl{1} = xs{2} /\ (d = encDHIES tag0 ptxt0){2} /\ cphList{1} = l{2}); last by auto.
  outline {2} [1] {r0 <@ Enc_map.S.sample (
                       enc (nth witness xs i).`2.`2 tag0 ptxt0,
                       fun c =>((nth witness xs i).`1, ((nth witness xs i).`2.`1, c)));}.
  rewrite equiv[{2} 1 Enc_map.sample].
  by inline*; auto.
  qed.

  lemma decryptdef: equiv [DHIES.decrypt ~ Scheme.decrypt : ={sk, tag, ctxt} ==>  ={res}].
  proof. by proc; wp; skip. qed.

(** FIRST HOP: MULTIPLE ORACLE DIFFIE HELLMAN ASSUMPTION *****)


(****** Adversary for the first hop ************)
module Adv1_Procs (ODHOrcl : ODH_OrclT) : MRPKE_OrclT = {
  include MRPKE_lor [-gen,lor,dec,init]
  var skeys : ((Pk * group),K) fmap

  proc init(b : bool) = {
     skeys <- empty;
     MRPKE_lor.init(b);
  }
  proc gen () = {
      var pk;
      pk <- witness;
      if (MRPKE_lor.count_gen < q_gen) {
         pk <@ ODH_Orcl.gen();
         if( pk \notin MRPKE_lor.pklist) {
               MRPKE_lor.pklist.[pk] <- witness;
         }
         MRPKE_lor.count_gen <- MRPKE_lor.count_gen + 1;
      }
      return pk;
  }

  proc lor (pks: MPk, tag : Tag, m0:PTxt, m1: PTxt) : MCTxt option = {
    var pkl, skeylist, keys, enclist, cph;
    var ro;

    ro <- None;

    if (MRPKE_lor.count_lor < q_lor) {
      if (pks \subset fdom MRPKE_lor.pklist /\ size (elems pks) < q_maxn) {
        pkl <- elems pks;
        keys <@ ODHOrcl.ror(pks);
        skeylist <- map (fun x:_*(_*_)=>((x.`1,x.`2.`1),x.`2.`2)) (oget keys);
        enclist <$ mencDHIES tag (if MRPKE_lor.b then m1 else m0) (oget keys);
        cph <- SmtMap.ofassoc enclist;
        skeys <- skeys + SmtMap.ofassoc skeylist;
        MRPKE_lor.lorlist <- MRPKE_lor.lorlist ++ fold_encs pks tag cph;
        ro <- Some cph;
      }
      MRPKE_lor.count_lor <- MRPKE_lor.count_lor + 1;
    }
    return ro;
  }

  proc dec (pk : Pk, tag : Tag, ctxt : CTxt) : PTxt option = {
    var msg,key,okey;
    msg <- None;
    if (MRPKE_lor.count_dec < q_dec) {
       if ((pk \in fdom MRPKE_lor.pklist) &&
        (!((pk,tag,ctxt) \in MRPKE_lor.lorlist))) {
           if ((pk,ctxt.`1) \notin skeys) {
                okey <@ ODHOrcl.hash(pk,ctxt.`1);
                key <- oget okey;
           }
           else {
                key <- oget skeys.[(pk,ctxt.`1)];
           }
           msg <- dec key tag (snd ctxt);
       }
       MRPKE_lor.count_dec <- MRPKE_lor.count_dec + 1;
    }
    return msg;
  }
}.

module Adv1(A : MRPKE_Adv, O : ODH_OrclT) = {
   module A = A(Adv1_Procs(O))

   proc guess() : bool = {
      var b,b' : bool;
      b <$ {0,1};
      Adv1_Procs(O).init(b);
      b' <@ A.guess();
      return (MRPKE_lor.b = b');
   }
}.

lemma L1 ['a,'b,'c,'d] (f: 'a->'b->('c*'d)) (s: 'a fset) (l: 'b list):
 size l = size (elems s) =>
 amap f (zip (elems s) l)
 =
 map (fun x=> (x, ((f x (nth witness l (index x (elems s)))).`1,
                   (f x (nth witness l (index x (elems s)))).`2))) (elems s).
proof.
move=> /eq_sym *.
rewrite -(@map_fst_zip _ (elems s) l) // /(\o) /=.
rewrite amap_assoc_zip //; first by apply uniq_elems.
by congr; apply: fun_ext => x /#.
qed.

lemma pkmem_foldenc pk t c pks tag mctxt:
 (pk,t,c) \in fold_encs pks tag mctxt => pk \in elems pks.
proof. by move=> /mapP [x [Hx //]]. qed.

lemma tagmem_foldenc pk t c pks tag mctxt:
 (pk,t,c) \in fold_encs pks tag mctxt => t=tag.
proof. by move=> /mapP [x [Hx //]]. qed.

lemma ctxt1mem_foldenc pk t c pks tag mctxt:
 (pk,t,c) \in fold_encs pks tag (SmtMap.ofassoc mctxt) => c.`1=(oget (assoc mctxt pk)).`1.
proof.
move=> /mapP [x [Hx //=]] [<<- [? ->]].
by rewrite SmtMap.ofassoc_get.
qed.

lemma mem_mencDHIES cphs tag ptxt kk:
 cphs \in mencDHIES tag ptxt kk =>
 amap (fun k => fst) cphs
 = amap (fun k => fst) kk.
proof.
rewrite supp_djoinmap; move=> [Hsz /allP H].
rewrite -(map_snd_zip _ kk) // -(map_fst_zip _ kk cphs) //.
apply eq_in_map; rewrite /(\o) /= => *.
by move: (H _ H0) => /=; rewrite supp_dmap; move=> [y [Hy1 /= ->]].
qed.

lemma ephmem_foldenc pk t c pks tag ptxt mctxt kk:
 (pk \in map fst kk)%List =>
 mctxt \in mencDHIES tag ptxt kk =>
 (pk,t,c) \in fold_encs pks tag (SmtMap.ofassoc mctxt) =>
 c.`1 = fst (oget (assoc kk pk)).
proof.
move=> Hin2 /mem_mencDHIES Hmap ? .
move: (Hin2); move: (eq_keys_amap _ _ _ _ Hmap) => <- Hin1.
rewrite -(Core.oget_omap_some fst (assoc kk pk)).
by apply/assocTP.
rewrite -(assoc_amap (fun pk => fst)) -Hmap assoc_amap Core.oget_omap_some /=.
 by apply assocTP.
by rewrite (ctxt1mem_foldenc _ _ _ _ _ _ H).
qed.

lemma hop1false &m
    (A <: MRPKE_Adv {-MRPKE_lor, -Adv1_Procs, -ODH_Orcl}):
       Pr [MRPKE_Sec(A).main() @ &m : res ] =
       Pr [ODH_Sec(Adv1(A)).game(false) @ &m : !res].
proof.
byequiv (_: !b{2} /\ ={glob A} ==> res{1} = !res{2}) => //.
proc; inline *.
pose inv (gPKE1 : glob MRPKE_lor) (gPKE2 : glob MRPKE_lor) (gODH2 : glob ODH_Orcl)
         (skeys2:(Pk * group, K) fmap) :=
  !gODH2.`1 /\
  gPKE1.`1=gPKE2.`1 /\ gPKE1.`2=gPKE2.`2 /\ gPKE1.`3=gPKE2.`3 /\ gPKE1.`4=gPKE2.`4 /\
  gPKE1.`5=gPKE2.`5  /\  fdom gPKE2.`6 = fdom gODH2.`4 /\ fdom skeys2 = gODH2.`5 /\
  gODH2.`3 <= gPKE1.`4 /\
  gODH2.`2 = gPKE2.`3 /\ gODH2.`4 = gPKE1.`6 /\
  (forall pk sk, gPKE1.`6.[pk] = Some sk => pk = g ^ sk) /\
  (forall pk gx k, skeys2.[(pk,gx)] = Some k => pk \in gPKE2.`6 && exists (x : exp), gx = g ^ x && k = hash(pk ^ x)) /\
  (forall pk sk, gPKE1.`6.[pk] = Some sk => pk = g ^ sk) /\
  (forall pk tag cph,
    ((pk, tag, cph) \in gPKE1.`5)%List => pk \in gPKE1.`6 && (pk, cph.`1) \in skeys2)  /\
  (forall pk sk gx k, gPKE1.`6.[pk] = Some sk => skeys2.[(pk, gx)] = Some k => k = hash(gx ^ sk)).
wp; call (_: inv (glob MRPKE_lor){1} (glob MRPKE_lor){2} (glob ODH_Orcl){2} Adv1_Procs.skeys{2}); last first.
 wp; rnd; wp; skip; rewrite /inv /=; clear inv => />; smt (fdom0 emptyE).
+ proc; inline*.
   sp; if; first by rewrite /inv.
   rcondt {2} 3; first by auto => />.
  seq 2 3: (#[/3:]pre /\ k{1}.`1=y{2} /\ k{1}.`2=gy{2} /\ (gy = g^y){2}).
   wp; rnd (fun (x:_*_) => x.`1) (fun x => (x, g^x)); skip; rewrite /inv /=; clear inv; progress.
   + rewrite /genDH dmap1E /(\o) /pred1 /=.
     by apply mu_eq => /= x /#.
   + by move: H9; rewrite /genDH supp_dmap; move => [x [Hx ->]] /=.
   by move: H9; rewrite /genDH supp_dmap; move => [x [Hx ->]] /=.
  if; first by rewrite /inv.
  + by wp; skip; rewrite /inv /=; clear inv => />; smt (fdom_set get_setE mem_fdom).
    by wp; skip; rewrite /inv /=; clear inv => />; smt (fdom_set get_setE mem_fdom).
  by skip.
+ proc.
  sp; if; 1: (by rewrite /inv; progress; smt()); 2: (by wp;skip;progress;smt()).
  if => //=.
  + by move=> /> /#.
  wp; rewrite equiv[{1} 1 -mencrypt_def1].
  + inline*; wp; rnd; wp.
    rnd{2}; rnd; wp; skip; rewrite /inv /=; clear inv; progress; last 18 by smt().
    + by apply dlist_ll; apply AEAD.gen_ll.
    + move: H15; rewrite !H /=.
      rewrite (L1 (fun k v => (g^ephL, hash(k^ephL))) pks{2} keys00) //.
      by apply/(supp_dlist_size _ _ _ _ H12)/size_ge0.
    + move: H15; rewrite !H /= (L1 (fun k v => (g^ephL, hash(k^ephL))) pks{2} keys00) //.
      by apply/(supp_dlist_size _ _ _ _ H12)/size_ge0.
    + move: H15 H16; rewrite !H /= (L1 (fun k v => (g^ephL, hash(k^ephL))) pks{2} keys00) //=.
       by apply/(supp_dlist_size _ _ _ _ H12)/size_ge0.
      move=> ? ?.
      rewrite -map_comp /(\o) /= fdom_join; congr.
      by rewrite fdom_ofassoc -map_comp /(\o) /= .
    + smt().
    + move: H16 H17 H18; rewrite !H /=.
      rewrite (L1 (fun k v => (g^ephL, hash(k^ephL))) pks{2} keys00) //.
       by apply/(supp_dlist_size _ _ _ _ H12)/size_ge0.
      move=> /= ? ?.
      rewrite joinE; pose E := (_ \in _)%SmtMap; case: E; rewrite /E; clear E; last smt().
      rewrite -map_comp /(\o) /= ofassoc_get mem_ofassoc -map_comp /(\o) /=.
      move=> /mapP [pk' [Hpk' /= [-> ->]]] _; smt (mem_fdom memE).
    + move: H16 H17 H18; rewrite !H /=.
      rewrite (L1 (fun k v => (g^ephL, hash(k^ephL))) pks{2} keys00) //.
       by apply/(supp_dlist_size _ _ _ _ H12)/size_ge0.
      move=> /= ? ?.
      rewrite joinE; pose E := (_ \in _)%SmtMap; case: E; rewrite /E; clear E; last smt().
      rewrite -map_comp /(\o) /= ofassoc_get.
      move => ? ?; exists ephL.
      move: (assoc_some _ _ _ H20) => /mapP [v [? /= [[? ?] ?]]]; smt().
    + move: H16 H17; rewrite !H /=.
      rewrite (L1 (fun k v => (g^ephL, hash(k^ephL))) pks{2} keys00) //.
       by apply/(supp_dlist_size _ _ _ _ H12)/size_ge0.
      move=> /= ? ?; move: H18; rewrite mem_cat; move=> [?|]; first smt().
      move=> /pkmem_foldenc; smt (mem_fdom memE).
    + move: H16 H17; rewrite !H /=.
      rewrite (L1 (fun k v => (g^ephL, hash(k^ephL))) pks{2} keys00) //.
       by apply/(supp_dlist_size _ _ _ _ H12)/size_ge0.
      move=> /= ? ?; move: H18; rewrite mem_cat mem_join; move=> [?|?]; first left; smt().
      right; rewrite mem_ofassoc -!map_comp /(\o) /=; apply/mapP; exists pk; split.
      + move: H18; rewrite /fold_encs; elim: (elems pks{2})=> // pk0 pks ih.
        by case: (pk = pk0)=> />.
      have T: pk \in map fst (map (fun x => (x, (g^ephL, hash(x^ephL)))) (elems pks{2})).
      + rewrite -map_comp /(\o) map_id.
        move: H18; rewrite /fold_encs; elim: (elems pks{2})=> // pk0 pks ih.
        by case: (pk = pk0)=> />.
      rewrite (ephmem_foldenc _ _ _ _ _ _ _ _ T H17 H18) /=.
      have ? : 0 <= index pk (elems pks{2}) < size (elems pks{2}).
      + smt(index_ge0 index_mem map_comp mapP).
      rewrite /assoc onth_nth_map -!map_comp /(\o) /= map_id
              (nth_map witness) //=.
    + move: H16 H17 H19; rewrite !H /= (L1 (fun k v => (g^ephL, hash(k^ephL))) pks{2} keys00) //.
       by apply/(supp_dlist_size _ _ _ _ H12)/size_ge0.
      move=> /= ? ?.
      rewrite joinE; pose E := (_ \in _)%SmtMap; case: E; rewrite /E; clear E; last smt().
      rewrite -map_comp /(\o) /= ofassoc_get => ? ?.
      move: (assoc_some _ _ _ H20) => /mapP [v [? /= [[? ?] ?]]].
      rewrite H24 H23 -H22.
      move: (H4 _ _ H18) => ->; congr.
      by rewrite -!GP.expM ZPF.mulrC.
  by wp; skip; rewrite /inv /=; clear inv => />; smt().
+ proc; inline*.
  sp 1 1 ; if; first by rewrite /inv.
   if;first by move=> /> ??? ->.
    case (((pk,ctxt.`1) \in Adv1_Procs.skeys){2}).
     rcondf {2} 1; first by auto => />.
     wp; skip; rewrite /inv /=; clear inv => /> *.
     rewrite /decrypt; congr.
     move: (eq_refl (MRPKE_lor.pklist{1}.[pk{2}])); case: {2}(MRPKE_lor.pklist{1}.[pk{2}]).
      by smt(mem_fdom).
     move=> sk Hpk; rewrite Hpk /=; smt (mem_fdom).
    rcondt {2} 1; first by auto => />.
    rcondt {2} 4.
     move => *;wp;skip; rewrite /inv /=; smt (mem_fdom).
    by wp; skip; rewrite /inv.
   by wp; skip; rewrite /inv.
  by skip.
qed.

module MRPKErnd_lor = {

  include MRPKE_lor [-init,lor,dec]

  var skeys : ((Pk * group),K) fmap

  proc init(b : bool) = {
     MRPKE_lor.init(b);
     skeys <- empty;
  }

  proc lor (pks: MPk, tag : Tag, m0:PTxt, m1: PTxt) : MCTxt option = {
    var keys, enclist, cph;
    var ro;

    ro <- None;

    if (MRPKE_lor.count_lor < q_lor) {
      if (pks \subset fdom MRPKE_lor.pklist  /\ size (elems pks) < q_maxn) {
        keys <$ mrndkeyDHIES (elems pks);
        enclist <$ mencDHIES tag (if MRPKE_lor.b then m1 else m0) keys;
        cph <- SmtMap.ofassoc enclist;
        skeys <- skeys + SmtMap.ofassoc (map (fun x:_*(_*_) => ((x.`1,x.`2.`1),x.`2.`2)) keys);
        MRPKE_lor.lorlist <- MRPKE_lor.lorlist ++ fold_encs pks tag cph;
        ro <- Some cph;
       }
       MRPKE_lor.count_lor <- MRPKE_lor.count_lor + 1;
    }
    return ro;
  }

  proc dec (pk : Pk, tag : Tag, ctxt : CTxt) : PTxt option = {
    var r, key;
    r <- None;
    if (MRPKE_lor.count_dec < q_dec) {
       if (pk \in fdom MRPKE_lor.pklist && !(pk,tag,ctxt) \in MRPKE_lor.lorlist) {
          if ( (pk, ctxt.`1) \in skeys )
            key <- oget skeys.[(pk, ctxt.`1)];
          else
            key <- hash (ctxt.`1 ^ (oget MRPKE_lor.pklist.[pk]));
          r <- dec key tag ctxt.`2;
       }
       MRPKE_lor.count_dec <- MRPKE_lor.count_dec + 1;
    }
    return r;
  }
}.

module MRPKErnd_Sec (A:MRPKE_Adv) = {
  proc game(b : bool) = {
    var b';
    MRPKErnd_lor.init(b);
    b' <@ A(MRPKErnd_lor).guess ();
    return (b'=b);
  }

  proc main() = {
    var b,b';
    b <$ {0,1};
    b'<@ game(b);
    return b';
  }
}.

lemma hop1true &m
    (A <: MRPKE_Adv {-MRPKErnd_lor, -Adv1_Procs, -ODH_Orcl}):
       Pr [MRPKErnd_Sec(A).main() @ &m : res ] =
       Pr [ODH_Sec(Adv1(A)).game(true) @ &m : res].
proof.
byequiv (_: b{2} /\ ={glob A} ==> res{1} = res{2}) => //.
proc; inline *.
pose inv (gPKE1:glob MRPKErnd_lor) (gPKE2:glob MRPKE_lor) (gODH2:glob ODH_Orcl)
         (skeys2:(Pk*group,K) fmap) :=
  gODH2.`1 /\ gPKE1.`2=gPKE2.`1 /\ gPKE1.`3=gPKE2.`2 /\ gPKE1.`5=gPKE2.`4 /\ gPKE1.`4=gPKE2.`3 /\
  gPKE1.`6=gPKE2.`5 /\ fdom gPKE2.`6 = fdom gODH2.`4 /\ gODH2.`3 <= gPKE1.`5 /\
  gODH2.`2 = gPKE2.`3 /\ gODH2.`4 = gPKE1.`7 /\ gPKE1.`1 = skeys2 /\ gODH2.`5 = fdom skeys2 /\
  (forall pk cph tag, ((pk,cph,tag) \in gPKE1.`6)%List => pk \in gPKE1.`7) /\
  (forall pk tag (ctxt : CTxt), (pk, tag, ctxt) \in gPKE1.`6 => (pk,ctxt.`1) \in skeys2).
wp; call (_: inv (glob MRPKErnd_lor){1} (glob MRPKE_lor){2} (glob ODH_Orcl){2} Adv1_Procs.skeys{2});
 last by wp; rnd; wp; skip => /> *; smt(fdom0).
+ proc;inline*.
  sp; if; first by rewrite /inv.
   rcondt {2} 3; first by auto => />.
   seq 2 3: (#[/3:]pre /\ k.`1{1}=y{2} /\ k.`2{1}=gy{2}).
    wp; rnd (fun (x:_*_) => x.`1) (fun x => (x, g^x)); skip; rewrite /inv /=; clear inv; progress.
    + rewrite /genDH dmap1E /(\o) /pred1 /=.
      by apply mu_eq => /= x /#.
    + by move: H6; rewrite /genDH supp_dmap; move => [x [Hx ->]].
    + by move: H6; rewrite /genDH supp_dmap; move => [x [Hx ->]].
   if; first by rewrite /inv.
    wp; skip; rewrite /inv => />; smt (fdom_set mem_fdom in_fsetU).
   by wp; skip; rewrite /inv => />; smt (fdom_set mem_fdom in_fsetU).
  by skip; rewrite /inv.
+ proc.
  sp; if; 1: (by rewrite /inv; progress; smt()); 2: (by wp;skip;progress;smt()).
  if => //=; 1: by smt ().
  inline *.
  rcondt {2} 9; 1: by move => *;wp;rnd;rnd;wp;rewrite /inv /=; clear inv;wp;skip => />; smt().
  rcondt {2} 9; 1: by move => *;wp;rnd;rnd;wp;rewrite /inv /=; clear inv;wp;skip => />; smt().
  swap{2} 10 1.
  seq 1 10 : (#pre /\ keys{1} = hs{2} /\ (map fst hs = elems pks){2} /\
              (gygxlist = amap (fun pk (x:_*_) => x.`1) hs){2}).
   outline {1} [1] { keys <@ MEnc.mrndkeys1(elems pks); }.
   rewrite equiv[{1} 1 mrndkeys_def].
   + inline*; wp; rnd; rnd; wp; skip; rewrite /inv /=; clear inv; progress.
       by rewrite H.
      rewrite H -map_comp /(\o) /= unzip1_zip //.
      by rewrite (supp_dlist_size _ _ _ _ H9) ?size_ge0.
     rewrite -map_comp /(\o) H /=.
     by rewrite -(map_fst_zip _ _ ksL) // (supp_dlist_size _ _ _ _ H9) ?size_ge0.
  wp; rnd; wp; skip; rewrite /inv /=; clear inv; progress.
  + by smt().
  + by rewrite fdom_join fdom_ofassoc -map_comp /(\o).
  + move: H10; rewrite mem_cat; move=> [?|]; first smt().
    move=> /pkmem_foldenc; smt (memE mem_fdom).
  + move: H10; rewrite mem_cat mem_join; move=> [?|?]; first smt().
    right; rewrite mem_ofassoc -!map_comp /(\o) /=.
    have T: pk \in map fst hs{2}.
    + rewrite H7; move: H10=> @/fold_encs.
      by elim: (elems pks{2})=> /> pk0 pks ih; case: (pk = pk0).
    rewrite (ephmem_foldenc _ _ _ _ _ _ _ _ T H9 H10) /=.
    have ?: uniq (map fst hs{2}).
    + by rewrite H7 uniq_elems.
    apply/mapP => /=.
    exists (pk,oget (assoc hs{2} pk)) => //=.
    by apply assoc_get_mem.
  by wp; skip; rewrite /inv /=; smt().
+ proc; inline*.
  sp 1 1 ; if; first by rewrite /inv /=; clear inv; progress.
   if; first by  progress;smt ().
    case (((pk,ctxt.`1) \in Adv1_Procs.skeys){2}).
     rcondf {2} 1; first by auto => />.
     by wp; skip; rewrite /inv.
    rcondt {2} 1; first by auto => />.
    rcondt {2} 4; 1: by move => *;wp;skip;rewrite /inv /=; smt (mem_fdom).
   by wp; skip; rewrite /inv.
   by wp; skip; rewrite /inv.
  by skip.
qed.

(****** Reduction to TAGGED CCA SECURITY OF AEAD ************)

module Adv2_Procs (AEADmul_Orcl : AEADmul_OraclesT) : MRPKE_OrclT = {
  include MRPKErnd_lor [-init, lor, dec]

  var kindex : ((Pk * Pk), int) fmap

  proc init() = {
     MRPKE_lor.pklist    <- empty;
     MRPKE_lor.lorlist   <- [];
     MRPKE_lor.count_gen <- 0;
     MRPKE_lor.count_lor <- 0;
     MRPKE_lor.count_dec <- 0;
     MRPKErnd_lor.skeys  <- empty;
     kindex              <- empty;
  }

  proc lor (pks: MPk, tag : Tag, m0:PTxt, m1: PTxt) : MCTxt option = {
    var ro, pkl, x, gx, aeadcph;

    ro <- None;

    if (MRPKE_lor.count_lor < q_lor) {
      if (pks \subset fdom MRPKE_lor.pklist /\ size (elems pks) < q_maxn) {
        pkl <- elems pks;
        x <$ dt;
        gx  <- g ^ x;
        aeadcph <@ AEADmul_Orcl.lor(size (elems pks),tag,m0,m1);
        if (aeadcph <> None) {
          (* (pk, gx), kidx *)
          kindex <- kindex + SmtMap.ofassoc (zip (map (fun pk => (pk, gx)) (elems pks))
                                             (map fst (oget aeadcph)));
          ro <- Some (SmtMap.ofassoc (zip (elems pks)
                                      ((map (fun cph => (gx,snd cph)) (oget aeadcph)))));
          MRPKErnd_lor.skeys <- MRPKErnd_lor.skeys +
            SmtMap.ofassoc (map (fun pk => ((pk, gx),witness)) (elems pks));
        }
        MRPKE_lor.lorlist <- MRPKE_lor.lorlist ++ (fold_encs pks tag (oget ro));
      }
      MRPKE_lor.count_lor <- MRPKE_lor.count_lor + 1;
    }
    return ro;
  }

  proc dec (pk : Pk, tag : Tag, ctxt : CTxt) : PTxt option = {
    var msg,key,keyidx;
    msg <- None;
    if (MRPKE_lor.count_dec < q_dec) {
       if ((pk \in fdom MRPKE_lor.pklist)&&
           (!((pk,tag,ctxt) \in MRPKE_lor.lorlist))) {
              if ((pk,ctxt.`1) \in MRPKErnd_lor.skeys) {
                   keyidx <- oget kindex.[(pk,ctxt.`1)];
                   msg <@ AEADmul_Orcl.dec(keyidx,tag,snd ctxt);
              }
              else {
                   key <- hash ((fst ctxt) ^ (oget MRPKE_lor.pklist.[pk]));
                   msg <- dec key tag (snd ctxt);
              }
      }
      MRPKE_lor.count_dec <- MRPKE_lor.count_dec + 1;
    }
    return msg;
  }
}.

module Adv2(A : MRPKE_Adv, O : AEADmul_OraclesT) = {
   module A = A(Adv2_Procs(O))

   proc guess() : bool = {
      var b' : bool;
      Adv2_Procs(O).init();
      b' <@ A.guess();
      return b';
   }
}.

lemma mem_fold_encs pk tag x pks l:
 pk \in elems pks =>
 assoc (zip (elems pks) l) pk = Some x =>
 (pk, tag, x) \in fold_encs pks tag (SmtMap.ofassoc (zip (elems pks) l)).
proof.
rewrite /fold_encs => ? ?.
have ->: (pk,tag,x)
         = (fun pk => (pk, tag, oget (SmtMap.ofassoc (zip (elems pks) l)).[pk])) pk.
 by rewrite /= ofassoc_get H0.
rewrite mem_map // => a b; smt().
qed.

lemma map_iota ['a, 'b] d (f: 'a -> 'b) (l: 'a list):
 map f l = map (fun k=> f (nth d l k)) (iota_ 0 (size l)).
proof.
elim: l => //=.
 by rewrite iota0.
move=> x xs IH /=.
move: (size_ge0 xs) => ?.
rewrite iota_add //= map_cat iota1 /= IH.
have E: 1 = 1 + 0 by smt().
rewrite {2}E iota_addl -map_comp /(\o) /=.
apply eq_in_map => y /mem_iota [? ?] /#.
qed.

lemma hop2 &m
    (A <: MRPKE_Adv { -Adv2_Procs, -MRPKErnd_lor, -AEADmul_Oracles }):
       Pr [MRPKErnd_Sec(A).main() @ &m : res ] =
       Pr [AEADmul_Sec(Adv2(A)).main() @ &m : res].
proof.
byequiv; first proc; inline *.
seq 5 1 : (#pre /\ b{1} = MRPKE_lor.b{1} /\ b0{1} = b{1} /\
           MRPKE_lor.b{1} = AEADmul_Oracles.b{2});
           first by wp;rnd;skip.
pose inv (gPKE1:glob MRPKErnd_lor) (gAdv2:glob Adv2_Procs) (gAEAD2:glob AEADmul_Oracles) :=
         gPKE1.`2 = gAEAD2.`1 /\ gPKE1.`3 = gAdv2.`3 /\ gPKE1.`4 = gAdv2.`4 /\
         gPKE1.`5 = gAdv2.`5 /\ gPKE1.`6 = gAdv2.`6 /\ gPKE1.`7 = gAdv2.`7 /\
         fdom gPKE1.`1 = fdom gAdv2.`2 /\ gAEAD2.`2 <= gAdv2.`3 /\ gAEAD2.`4 <= gAdv2.`5 /\
         fdom gAdv2.`1 = fdom gAdv2.`2 /\ size gAEAD2.`3 = gAEAD2.`6 /\
         (forall i tag cph,
             (i, tag, cph) \in gAEAD2.`5 =>
             0 <= i < gAEAD2.`6) /\
         (forall pk eph i,
             gAdv2.`1.[(pk,eph)] = Some i =>
             0 <= i < gAEAD2.`6) /\
         (forall pk eph i tag c,
             gAdv2.`1.[(pk,eph)] = Some i =>
             (i, tag, c) \in gAEAD2.`5 =>
             (pk, tag, (eph,c)) \in gAdv2.`6) /\
         (forall pk eph i,
             gAdv2.`1.[(pk,eph)] = Some i =>
             gPKE1.`1.[(pk,eph)] = Some (nth witness gAEAD2.`3 i)).
wp; call (_: inv (glob MRPKErnd_lor){1} (glob Adv2_Procs){2} (glob AEADmul_Oracles){2});
last by wp; skip; rewrite /inv /= => />; smt (fdom0 emptyE).
+ proc;inline *.
  seq 1 1 : (#pre /\ ={pk}); first by auto => />.
  if => //; first by rewrite /inv /=.
  seq 2 2 : (#pre /\ ={k}); first by auto => />.
  if => //; first (by rewrite /inv /=).
   by wp; skip; rewrite /inv /=; clear inv => />.
  by wp; skip; rewrite /inv /=; clear inv => />.
+ proc.
  seq 1 1 : (#pre /\ ={ro}); first by auto => />.
  if => //; first by rewrite /inv /= => />.
  if; 1: (by rewrite /inv /=; clear inv);
      2: (by wp; skip; rewrite /inv => />; smt()).
  inline *.
  rcondt {2} 9; 1: by move=>*; wp; rnd; wp; skip; rewrite /inv /= => />; smt(size_ge0).
  rcondt {2} 18; first by auto => />.
  simplify; swap{2} 12 1; swap{2} [8..10] 2; swap{2} 3 6; swap{2} [4..6] 1.
  seq 1 4 : (#pre /\ keys{1} = (zip (elems pks) (map (fun k=>(g^x,k)) new_keys)){2} /\
              (n = size (elems pks) /\ n = size new_keys){2}).
   outline {1} [1] { keys <@ MEnc.mrndkeys1(elems pks); }.
   rewrite equiv[{1} 1 mrndkeys_def].
   + inline*; wp; rnd; wp; rnd; wp; skip; rewrite /inv /=; clear inv; progress.
           by rewrite zip_mapr.
     smt (supp_dlist_size size_ge0).
  seq 1 4: (#pre /\ enclist{1} = (zip (elems pks) (map (fun k=>(g^x,k)) lctxt)){2} /\
            (size lctxt = size (elems pks) /\ aad = tag){2}).
   outline {1} [1] { enclist <@ MEnc.mencDHIES1(tag,if MRPKE_lor.b then m1 else m0,keys); }.
   rewrite equiv[{1} 1 mencDHIES_eq].
   + inline*; wp; rnd; wp; skip; rewrite /inv /=; clear inv; progress.
     - apply eq_distr; congr.
       rewrite (map_comp snd snd) unzip2_zip; first smt (size_map).
       by rewrite -map_comp /(\o) map_id.
     - by move: H12; rewrite zip_mapr -map_comp /(\o)/= unzip2_zip /#.
     - rewrite !zip_mapr !(map_zip_nth witness witness) /= 1,3:/#.
          rewrite size_map size_iota H10.
           move : H12; rewrite /menc. smt(size_ge0 supp_djoinmap).
          rewrite H10.
           move : H12; rewrite /menc. smt(size_ge0 supp_djoinmap).
       rewrite size_map /range /= size_iota ler_maxr 1:size_ge0.
       apply eq_in_map => y /mem_iota /= [? ?] /=.
       by rewrite (nth_map witness) /= 1:#smt:(size_iota) nth_iota.
     - rewrite H10.
           move : H12; rewrite /menc. smt(size_ge0 supp_djoinmap).
  wp; skip; rewrite /inv /=; clear inv; progress.
  + rewrite /=; congr; congr.
    have ->: (fun (cph : int * Cph) => (g ^ x{2}, cph.`2))
             = (fun k=>(g^x{2}, k)) \o snd by done.
    rewrite map_comp unzip2_zip //.
    rewrite size_iota. smt (size_ge0).
  + congr; congr.
    rewrite /=; congr; congr.
    have ->: (fun (cph : int * Cph) => (g ^ x{2}, cph.`2))
             = (fun k=>(g^x{2}, k)) \o snd by done.
    rewrite map_comp unzip2_zip //.
    rewrite size_iota. smt (size_ge0).
  + rewrite !fdom_join H !fdom_ofassoc; congr; congr.
    rewrite -!map_comp /(\o) /=.
    apply eq_sym; rewrite -(map_fst_zip _ _ (map (fun (k : K) => (g ^ x{2}, k)) new_keys{2})) //;
    first by rewrite size_map.
    by rewrite !zip_mapr -!map_comp /(\o) /=.
  + smt().
  + rewrite !fdom_join !fdom_ofassoc; congr; congr.
    rewrite -!map_comp /(\o) /= unzip1_zip //.
    rewrite !size_map size_zip size_iota. smt (size_ge0).
  + smt (size_cat).
  + move: H12; rewrite mem_cat; move=> [? /#|].
    move=> /mapP [[y1 y2] /=] /> /mem_zip_fst; smt (size_ge0 mem_iota).
  + move: H12; rewrite mem_cat; move=> [?|]. smt (size_ge0).
    move=> /mapP [[y1 y2] /=] /> /mem_zip_fst; smt (size_ge0 mem_iota).
  + move: H12; rewrite /= joinE.
    pose E:= ((pk, eph) \in _)%SmtMap; case: E => ?; last smt().
    rewrite ofassoc_get assoc_zip unzip1_zip; first 3 smt (size_map size_iota size_ge0).
    move=> ?; move: (onth_some_mem _ _ _ H13); smt (size_ge0 mem_iota).
  + move: H12; rewrite joinE.
    pose E:= ((pk, eph) \in _)%SmtMap; case: E => ?; last smt(size_ge0).
    rewrite ofassoc_get assoc_zip unzip1_zip; first 3 smt (size_map size_iota size_ge0).
    move=> ?; move: (onth_some_mem _ _ _ H14). smt (size_ge0 mem_iota).
  + move: H12; rewrite /= joinE mem_cat.
    pose E:= ((pk, eph) \in _)%SmtMap; case: E => ? ?; last first.
     have T: (i, tag0, c) \in AEADmul_Oracles.lorlist{2}.
      move: H13; rewrite mem_cat; move=> [? /#|?].
      move: H13 => /mapP [[iy cy] /= [?]]; progress.
      move: (H4 _ _ _ H14).
      move: (mem_zip_fst _ _ _ H13); smt (mem_iota).
     by left; apply (H5 pk eph i tag0 c).
    right.
    move: H14; rewrite ofassoc_get unzip1_zip; 1: smt (size_iota size_ge0).
    move/assoc_some_onth_mem => [idx] /onth_zip_some [] /onth_map_some [pk']; progress.
    have Hidx: (index pk' (elems pks{2})) = idx by smt (onth_some index_uniq uniq_elems).
    move:H15=> /onth_iota_some; progress.
    move: H13; rewrite mem_cat; move=> [? /#|].
    move=> /mapP [[i' c'] /=] [] /onth_mem [idx'] /onth_zip_some /= [] /onth_iota_some; progress.
    have Hidx': idx = idx' by smt().
    apply mem_fold_encs. apply: onth_some_mem H14.
    rewrite assoc_zip. smt (size_map size_zip size_iota size_ge0).
    apply/onth_map_some; exists (size AEADmul_Oracles.keys{2} + idx', c')=> /=.
    apply onth_zip_some => /=; split; last smt().
    apply/onth_iota_some; smt().
  + move: H12; rewrite /= !joinE => ?.
    pose L:= map _ (zip _ _).
    have ->: L = zip (map (fun pk=>(pk,g^x{2})) (elems (pks{2}))) new_keys{2}.
     rewrite /L -zip_map_proj /(\o) /=; congr.
      rewrite (map_zip_nth witness witness) 1:size_map 1:// eq_sym (map_iota witness).
      apply eq_in_map => /= k Hk.
      rewrite (nth_map witness); smt (mem_iota size_ge0).
     rewrite (map_comp snd snd) unzip2_zip 1:size_map 1:/#.
     by rewrite -map_comp /(\o) /= map_id.
    move: H12; pose E:= ((pk, eph) \in _)%SmtMap; case: E => ? ?; last first.
     pose E':= ((pk, eph) \in _)%SmtMap; case: E' => ?; last first.
      rewrite (H6 pk eph i) //; smt (nth_cat).
     move: H12 H14; rewrite /E /E' !mem_ofassoc !unzip1_zip;
       smt (size_iota size_ge0 size_map).
    pose E':= ((pk, eph) \in _)%SmtMap; case: E' => ?; last first.
     move: H12 H14; rewrite /E /E' !mem_ofassoc !unzip1_zip; smt (size_iota size_ge0 size_map).
    move: H13; rewrite !ofassoc_get.
    move=> /assoc_some_onth_mem => [[idx]] /onth_zip_some /= [].
    move=> /onth_map_some => [[pk']]; progress.
    move: H15 => /onth_map_some [[i' c']]; progress.
    move: H15 => /onth_zip_some [] /onth_iota_some; progress.
    rewrite assoc_zip 1:#smt:(size_map) (onth_nth witness).
    + smt (index_map onth_some index_uniq uniq_elems).
    congr.
    rewrite nth_cat.
    have -> /=: !(size AEADmul_Oracles.keys{2} + idx < size AEADmul_Oracles.keys{2}) by smt().
    congr.
    rewrite (index_map (fun (pk : Pk) => (pk, g ^ x{2}))) 1:/#.
    smt (index_map onth_some index_uniq uniq_elems).
+ proc.
  seq 1 1 : (#pre /\ r{1} = msg{2}); first by auto => />.
  if=> //; first by rewrite /inv.
  if=> //; first by rewrite /inv.
   if=> //; 1: by rewrite /inv /= => /> *; smt (mem_fdom).
    inline *.
    rcondt {2} 6.
     move=> *; wp; skip; rewrite /inv => /> *.
     (have: exists i, Adv2_Procs.kindex{hr}.[(pk{m0}, ctxt{m0}.`1)] = Some i by smt (mem_fdom));
     smt ().
    wp; skip; rewrite /inv /=; clear inv; progress;
    (have: exists i, Adv2_Procs.kindex{2}.[(pk{2}, ctxt{2}.`1)] = Some i by smt (mem_fdom)); smt ().
   wp; skip; rewrite /inv /= /#.
  wp; skip; rewrite /inv /#.
+ by auto => />.
+ by auto => />.
qed.

lemma reduction &m
  (A <: MRPKE_Adv {  -Adv2_Procs, -Adv1_Procs, -ODH_Orcl, -MRPKE_lor, -AEADmul_Oracles, -MRPKErnd_lor }):
     Pr [MRPKE_Sec(A).main() @ &m : res ] <=
     `| Pr[ODH_Sec(Adv1(A)).game(false) @ &m : !res] -
        Pr[ODH_Sec(Adv1(A)).game(true) @ &m : res] | +
     Pr [AEADmul_Sec(Adv2(A)).main() @ &m : res].
proof.
rewrite (hop1false &m A).
rewrite -(hop1true &m A).
rewrite (hop2 &m A).
by smt ().
qed.
