cnst eta : int.
cnst pk_size : int.

type pk_type = bitstring{pk_size}.

op [||] : (bitstring{eta}, bitstring{pk_size}) -> bitstring{eta + pk_size} 
as append_bs.

type bs_eta_pk = bitstring{eta} * pk_type.

op split_bs : bitstring{eta + pk_size} -> bs_eta_pk.

(* Certificate autority (CA) *)

(* Digital signature *)
type ds_random.
pop sample_ds: int -> ds_random.
type ds_pk. (* public key *)
type ds_sk. (* private key *)
type ds_k = ds_pk * ds_sk.
type certificate. (* the result of the signature *)

type kg_random.
pop sample_kg : int -> kg_random.
op kg : kg_random -> ds_pk * ds_sk.
op sig : (ds_random, ds_sk, pk_type) -> certificate.
op verify : (ds_pk, pk_type, certificate) -> bool.

(* Trusted Platform Module (TPM) *)

(* Asymmetric encryption *)
(* To encode asymmetric encryption and decryption, I use operators.
   Since the encryption is probabilistic, I parametrize the encryption
   by a element of type ae_random. I also declare a probabilistic operator
   "sample_ae" returning a distribution of element in ae_random. 
    No assumption is done on this probabilistic operators. *)

type ae_random. (* The type of the random element needed by the encryption *)
pop sample_ae: int -> ae_random.

type ae_pk. (* public key *)
type ae_sk. (* secret key *)
type ae_k = ae_pk * ae_sk.
type cipher. (* the result of the encryption *)

(* This operator is in fact a predicate ensuring that the pair of keys 
 is a valid pair for the encryption, decription. *)
op check_aekey : (ae_pk, ae_sk) -> bool.

type message = bitstring{eta + pk_size}.
op a_enc : (ae_random, ae_pk, message) -> cipher.
op a_dec : (ae_sk, cipher) -> message.

axiom a_enc_DEC : forall (r:ae_random, epk:ae_pk, esk:ae_sk, m:message),
   check_aekey(epk,esk) => a_dec(esk, a_enc(r,epk, m)) = m.

type akg_random.
pop sample_akg : int -> akg_random.
op a_kg : akg_random -> ae_pk * ae_sk.

axiom check_a_kg : 
  forall (r:akg_random),
    check_aekey(fst(a_kg(r)), snd(a_kg(r))).

(* Remark it could be great to allow to define probabilistic operators,
   which range in some properties:
pop a_kg : { p : ae_pk * ae_sk | 
                check_aekey(fst(p), snd(p)) }.
   In other word to allows refinement type, as in F7.
This will certainly simplify the definition of the games.
In particular it will allows to remove the declaration of akg_random, sample_akg
and allows to replace the sequence:
   r = sample_akg;
   (pk,sk) = a_kg(r);
   directly by
   (pk,sk) = a_kg;
Which clarify the code
*)

(* Symmetric encryption *)

type se_key = bitstring{eta}.
type scipher. (* the result of the symmetric encryption *)

pop s_kg :  unit -> se_key. 
type s_random.
pop sample_s : unit -> s_random.
op s_enc : (s_random, se_key, certificate) -> scipher.
op s_dec : (se_key, scipher) -> certificate.

cnst p_ca  : int. (* bound the number of CA oracles *)
cnst p_tpm : int. (* bound the number of TPM oracles *)

axiom p_ca_pos :  0 < p_ca .

type CAid = int.
type SessionId = int.

type challenge = ae_pk * ds_pk * pk_type * certificate.

(* The adversary  *)
adversary A1 (capks:(CAid,ds_pk) map, tmppks:ae_pk list) : 
     (CAid, ae_pk list) map * (ae_pk, pk_type list) map {}.

adversary A2 () : challenge 
    {
      (* TPM oracles: identified by ae_pk *)
      (SessionId, ae_pk, pk_type) -> unit; (* 1 *)
      (SessionId, cipher) -> bitstring{eta} option; (* 2 and 3 *)

      (* CA oracles: identified by ds_pk *)
      (SessionId, CAid, ae_pk, pk_type) -> cipher option; (* 1 *)
      (SessionId, bitstring{eta}) -> (scipher * cipher) option; (* 2 *)

      (* Corruption oracle *)
      CAid -> ds_sk option
    }.

op test_reg : 
  ((ds_pk * (pk_type * certificate)), 
  (ae_pk * (ds_pk * (pk_type * certificate))) list) -> bool.

(* axiom a_dom_spec : forall (m:(ae_pk, ae_sk) map, epk:ae_pk).
   { in_dom(epk,m) == in(epk,a_dom(m)) }. *)

(* The experiment on figure 4 *)

game PCAS = {

  (* TPM oracles *)
  (* The public and secret asymetric encryption keys of the TPMs *)
  var AEKey : (ae_pk, ae_sk) map

  (* ValidKey represent the short term key knows by the the TPM *)
  (* A pk can not be in two different list i.e:
      forall pk, pk in ValidKey[i] => pk in ValidKey[j] => i = j *)
  
  var ValidKey : (ae_pk, pk_type list) map
  
  var TPMSession : (SessionId, (ae_pk * pk_type)) map

  (* This is the initialisation sequence of the TMP,
     the TPM check that it known the key pk.
     Furthermore it check that the session identifier is fresh,
     if it is the case then pk will be associate to  
  *)
     
  fun TPM_1 (sid : int, epk : ae_pk, pk : pk_type) : unit = {
    if (!in_dom(sid, TPMSession) && (* sid is a fresh session *)
      in_dom(epk, AEKey) &&
      (in_dom (epk, ValidKey) && mem(pk, ValidKey[epk]))
        (* pk is known by the TPM *)
    ) { 
      (* In that case we start the session *)
      TPMSession[sid] = (epk, pk);
    }
  } 

  (* Since both TPM_2 and TPM_3 make the same thing, I merge the two functions.
     Normally it is important to be able to relate the number of session with
     the number of decription. I postpone this *)
       
  fun TPM_2(sid : SessionId, a : cipher) : bitstring{eta} option = {
    var esk   : ae_sk;
    var epk   : ae_pk;
    var pk    : pk_type;
    var msg   : message;
    var c     : bitstring{eta};
    var pk'   : pk_type;
    var res   : bitstring{eta} option = None;
    if (in_dom(sid, TPMSession)) {
       (epk,pk) = TPMSession[sid];
       esk = AEKey[epk];
       msg = a_dec(esk, a);
       (c,pk') = split_bs(msg);
       if (pk = pk') { res = Some(c);}
    }     
    return res;
  }

  (* AC oracles *)
  var DSKey : (CAid, ds_pk * ds_sk) map
  var ValidTPM : (CAid, ae_pk list) map

  var CASession : (SessionId, (bitstring{eta} * (CAid * (ae_pk * pk_type)))) map

  fun AC_1 (sid : SessionId, caid : CAid, epk : ae_pk, pk : pk_type) : 
                                            cipher option = {
    var a   : cipher;
    var c   : bitstring{eta} = {0,1}^eta;
    var res : cipher option = None;
    var r   : ae_random = sample_ae(0);
    if (!in_dom(sid,CASession) && (* sid is a fresh session *)
        in_dom(caid, DSKey) &&    (* cpk is a valid DS key *)
        in_dom(caid, ValidTPM) && (mem(epk, ValidTPM[caid]))
             (* the TPM tpmid is known by the CA associated to caid *)
       ) {
      (* In that case we start the session *)
      CASession[sid] = (c, (caid, (epk, pk)));
      a = a_enc(r, epk, (c || pk));
      res = Some(a);
    }
    return res;
  }

  var RegList : challenge list

  fun AC_2 (sid : SessionId, c' : bitstring{eta}) : 
                        (scipher * cipher) option = {
    var c     : bitstring{eta};
    var caid  : CAid;
    var cpk   : ds_pk;
    var epk   : ae_pk;
    var pk    : pk_type;
    var csk   : ds_sk;
    var cer   : certificate;
    var k     : se_key;
    var b     : scipher;
    var d     : cipher;
    var r     : ae_random = sample_ae(0);
    var res   : (scipher * cipher) option = None;
    var rs    : ds_random = sample_ds(0);
    var rse   : s_random = sample_s();
 
    if (in_dom(sid, CASession)) {
       (c,caid,epk,pk) = CASession[sid];
       (cpk,csk) = DSKey[caid];
       cer = sig(rs, csk, pk);
       if (c = c') {
          k = s_kg(0);
          b = s_enc(rse,k,cer);
          d = a_enc(r,epk, k || pk);
          RegList = (epk, (cpk, (pk, cer))) :: RegList;
          res = some ((b, d));
       }
    }
    return res;
  }

  var LCorrCA : ds_pk list

  fun CorrCA(caid : CAid) : ds_sk option = {
    var res : ds_sk option = none;

    if (caid < p_ca) {
      LCorrCA = fst(DSKey[caid]) :: LCorrCA;
      res = some(snd(DSKey[caid]));
    }
    return res;
  }

  abs A1 = A1 {}

  abs A2 = A2 {TPM_1, TPM_2, AC_1, AC_2, CorrCA } 

  fun Main () : bool = {

    var epkl   : ae_pk;
    var cpkj   : ds_pk;
    var pk     : pk_type;
    var cer    : certificate;
    var res    : bool;
    var i,i'   : int;
    var ca_pk  : (CAid,ds_pk) map;
    var tpm_pk : ae_pk list;
    var skg    : kg_random;
    var cpk    : ds_pk;
    var csk    : ds_sk;
    var epk    : ae_pk;
    var esk    : ae_sk;
    var sakg   : akg_random;
  
    (*  initialisation of TPM keys *)
    AEKey = empty_map ();
    tpm_pk = [];    
    i' = 0;
    while (i' < p_tpm) {
      sakg = sample_akg(0);
      (epk,esk) = a_kg(sakg);
      AEKey[epk] = esk;
      tpm_pk = epk :: tpm_pk;
      i' = i' + 1;
    }
  
    (*  initialisation of CA keys *)
    DSKey = empty_map ();
    ca_pk = empty_map ();    
    i = 0;
    while (i < p_ca) {
      skg = sample_kg(0);
      (cpk,csk) = kg(skg);
      DSKey[i] = (cpk,csk);
      ca_pk[i] = cpk;
      i = i + 1;
    }

    TPMSession = empty_map ();
    CASession = empty_map ();
    LCorrCA = [];
  
    (* Remark : A1 and A2 should normaly share a state 
       A solution is to add a parameter *)
    (ValidTPM, ValidKey) = A1(ca_pk, tpm_pk);
    RegList = [];
    (* this stand for (epkl, cpkj, pk, cer) = A2() *)
    (epkl, cpkj,pk,cer) = A2(); 
    if (!verify(cpkj, pk, cer) || mem(cpkj,LCorrCA)) { 
      res = false; 
    } else {
      if (!test_reg( (cpkj,(pk,cer)), RegList)) { 
        res = true;
      } else {
        if (mem((epkl,(cpkj,(pk,cer))),RegList) && 
           !(in_dom(epkl,ValidKey) && mem(pk, ValidKey[epkl]))) { 
          res = true;
        } else { 
          res = false;
        }
      }
    }  
    return res;
  }

}.


(* We define the INDCCA experiment *)
cnst msg0 : message.

game IND_CCA0 = {

  var AEKey : (ae_pk, ae_sk) map  
  var LOG : (ae_pk * (message * cipher)) list

  fun A_ENC (epk:ae_pk, msg:message) : cipher = {
    var r:ae_random = sample_ae(0);
    var c':cipher = a_enc(r,epk,msg);
    LOG = (epk,(msg,c')) :: LOG;
    return c';
  }
   
  fun A_DEC (epk:ae_pk, c:cipher) : message = {
    var res : message = msg0;
    if (in_dom(epk, AEKey)) {
      res = a_dec(AEKey[epk], c);
      (* If the decryption correspond to a anterior encryption query,
          we return msg0 *)
      if (mem((epk, (res,c)), LOG)) { res = msg0; };
    };
    return res;
  }

  (**** The adversary part ****)
  (* The advesary should not use LOG and AEKey *)

  var tpm_pk : ae_pk list

  var ValidKey : (ae_pk, pk_type list) map
  
  var TPMSession : (SessionId, (ae_pk * pk_type)) map

  fun TPM_1 (sid : int, epk : ae_pk, pk : pk_type) : unit = {
    if (!in_dom(sid, TPMSession) && (* sid is a fresh session *)
         mem(epk,tpm_pk) && (* epkis a valid identifier for the TPM *)
         (in_dom (epk, ValidKey) && mem(pk, ValidKey[epk])) 
               (* pk is known by the TPM *)
       ) { 
      (* In that case we start the session *)
      TPMSession[sid] = (epk, pk);
    };
    return;
  } 

  var FakeEnc : (ae_pk * cipher, message) map
  fun TPM_2(sid : SessionId, a : cipher) : bitstring{eta} option = {
    var epk   : ae_pk;
    var pk    : pk_type;
    var msg   : message;
    var c     : bitstring{eta};
    var pk'   : pk_type;
    var res   : bitstring{eta} option = none;
    if (in_dom(sid, TPMSession)) {
       (epk,pk) = TPMSession[sid];
       if (in_dom((epk,a),FakeEnc)) {
         msg = FakeEnc[(epk,a)];
       } else {
         msg = A_DEC(epk,a);
       }
       (c,pk') = split_bs(msg);
       if (pk = pk') { res = some(c);};
    };      
    return res;
  }

  (* AC oracles *)
  var DSKey : (CAid, ds_pk * ds_sk) map
  var ValidTPM : (CAid, ae_pk list) map

  var CASession : (SessionId, (bitstring{eta} * (CAid * (ae_pk * pk_type)))) map

  fun AC_1 (sid : SessionId, caid : CAid, epk : ae_pk, pk : pk_type) : 
                                            cipher option = {
    var a   : cipher;
    var c   : bitstring{eta} = {0,1}^eta;
    var res : cipher option = none;
    if (!in_dom(sid,CASession) && (* sid is a fresh session *)
        in_dom(caid, DSKey) && (* cpk is a valid DS key *)
        in_dom(caid, ValidTPM) && (mem(epk, ValidTPM[caid]))
             (* the TPM tpmid is known by the CA associated to caid *)
       ) {
      (* In that case we start the session *)
      CASession[sid] = (c, (caid, (epk, pk)));
      a = A_ENC(epk, (c || pk));
      FakeEnc[(epk,a)] = c || pk;
      res = some(a);
    };
    return res;
  }

  var RegList : challenge list

  fun AC_2 (sid : SessionId, c' : bitstring{eta}) : 
                        (scipher * cipher) option = {
    var c     : bitstring{eta};
    var aux1  : CAid * (ae_pk * pk_type);
    var aux2  : ae_pk * pk_type;
    var caid  : CAid;
    var cpk   : ds_pk;
    var epk   : ae_pk;
    var pk    : pk_type;
    var csk   : ds_sk;
    var cer   : certificate;
    var k     : se_key;
    var b     : scipher;
    var d     : cipher;
    var res   : (scipher * cipher) option = none;
    var rs    : ds_random = sample_ds(0);
    var rse   : s_random = sample_s(0);
 
    if (in_dom(sid, CASession)) {
       (c, aux1) = CASession[sid];
       (caid,aux2) = aux1;
       (epk, pk) = aux2;
       (cpk,csk) = DSKey[caid];
       cer = sig(rs, csk, pk);
       if (c = c') {
          k = s_kg(0);
          b = s_enc(rse,k,cer);
          d = A_ENC(epk, k || pk);
          FakeEnc[(epk,d)] = k || pk;
          RegList = (epk, (cpk, (pk, cer))) :: RegList;
          res = some ((b, d));
       };
    };
    return res;
  }

  var LCorrCA : ds_pk list

  fun CorrCA(caid : CAid) : ds_sk option = {
    var res : ds_sk option = none;

    if (caid < p_ca) {
      LCorrCA = fst(DSKey[caid]) :: LCorrCA;
      res = some(snd(DSKey[caid]));
    };
    return res;
  }

  abs A1 = A1 {}

  abs A2 = A2 {TPM_1, TPM_2, AC_1, AC_2, CorrCA } 

  var epkl_   : ae_pk
  var cpkj_   : ds_pk
  var pk_     : pk_type
  var cer_    : certificate
  var j0      : int
  fun B (tpm_pk' : ae_pk list) : bool = {
    var aux1   : ds_pk * (pk_type * certificate);
    var aux2   : pk_type * certificate;
    var res    : bool;
    var ca_pk  : (CAid,ds_pk) map;
    var skg    : kg_random;
    var cpk    : ds_pk;
    var csk    : ds_sk;
    var i      : int;   

    (*  initialisation of CA keys *)
    DSKey = empty_map ();
    ca_pk = empty_map ();    
    i = 0;
    while (i < p_ca) {
      skg = sample_kg(0);
      (cpk,csk) = kg(skg);
      DSKey[i] = (cpk,csk);
      ca_pk[i] = cpk;
      i = i + 1;
    }

    tpm_pk = tpm_pk';
    FakeEnc = empty_map(); 
    TPMSession = empty_map ();
    CASession = empty_map ();
    LCorrCA = [];
    
 

    (ValidTPM, ValidKey) = A1(ca_pk, tpm_pk);
    RegList = [];
    (* this stand for (epkl_, cpkj_, pk_, cer_) = A2() *)
    (epkl_, aux1) = A2(); 
    (cpkj_, aux2) = aux1;
    (pk_, cer_) = aux2;
    
    if (!verify(cpkj_, pk_, cer_) || mem(cpkj_,LCorrCA)) { 
      res = false; 
    } else {
      if (!test_reg( (cpkj_,(pk_,cer_)), RegList)) { 
        res = true;
      } else {
        if (mem((epkl_,(cpkj_,(pk_,cer_))),RegList) && 
           !(in_dom(epkl_,ValidKey) && mem(pk_, ValidKey[epkl_]))) { 
          res = true;
        } else { 
          res = false;
        }
      }
    }  
    j0 = [0 .. p_ca - 1];
    return res;
  }

 
  (**** The main part *****)
  fun Main ()   : bool = {
    var d       : bool;
    var tpm_pk' : ae_pk list;
    var epk     : ae_pk;
    var esk     : ae_sk;
    var sakg    : akg_random;
    var i'      : int;
    (*  initialisation of encryption keys *)
    AEKey = empty_map ();
    tpm_pk' = [];    
    i' = 0;
    while (i' < p_tpm) {
      sakg = sample_akg(0);
      (epk,esk) = a_kg(sakg);
      AEKey[epk] = esk;
      tpm_pk' = epk::tpm_pk';
      i' = i' + 1;
    }
    LOG = [];
    d = B(tpm_pk');
    return d;
  }
}

   
  
game IND_CCA1 = IND_CCA0 where 
   A_ENC = {
    var r:ae_random = sample_ae(0);
    var c':cipher = a_enc(r,epk,msg0);
    LOG = (epk,(msg,c')) :: LOG;
    return c';
  }


(* invariants : 
   (mem(epk,tmp_key) = in_dom(epk, AEKey)){2}
   in_dom(epk,AEKey) => valid_key(AEKey[epk],epk)
   TPMSession[sid] = (epk,pk) => in_dom(epk,ValidKey)
   in_dom((epk,a),FakeEnc) -> a_dec(esk,a) = FakeEnc[(epk,a)]
   mem((epk,c,a), LOG) -> in_dom((epk,a),FakeEnc) 
*)

prover "alt-ergo".

equiv PCAS_CCA0 : PCAS.Main ~ IND_CCA0.Main : {true} => ={res}.
inline; wp.
rnd{2};wp.
call inv (={ AEKey, ValidKey, TPMSession,
             DSKey, ValidTPM, CASession, RegList, LCorrCA } 
    /\
    (forall (epk:ae_pk). 
        { (mem(epk,tpm_pk) = in_dom(epk,AEKey)){2} }) 
    /\
    (forall (epk:ae_pk). 
        { (in_dom(epk,AEKey)){1} } => 
        { (check_aekey(epk, AEKey[epk])){1} })
    /\
    (forall (sid:int).
       { (in_dom(sid,TPMSession)){1} } =>
       { (in_dom(fst(TPMSession[sid]),AEKey)){1} })
    /\
    (forall (epk:ae_pk, a:cipher).
       { (in_dom((epk,a),FakeEnc)){2} } =>
       { (in_dom(epk,AEKey)){2} } =>  
       { (FakeEnc[(epk,a)] = a_dec(AEKey[epk],a)){2} }) 
    /\
    (forall (epk:ae_pk, c:message, a:cipher).
       { (mem((epk,(c,a)), LOG)){2} } =>
       { (in_dom((epk,a),FakeEnc)){2} })).  
auto inv {true}.
swap{2} [5-6] 4;wp.
app 3 3 (={AEKey, i'} 
         /\
         { tpm_pk{1} = tpm_pk'{2} } 
         /\
         (forall (epk:ae_pk). 
             { (mem(epk,tpm_pk') = in_dom(epk,AEKey)){2} }) 
         /\
         (forall (epk:ae_pk). 
             { (in_dom(epk,AEKey)){1} } => 
             { (check_aekey(epk, AEKey[epk])){1} })).
trivial.
while : (={AEKey, i'} 
         /\
         { tpm_pk{1} = tpm_pk'{2} } 
         /\
         (forall (epk:ae_pk). 
             { (mem(epk,tpm_pk') = in_dom(epk,AEKey)){2} }) 
         /\
         (forall (epk:ae_pk). 
             { (in_dom(epk,AEKey)){1} } => 
             { (check_aekey(epk, AEKey[epk])){1} })).
(* body *)
wp;rnd;trivial.
(* tail *)
app 3 3 (={AEKey, i', i, DSKey, ca_pk} 
         /\
         { tpm_pk{1} = tpm_pk'{2} } 
         /\
         (forall (epk:ae_pk). 
             { (mem(epk,tpm_pk') = in_dom(epk,AEKey)){2} }) 
         /\
         (forall (epk:ae_pk). 
             { (in_dom(epk,AEKey)){1} } => 
             { (check_aekey(epk, AEKey[epk])){1} })).
trivial.
while : (={AEKey, i', i, DSKey, ca_pk} 
         /\
         { tpm_pk{1} = tpm_pk'{2} } 
         /\
         (forall (epk:ae_pk). 
             { (mem(epk,tpm_pk') = in_dom(epk,AEKey)){2} }) 
         /\
         (forall (epk:ae_pk). 
             { (in_dom(epk,AEKey)){1} } => 
             { (check_aekey(epk, AEKey[epk])){1} })).
(* body *)
wp;rnd;trivial.
(* tail *)
prover simplify.
trivial.
save.

claim PrPCAS_CCA0 : PCAS.Main[res] = IND_CCA0.Main[res] using PCAS_CCA0.

equiv IND_CCA1_1 : IND_CCA1.Main ~ IND_CCA1.Main : {true} => 
   { res{1} } =>
   { ((verify(cpkj_, pk_, cer_) && !mem(cpkj_,LCorrCA) &&
       !test_reg( (cpkj_,(pk_,cer_)), RegList))
      ||
      (mem((epkl_,(cpkj_,(pk_,cer_))),RegList) && 
       !(in_dom(epkl_,ValidKey) && mem(pk_, ValidKey[epkl_])))){2} }.
inline B;wp.
rnd;wp.
prover "alt-ergo".
call inv ={ AEKey, ValidKey, TPMSession,
            DSKey, ValidTPM, CASession, RegList, LCorrCA, 
            FakeEnc, LOG, tpm_pk }.
auto inv {true}.
app 3 3 (={AEKey,i',tpm_pk'}).
trivial.
while : (={AEKey,i',tpm_pk'}).
wp;rnd;trivial.
app 5 5  (={AEKey,i,tpm_pk'_0, LOG, DSKey, ca_pk}).
trivial.
while : (={AEKey,i,tpm_pk'_0, LOG, DSKey, ca_pk}).
wp;rnd;trivial.
prover simplify.
trivial.
save.

claim PrIND_CCA1 : 
 IND_CCA1.Main[res] <= 
 IND_CCA1.Main[( verify(cpkj_, pk_, cer_) && !mem(cpkj_,LCorrCA) &&
                 !test_reg( (cpkj_,(pk_,cer_)), RegList))
               ||
               ( mem((epkl_,(cpkj_,(pk_,cer_))),RegList) && 
                 !(in_dom(epkl_,ValidKey) && mem(pk_, ValidKey[epkl_])))]
using IND_CCA1_1.

claim PrIND_CCA1_split : 
 IND_CCA1.Main[( verify(cpkj_, pk_, cer_) && !mem(cpkj_,LCorrCA) &&
                 !test_reg( (cpkj_,(pk_,cer_)), RegList))
               ||
               ( mem((epkl_,(cpkj_,(pk_,cer_))),RegList) && 
                 !(in_dom(epkl_,ValidKey) && mem(pk_, ValidKey[epkl_])))]
 <=
 IND_CCA1.Main[ verify(cpkj_, pk_, cer_) && !mem(cpkj_,LCorrCA) &&
                 !test_reg( (cpkj_,(pk_,cer_)), RegList) ] +
 IND_CCA1.Main[ mem((epkl_,(cpkj_,(pk_,cer_))),RegList) && 
                 !(in_dom(epkl_,ValidKey) && mem(pk_, ValidKey[epkl_]))]
split.

(* At that point we should bound the two probabilities
   we start by showing that 
    IND_CCA1.Main[ verify(cpkj_, pk_, cer_) && !mem(cpkj_,LCorrCA) &&
                 !test_reg( (cpkj_,(pk_,cer_)), RegList) ]
   is bounded by the probability of forging a message *)

(** Definition of the EU-CMA game  **)

game EU_CMA = {
  var SLOG : (pk_type * certificate) list
  var ssk: ds_sk

  fun Sig(m:pk_type) : certificate = {
    var cer : certificate;
    var rs   : ds_random = sample_ds(0);
    cer = sig(rs,ssk, m);
    SLOG = (m, cer) :: SLOG;
    return cer;
  }

  (* Definition of the adversary *)
  (* The adversary should not use SLOG and ssk *)
  var spk : ds_pk
  var AEKey : (ae_pk, ae_sk) map  
  var LOG : (ae_pk * (message * cipher)) list

  fun A_ENC (epk:ae_pk, msg:message) : cipher = {
    var r:ae_random = sample_ae(0);
    var c':cipher = a_enc(r,epk,msg0);
    LOG = (epk,(msg,c')) :: LOG;
    return c';
  }
   
  fun A_DEC (epk:ae_pk, c:cipher) : message = {
    var res : message = msg0;
    if (in_dom(epk, AEKey)) {
      res = a_dec(AEKey[epk], c);
      (* If the decryption correspond to a anterior encryption query,
          we return msg0 *)
      if (mem((epk, (res,c)), LOG)) { res = msg0; };
    };
    return res;
  }

  (**** The adversary part ****)

  var tpm_pk : ae_pk list

  var ValidKey : (ae_pk, pk_type list) map
  
  var TPMSession : (SessionId, (ae_pk * pk_type)) map

  fun TPM_1 (sid : int, epk : ae_pk, pk : pk_type) : unit = {
    if (!in_dom(sid, TPMSession) && (* sid is a fresh session *)
         mem(epk,tpm_pk) && (* epkis a valid identifier for the TPM *)
         (in_dom (epk, ValidKey) && mem(pk, ValidKey[epk])) 
               (* pk is known by the TPM *)
       ) { 
      (* In that case we start the session *)
      TPMSession[sid] = (epk, pk);
    };
    return;
  } 

  var FakeEnc : (ae_pk * cipher, message) map

  fun TPM_2(sid : SessionId, a : cipher) : bitstring{eta} option = {
    var epk   : ae_pk;
    var pk    : pk_type;
    var msg   : message;
    var c     : bitstring{eta};
    var pk'   : pk_type;
    var res   : bitstring{eta} option = none;
    if (in_dom(sid, TPMSession)) {
       (epk,pk) = TPMSession[sid];
       if (in_dom((epk,a),FakeEnc)) {
         msg = FakeEnc[(epk,a)];
       } else {
         msg = A_DEC(epk,a);
       }
       (c,pk') = split_bs(msg);
       if (pk = pk') { res = some(c);};
    };      
    return res;
  }

  (* AC oracles *)

  var j0 : CAid
  var DSKey : (CAid, ds_pk * ds_sk) map
  var ValidTPM : (CAid, ae_pk list) map

  var CASession : (SessionId, (bitstring{eta} * (CAid * (ae_pk * pk_type)))) map

  fun AC_1 (sid : SessionId, caid : CAid, epk : ae_pk, pk : pk_type) : 
                                            cipher option = {
    var a   : cipher;
    var c   : bitstring{eta} = {0,1}^eta;
    var res : cipher option = none;
    if (!in_dom(sid,CASession) && (* sid is a fresh session *)
        (in_dom(caid, DSKey) || caid = j0) && (* cpk is a valid DS key *)
        in_dom(caid, ValidTPM) && (mem(epk, ValidTPM[caid]))
             (* the TPM tpmid is known by the CA associated to caid *)
       ) {
      (* In that case we start the session *)
      CASession[sid] = (c, (caid, (epk, pk)));
      a = A_ENC(epk, (c || pk));
      FakeEnc[(epk,a)] = c || pk;
      res = some(a);
    };
    return res;
  }

  var RegList : challenge list

  fun AC_2 (sid : SessionId, c' : bitstring{eta}) : 
                        (scipher * cipher) option = {
    var c     : bitstring{eta};
    var aux1  : CAid * (ae_pk * pk_type);
    var aux2  : ae_pk * pk_type;
    var caid  : CAid;
    var cpk   : ds_pk;
    var epk   : ae_pk;
    var pk    : pk_type;
    var csk   : ds_sk;
    var cer   : certificate;
    var k     : se_key;
    var b     : scipher;
    var d     : cipher;
    var res   : (scipher * cipher) option = none;
    var rs    : ds_random = sample_ds(0);
    var rse   : s_random = sample_s(0);
 
    if (in_dom(sid, CASession)) {
       (c, aux1) = CASession[sid];
       (caid,aux2) = aux1;
       (epk, pk) = aux2;

       if (caid = j0) {
         cpk = spk;
         cer = Sig(pk);
       } else {  
         (cpk,csk) = DSKey[caid];
         cer = sig(rs, csk, pk);
       }
       if (c = c') {
          k = s_kg(0);
          b = s_enc(rse,k,cer);
          d = A_ENC(epk, k || pk);
          FakeEnc[(epk,d)] = k || pk;
          RegList = (epk, (cpk, (pk, cer))) :: RegList;
          res = some ((b, d));
       };
    };
    return res;
  }

  var LCorrCA : ds_pk list

  fun CorrCA(caid : CAid) : ds_sk option = {
    var res : ds_sk option = none;
    if (caid < p_ca) {
      if (caid = j0) { 
        LCorrCA = spk:: LCorrCA;
      } else {
        LCorrCA = fst(DSKey[caid]) :: LCorrCA;
        res = some(snd(DSKey[caid]));
      }
    };
    return res;
  }

  abs A1 = A1 {}

  abs A2 = A2 {TPM_1, TPM_2, AC_1, AC_2, CorrCA } 

  var epkl_   : ae_pk
  var cpkj_   : ds_pk
  var pk_     : pk_type
  var cer_    : certificate

  fun B (spk' : ds_pk) : (pk_type*certificate) = {
    var aux1   : ds_pk * (pk_type * certificate);
    var aux2   : pk_type * certificate;
    var res    : bool;
    var ca_pk  : (CAid,ds_pk) map;
    var skg    : kg_random;
    var sakg   : akg_random;
    var cpk    : ds_pk;
    var csk    : ds_sk;
    var epk    : ae_pk;
    var esk    : ae_sk;
    var i,i'   : int;   
  
    (*  initialisation of encryption keys *)
    AEKey = empty_map ();
    tpm_pk = [];    
    i' = 0;
    while (i' < p_tpm) {
      sakg = sample_akg(0);
      (epk,esk) = a_kg(sakg);
      AEKey[epk] = esk;
      tpm_pk = epk::tpm_pk;
      i' = i' + 1;
    }

    (*  initialisation of CA keys *)
    j0 = [0 .. p_ca-1];
    DSKey = empty_map ();
    ca_pk = empty_map ();    
    i = 0;
    spk = spk';
    while (i < j0) {
      skg = sample_kg(0);
      (cpk,csk) = kg(skg);
      DSKey[i] = (cpk,csk);
      ca_pk[i] = cpk;
      i = i + 1;
    }
    ca_pk[i] = spk;
    i = i + 1;
    while (i < p_ca) {
      skg = sample_kg(0);
      (cpk,csk) = kg(skg);
      DSKey[i] = (cpk,csk);
      ca_pk[i] = cpk;
      i = i + 1;
    }

    LOG = [];
    FakeEnc = empty_map(); 
    TPMSession = empty_map ();
    CASession = empty_map ();
    LCorrCA = [];
    
 

    (ValidTPM, ValidKey) = A1(ca_pk, tpm_pk);
    RegList = [];
    (* this stand for (epkl_, cpkj_, pk_, cer_) = A2() *)
    (epkl_, aux1) = A2(); 
    (cpkj_, aux2) = aux1;
    (pk_, cer_) = aux2;
    
    return (pk_, cer_);

  }

  (* The main game *)
  fun Main () : bool = {
    var skg : kg_random = sample_kg(0);
    var spk' : ds_pk;
    var m   : pk_type;
    var sig : certificate;
    (spk',ssk) = kg(skg);
    SLOG = [];
    (m, sig) = B(spk');
    return (verify(spk',m,sig) && !(mem((m,sig),SLOG)));
  }
}

game EU_CMA_1 = EU_CMA
   where CorrCA = {
    var res : ds_sk option = none;
    if (caid < p_ca) {
      if (caid = j0) { 
        LCorrCA = spk:: LCorrCA;
        res = some(ssk);
      } else {
        LCorrCA = fst(DSKey[caid]) :: LCorrCA;
        res = some(snd(DSKey[caid]));
      }
    };
    return res;
  }.

(* I admit this for the moment this easycrypt is not able to proof it. *)
claim IND_CCA1_j0 : 
    IND_CCA1.Main[verify(cpkj_, pk_, cer_) && 
                  !mem(cpkj_,LCorrCA) &&
                  !test_reg( (cpkj_,(pk_,cer_)), RegList)] * (1%r / p_ca%r) <=
    IND_CCA1.Main[verify(cpkj_, pk_, cer_) && 
                  !mem(cpkj_,LCorrCA) &&
                  !test_reg( (cpkj_,(pk_,cer_)), RegList) &&
                  fst(DSKey[j0]) = cpkj_ ]
admit.

(* This axiom should normaly be implies by p_ca_pos *)
axiom p_ca_pos' : { 0%r < p_ca%r }.

axiom toto : forall (x:real, y:real, z:real).
   { 0%r < z } => { x * (1%r / z) <= y } => { x <= z * y } .

claim IND_CCA1_j0' : 
    IND_CCA1.Main[verify(cpkj_, pk_, cer_) && 
                  !mem(cpkj_,LCorrCA) &&
                  !test_reg( (cpkj_,(pk_,cer_)), RegList)] <=
    p_ca%r * 
    IND_CCA1.Main[verify(cpkj_, pk_, cer_) && 
                  !mem(cpkj_,LCorrCA) &&
                  !test_reg( (cpkj_,(pk_,cer_)), RegList) &&
                  fst(DSKey[j0]) = cpkj_ ] .
unset IND_CCA1_j0.

equiv IND_CCA1_EU_CMA_1_CA2 : IND_CCA1.AC_2 ~ EU_CMA_1.AC_2 :
   (={ sid, c', AEKey, ValidKey, TPMSession, LOG, 
             ValidTPM, CASession, RegList, LCorrCA, 
             FakeEnc, j0, tpm_pk} 
          /\ 
          (forall (j:CAid). { !j=j0{1} } =>
             { (in_dom(j,DSKey)){1} = (in_dom(j,DSKey)){2} })
          /\
          (forall (j:CAid). { !j=j0{1} } =>
              { (DSKey[j]){1} = (DSKey[j]){2} })
          /\ 
          { (in_dom(j0,DSKey)){1} }
          /\ 
          { (DSKey[j0]){1} = ((spk,ssk)){2} }
          /\ 
          (forall (pk:pk_type, sig:certificate).
              { (mem((pk,sig),SLOG)){2} } =>
              exists (epk:ae_pk). 
                {mem((epk, (spk{2}, (pk, sig))), RegList{2})}))
    =>
    (={ res, AEKey, ValidKey, TPMSession, LOG, 
             ValidTPM, CASession, RegList, LCorrCA, 
             FakeEnc, j0, tpm_pk} 
          /\ 
          (forall (j:CAid). { !j=j0{1} } =>
             { (in_dom(j,DSKey)){1} = (in_dom(j,DSKey)){2} })
          /\
          (forall (j:CAid). { !j=j0{1} } =>
              { (DSKey[j]){1} = (DSKey[j]){2} })
          /\ 
          { (in_dom(j0,DSKey)){1} }
          /\ 
          { (DSKey[j0]){1} = ((spk,ssk)){2} }
          /\ 
          (forall (pk:pk_type, sig:certificate).
              { (mem((pk,sig),SLOG)){2} } =>
              exists (epk:ae_pk). 
                {mem((epk, (spk{2}, (pk, sig))), RegList{2})})).

inline;derandomize.
wp.
swap{2} [3-3] -1.
prover "alt-ergo".
do 3 rnd;trivial.
case {1} : (in_dom(sid,CASession) && fst(snd(CASession[sid]))=j0).
rnd;rnd{2};trivial.
rnd{2};rnd;trivial.
save.

axiom test_reg_spec : 
  forall (cpk:ds_pk, pk:pk_type, cer:certificate, 
          l : (ae_pk * (ds_pk * (pk_type * certificate))) list).
     (exists (epk:ae_pk). { mem((epk,(cpk,(pk,cer))), l) }) => 
     { test_reg((cpk,(pk,cer)),l) }.

equiv IND_CCA1_EU_CMA_1: IND_CCA1.Main ~ EU_CMA_1.Main : { true } =>
    ({ (verify(cpkj_, pk_, cer_) && 
      !mem(cpkj_,LCorrCA) &&
      !test_reg( (cpkj_,(pk_,cer_)), RegList) &&
      fst(DSKey[j0]) = cpkj_){1}} =>
    { (res && !mem(spk,LCorrCA)){2} }).
inline;wp.
swap{1} -15.
wp.
call inv (={ AEKey, ValidKey, TPMSession, LOG, 
             ValidTPM, CASession, RegList, LCorrCA, 
             FakeEnc, j0, tpm_pk} 
          /\ 
          (forall (j:CAid). { !j=j0{1} } =>
             { (in_dom(j,DSKey)){1} = (in_dom(j,DSKey)){2} })
          /\
          (forall (j:CAid). { !j=j0{1} } =>
              { (DSKey[j]){1} = (DSKey[j]){2} })
          /\ 
          { (in_dom(j0,DSKey)){1} }
          /\ 
          { (DSKey[j0]){1} = ((spk,ssk)){2} }
          /\ 
          (forall (pk:pk_type, sig:certificate).
              { (mem((pk,sig),SLOG)){2} } =>
              exists (epk:ae_pk). 
                {mem((epk, (spk{2}, (pk, sig))), RegList{2})})).
auto inv {true}.
swap{2} [5-9] -4.
app 3 3 (={AEKey,i'} /\ {tpm_pk'{1} = tpm_pk{2}}).
trivial.
while :  (={AEKey, i'} /\ {tpm_pk'{1} = tpm_pk{2}}).
wp;rnd;trivial.
swap{1} [1-2] 5;swap{2} [4-4] 9. 
swap{2} [8-8] 1;swap{2} [2-4] 4.
wp.
app 4 4 (={AEKey, j0, DSKey,ca_pk,i} /\ 
         { tpm_pk'{1} = tpm_pk{2} } /\
         { i{1} = 0 } /\ 
         { 0 <= j0{1} } /\ { j0{1} < p_ca } /\
         { DSKey{1} = empty_map() } /\
         { ca_pk{1} = empty_map() }).
wp;rnd;trivial.
splitw {1} (i < j0).
while : (={AEKey, j0, i, DSKey, ca_pk} /\
          { tpm_pk'{1} = tpm_pk{2} } /\
          { (i <= j0){1} } /\
          { 0 <= j0{1} } /\ { j0{1} < p_ca }).
wp;rnd;trivial.
unroll {1}.
app 5 6 (={AEKey, j0, i, ca_pk} /\
          { (spk = spk'){2} } /\
          { tpm_pk'{1} = tpm_pk{2} } /\
          { 0 <= j0{1} } /\ { j0{1} < p_ca } /\
          { (j0 < i){1} } /\
          (forall (j:CAid). { !j=j0{1} } =>
             { (in_dom(j,DSKey)){1} = (in_dom(j,DSKey)){2} })
          /\
          (forall (j:CAid). { !j=j0{1} } =>
              { (DSKey[j]){1} = (DSKey[j]){2} })
          /\ 
          { (in_dom(j0,DSKey)){1} }
          /\ 
          { (DSKey[j0]){1} = ((spk,ssk)){2} }).
wp;rnd;trivial.
while : (={AEKey, j0, i, ca_pk} /\
          { (spk = spk'){2} } /\
          { tpm_pk'{1} = tpm_pk{2} } /\
          { 0 <= j0{1} } /\ { j0{1} < p_ca } /\
          { (j0 < i){1} } /\
          (forall (j:CAid). { !j=j0{1} } =>
             { (in_dom(j,DSKey)){1} = (in_dom(j,DSKey)){2} })
          /\
          (forall (j:CAid). { !j=j0{1} } =>
              { (DSKey[j]){1} = (DSKey[j]){2} })
          /\ 
          { (in_dom(j0,DSKey)){1} }
          /\ 
          { (DSKey[j0]){1} = ((spk,ssk)){2} }).
wp;rnd;trivial.
prover simplify.
trivial.
prover "alt-ergo".
trivial.
save.          

claim IND_CCA1_EU_CMA_1 :
   IND_CCA1.Main[verify(cpkj_, pk_, cer_) && 
                  !mem(cpkj_,LCorrCA) &&
                  !test_reg( (cpkj_,(pk_,cer_)), RegList) &&
                  fst(DSKey[j0]) = cpkj_ ] <= 
   EU_CMA_1.Main[res && !mem(spk,LCorrCA)]
using IND_CCA1_EU_CMA_1.

(* We prove that EU_CMA_1 = EU_CMA upto the bad event mem(spk,LCorrCA) *)

prover simplify.  
equiv EU_CMA_1_EU_CMA : EU_CMA_1.Main ~ EU_CMA.Main : {true} =>
    { (mem(spk,LCorrCA)){1} = (mem(spk,LCorrCA)){2} } /\
    ({(!mem(spk,LCorrCA)){1}} => ={res,LCorrCA,spk}).
inline B;wp.
call inv upto {mem(spk,LCorrCA)} with
  ={SLOG, ssk, spk, AEKey, LOG, tpm_pk, ValidKey, TPMSession, FakeEnc,j0,
    DSKey, ValidTPM,CASession,LCorrCA,RegList}.
wp;call inv ={SLOG, ssk, spk, AEKey, LOG, tpm_pk, TPMSession, FakeEnc,j0,
    DSKey, CASession,LCorrCA}.
wp.
app 7 7 ={spk',ssk, SLOG,spk'_0,AEKey,tpm_pk,i'}.
wp;rnd;trivial.
while : ={spk',ssk, SLOG,spk'_0,AEKey,tpm_pk,i'}. 
wp;rnd;trivial.
app 5 5 ={spk',ssk, SLOG,spk'_0,AEKey,tpm_pk,i', j0, DSKey,ca_pk, i, spk}.
wp;rnd;trivial.
while : ={spk',ssk, SLOG,spk'_0,AEKey,tpm_pk,i', j0, DSKey,ca_pk, i, spk}.
wp;rnd;trivial.
app 2 2 ={spk',ssk, SLOG,spk'_0,AEKey,tpm_pk,i', j0, DSKey,ca_pk, i, spk}.
wp;trivial.
while : ={spk',ssk, SLOG,spk'_0,AEKey,tpm_pk,i', j0, DSKey,ca_pk, i, spk}.
wp;rnd;trivial.
trivial.
save.

claim EU_CMA_1_EU_CMA : 
  EU_CMA_1.Main[res && !mem(spk,LCorrCA)] <= EU_CMA.Main[res]
using EU_CMA_1_EU_CMA.

axiom rmult_pos : forall (x:real, y:real, z:real).
   { 0%r <= z } => { x <= y } => { z * x <= z * y}.

claim auxiliary1 : 
  IND_CCA1.Main[verify(cpkj_, pk_, cer_) && 
                  !mem(cpkj_,LCorrCA) &&
                  !test_reg( (cpkj_,(pk_,cer_)), RegList)] <=
  p_ca%r *  EU_CMA.Main[res].

unset IND_CCA1_EU_CMA_1, EU_CMA_1_EU_CMA, rmult_pos.

(* We bound the probability of 
   IND_CCA1.Main[ mem((epkl_,(cpkj_,(pk_,cer_))),RegList) && 
                 !(in_dom(epkl_,ValidKey) && mem(pk_, ValidKey[epkl_]))] *)
(* This part should be done 
   max_session should bound the maximun number of session 
   We should instrumentize the previous game *)
cnst max_session : int.

claim find_random :
    IND_CCA1.Main[ mem((epkl_,(cpkj_,(pk_,cer_))),RegList) && 
                 !(in_dom(epkl_,ValidKey) && mem(pk_, ValidKey[epkl_]))] <=
      max_session%r / (2^eta)%r
admit.

(* Now we can conclude *)

claim conclusion :
   PCAS.Main[res] <= 
     | IND_CCA0.Main[res] - IND_CCA1.Main[res] | +
     p_ca%r * EU_CMA.Main[res] +
     max_session%r / (2^eta)%r.
