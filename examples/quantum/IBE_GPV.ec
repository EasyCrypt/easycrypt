require import AllCore List Distr DBool CHoareTactic.
require (*  *) T_QROM T_PERM T_CPA T_IBE.
(*   *) import StdOrder RField RealOrder StdBigop Bigreal.
(* --------------------------------------------------------------------------- *)

clone import T_IBE as IBE.

clone include T_PERM with 
   type pkey  <- mpkey,
   type skey  <- mskey,
   type dom   <- skey,
   type codom <- pkey.

clone import T_PSF as PSF.

clone import T_QROM as QROM with
  type from <- identity,
  type hash <- pkey
  rename "hash" as "pkey".

clone include T_CPA with
   type msg    <- msg,
   type cipher <- cipher,
   type pkey   <- mpkey * pkey,
   type skey   <- skey,
   type input  <- real.

import MUFF.
(* --------------------------------------------------------------------------*)
op [lossless uniform full] dskey : skey distr.
(* FIXME: this should be provable because f is bijective *)
axiom dpkey_dskey : mu1 dpkey witness = mu1 dskey witness.

op dfskey : (identity -> skey) distr = dfun (fun _ => dskey).

lemma dfskey_ll: is_lossless dfskey.
proof. apply dfun_ll => ?;apply dskey_ll. qed.

lemma dfskey_uni: is_uniform dfskey.
proof. apply dfun_uni => ?; apply dskey_uni. qed.

lemma dfskey_fu: is_full dfskey.
proof. apply dfun_fu => ?; apply dskey_fu. qed.

hint solve 0 random : dfskey_ll dfskey_uni dfskey_fu.

lemma dfskey_dfpkey (hs: identity -> skey) (hh:identity -> pkey) : mu1 dfskey hs = mu1 dfpkey hh.
proof.
  rewrite !dfun1E;apply BRM.eq_big => //= x _.
  rewrite (is_full_funiform _ dskey_fu dskey_uni _ witness).
  by rewrite (is_full_funiform _ dpkey_fu dpkey_uni _ witness) dpkey_dskey.
qed.

(* --------------------------------------------------------------------------- *)
(* Security definition of IBE scheme in the QROM  *)

module type IBEScheme_QROM (H:QRO) = {
  proc kg() : mpkey * mskey
  proc extract(msk:mskey, id:identity) : skey
  proc enc(mpk:mpkey, id:identity, m:msg) : cipher
  proc dec(sk:skey, c:cipher) : msg option
}.

quantum module type AdvIDCPA_QROM (H:QRO) (O:OrclIBE) = {
  proc choose (mpk:mpkey) : identity * msg * msg
  proc guess (c:cipher) : bool
}.

module Wrap (A:AdvIDCPA_QROM) (H:QRO) (O:OrclIBE) = {
  var ch : int
  var ce : int

  module Hc = {
    quantum proc h {x:identity} = {
      quantum var h;
      ch <- ch+1;
      h <@ H.h{x};
      return h;
    }
  } 

  module Oc = {
    proc extract (id:identity) = {
      var s;
      ce <- ce+1;
      s <@ O.extract(id);
      return s;
    }
  }

  proc choose(mpk:mpkey) = {
    var ms;
    ch <- 0; ce <- 0;
    ms <@ A(Hc, Oc).choose(mpk); 
    return ms;
  } 

  proc guess = A(Hc,Oc).guess

}.

module IDCPA_QROM (A:AdvIDCPA_QROM) (S:IBEScheme_QROM) = {
  proc main() = {
    var b;
    QRO.init();
    b <@ IDCPA(Wrap(A, QRO), S(QRO)).main();
    return b;
  }
}.

module type EncScheme0  = {
  proc enc (pk : mpkey * pkey, m : msg): cipher   
  proc dec (sk : skey, c : cipher): msg option 
}.

module ES(E:EncScheme0) : EncScheme = {
  proc kg() : (mpkey*pkey) * skey = {
    var mpk, msk, sk;
    (mpk, msk) <$ kg;
    sk <$ sampleD;
    return ((mpk, f mpk sk), sk);
  }
  include E
}.

(* --------------------------------------------------------------------------- *)
(* GPV scheme                                                                  *)

module GPV (E:EncScheme0) (H:QRO) = {
  proc kg() : mpkey * mskey = { var keys; keys <$ kg; return keys; }
  proc extract(msk:mskey, id:identity) : skey = {
    var pk;
    pk <@ H.h{id};
    return (finv msk pk);
  }
     
  proc enc(mpk:mpkey, id:identity, m:msg) : cipher = {
    var pk, c;
    pk <@ H.h{id};
    c <@ E.enc((mpk, pk), m);
    return c;
  }
  proc dec = E.dec
    
}.

(* --------------------------------------------------------------------------- *)
(* Maximal number of queries to the extract/hash oracle *)
op cqe : { int | 0 <= cqe } as ge0_cqe.
op cqh : { int | 0 <= cqh } as ge0_cqh.

op gqe : { int | 0 <= gqe } as ge0_gqe.
op gqh : { int | 0 <= gqh } as ge0_gqh.

op qe = cqe + gqe.
op qh = cqh + gqh.

lemma ge0_qe : 0 <= qe.
proof. smt(ge0_cqe ge0_gqe). qed.

lemma ge0_qh : 0 <= qh.
proof. smt(ge0_cqh ge0_gqh). qed.

op q = qe + qh + 1.

(* --------------------------------------------------------------------------- *)

module B (A:AdvIDCPA_QROM) : AdvCPA = {
  import var IDCPA

  var he : identity -> skey
  var bf : identity -> bool

  module E0 = {
    proc extract(id:identity) : skey = {
      log <- id::log;
      return he id;
    }
  }

  proc choose (lam_:real, k: mpkey * pkey) : msg * msg = {
    var m1, m2, mpk, pk;
    (mpk, pk) <- k;
    log <- [];
    bf <$ dbfun lam_;
    he <$ dfskey;
    QRO.h <- (fun m => if bf m then pk else f mpk (he m)); 
    (id,m1,m2) <@ A(QRO,E0).choose(mpk);
    return (m1,m2);
  }

  proc guess(c:cipher) : bool = {
    var b';
    b' <@ A(QRO,E0).guess(c);
    if (!(bf id /\ (forall x', x' \in log => !bf x'))) b' <$ {0,1};
    return b';
  }
    
}.

clone import SemiConstDistr with
    op k <- qe.

section.

declare module E <: EncScheme0 {-IDCPA, -QRO, -B, -Wrap, -SCD}.

declare module A <: 
  AdvIDCPA_QROM { -IDCPA, -QRO, -E, -B, -Wrap, -SCD}.

declare axiom A_wf : hoare [ IDCPA_QROM(A,GPV(E)).main : true ==> !IDCPA.id \in IDCPA.log /\
                                                          uniq IDCPA.log /\
                                                          size IDCPA.log = qe].

declare axiom choose_ll (H <: QRO{-A}) (O <: OrclIBE{-A}) :
   islossless O.extract => islossless H.h => islossless A(H, O).choose.

declare axiom guess_ll (H <: QRO{-A}) (O <: OrclIBE{-A}) :
  islossless O.extract => islossless H.h => islossless A(H, O).guess.

declare axiom hoare_bound_c (H<:QRO{-A,-Wrap}) (O<:OrclIBE{-A,-Wrap}) : 
  hoare [Wrap(A, H, O).choose : true  ==> Wrap.ce <= cqe /\ Wrap.ch <= cqh].

declare axiom hoare_bound_g (H<:QRO{-A,-Wrap}) (O<:OrclIBE{-A,-Wrap}) ke kh: 
  hoare [Wrap(A, H, O).guess : Wrap.ce = ke /\ Wrap.ch = kh  ==> 
                               Wrap.ce <= ke + gqe /\ Wrap.ch <= kh + gqh].

declare axiom enc_ll : islossless E.enc.

module type Init = {
  proc * init (h: identity -> pkey, lam_: real) : (identity -> bool) * (identity -> pkey)
}.

local module G(I:Init) = {
  import var IDCPA
  var bf   : identity -> bool
 
  proc main0(lam_:real) = {
    var b2;
    QRO.init();
    (bf, QRO.h) <@ I.init(QRO.h, lam_);
    b2 <@ IDCPA(Wrap(A,QRO), GPV(E,QRO)).main();
    return b2;
  }

  proc main(lam_:real) = {
    var b1;
    b1 <@ main0(lam_);
    if (bf IDCPA.id /\ forall id', id' \in log => !bf id') b1 <- IDCPA.b = IDCPA.b';
    else b1 <$ {0,1};
    return b1 ;
  }
}.

local lemma pr_split lam (I<:Init{-A,-E, -QRO}) &m :
  islossless I.init =>
  equiv [I.init ~ I.init : ={arg} ==> ={res}] =>
  Pr[G(I).main(lam) @ &m : res] = 
   0.5 * (1.0 - Pr[G(I).main0(lam) @ &m : G.bf IDCPA.id /\ forall id', id' \in IDCPA.log => !G.bf id']) +
   Pr[G(I).main0(lam) @ &m : res /\ (G.bf IDCPA.id /\ forall id', id' \in IDCPA.log => !G.bf id')].
proof.
  move=> I_ll hI.
  have -> : Pr[G(I).main(lam) @ &m : res] =
    Pr[G(I).main(lam) @ &m : 
      res /\ !(G.bf IDCPA.id /\ (forall id', id' \in IDCPA.log => !G.bf id')) \/
      res /\  (G.bf IDCPA.id /\ (forall id', id' \in IDCPA.log => !G.bf id'))].
  + by rewrite Pr [mu_eq] 1:/#.
  rewrite Pr [mu_disjoint] 1:/#; congr.
  + pose r :=  
      Pr[G(I).main0(lam) @ &m : G.bf IDCPA.id /\ forall (id' : identity), id' \in IDCPA.log => ! G.bf id'].
    byphoare (_: lam_ = lam /\ glob A = (glob A){m} /\ glob E = (glob E){m}==> _) => //.
    proc.
    seq 1 : (G.bf IDCPA.id /\ forall id', id' \in IDCPA.log => ! G.bf id')
            r 0.0
            (1.0 - r) 0.5 
            true => //.
    + by conseq (: false) => /> //.
    + phoare split ! 1.0 r.
      + islossless. 
        + by apply (guess_ll (<:Wrap(A, QRO, IDCPA(Wrap(A, QRO), GPV(E, QRO)).E).Hc)
                             (<:Wrap(A, QRO, IDCPA(Wrap(A, QRO), GPV(E, QRO)).E).Oc)); islossless.
        + by apply enc_ll.              
        by apply (choose_ll (<:Wrap(A, QRO, IDCPA(Wrap(A, QRO), GPV(E, QRO)).E).Hc)
                             (<:Wrap(A, QRO, IDCPA(Wrap(A, QRO), GPV(E, QRO)).E).Oc)); islossless.
      call (: (glob A, glob E) = (glob A, glob E){m} /\ lam_ = lam ==> 
               G.bf IDCPA.id /\ forall (id' : identity), id' \in IDCPA.log => ! G.bf id'); 2: by auto.
      by bypr => &m0 h; rewrite /r; byequiv => //; sim; move: h => />.  
    by rcondf 1 => //; conseq />; rnd (pred1 true); skip => /> *; rewrite dbool1E /= /pred1.
  byequiv (: _ ==> (res /\ G.bf IDCPA.id /\ forall (id' : identity), id' \in IDCPA.log => ! G.bf id'){1} =
                 (res /\ G.bf IDCPA.id /\ forall (id' : identity), id' \in IDCPA.log => ! G.bf id'){2}) => //;
    last by move=> &1 &2 ->.
  proc. inline *; wp.
  seq 22 21: (={IDCPA.id, IDCPA.log, IDCPA.b, IDCPA.b', G.bf}); 1: by sim.
  sp; if{1}; 1: by wp; skip => /> /#.
  conseq (:true). smt().
  rnd{1}; auto.
qed.

local module Init1 = {
  proc init(h:identity -> pkey, lam_:real) = {
    var bf;
    bf <$ dbfun lam_;
    return (bf, h);
  }
}.

local module G1 = {
  proc main(lam_) = {
    var b2;
    b2 <@ IDCPA_QROM(A,GPV(E)).main();
    G.bf <$ dbfun lam_;
    return b2;
  }  
}.

local equiv GI1_G1 : G(Init1).main0 ~ G1.main : ={glob A, glob E, lam_} ==> 
                     ={res,IDCPA.id, IDCPA.log,G.bf}.
proof.
  proc; inline [-tuple] Init1.init IDCPA_QROM(A, GPV(E)).main.
  swap{1} 7 2; swap{1} [3..5] 3; wp. 
  rnd; wp; conseq (_: b2{1} = b{2} /\ ={IDCPA.id, IDCPA.log}) => />.
  by sim.  
qed.

local lemma pr_GI1 &m lam:
  0.0 <= lam <= 1.0 => 
  Pr[G(Init1).main0(lam) @ &m : res /\ (G.bf IDCPA.id /\ forall id', id' \in IDCPA.log => !G.bf id')] =
  (lam * (1.0 -lam)^qe) * Pr[IDCPA_QROM(A,GPV(E)).main() @ &m : res].
proof.
move=> lam_bound.
have -> : Pr[G(Init1).main0(lam) @ &m : res /\ (G.bf IDCPA.id /\ forall id', id' \in IDCPA.log => !G.bf id')] =
          Pr[G1.main(lam) @ &m : res /\ (G.bf IDCPA.id /\ forall id', id' \in IDCPA.log => !G.bf id')].
+ by byequiv GI1_G1.
byphoare (:(glob A, glob E) = (glob A, glob E){m} /\ lam_ = lam==> _) => //.
proc. 
seq 1 : b2 (Pr[IDCPA_QROM(A, GPV(E)).main() @ &m : res]) (lam*(1.0-lam)^qe)
        _ 0.0 
       (!IDCPA.id \in IDCPA.log /\ uniq IDCPA.log /\ size IDCPA.log = qe /\ lam_ = lam).
+ by call A_wf; auto.
+ call (: (glob A, glob E) = (glob A, glob E){m} ==> res); 2: by auto.
  by bypr => &m0 /> ??; byequiv => //; sim.
+ rnd (fun t => t IDCPA.id /\ forall id', id' \in IDCPA.log => ! t id').
  by skip => /> &1 hid hu <- _; apply pr_dbfun_l_eq.
+ by conseq (:false) => // />.
smt().
qed.

local lemma pr_GI1t &m lam: 
  0.0 <= lam <= 1.0 => 
  Pr[G(Init1).main0(lam) @ &m : G.bf IDCPA.id /\ forall id', id' \in IDCPA.log => !G.bf id'] =
  (lam * (1.0 -lam)^qe).
proof.
move=> lam_bound.
have -> : Pr[G(Init1).main0(lam) @ &m : G.bf IDCPA.id /\ forall id', id' \in IDCPA.log => !G.bf id'] =
          Pr[G1.main(lam) @ &m : G.bf IDCPA.id /\ forall id', id' \in IDCPA.log => !G.bf id'].
+ by byequiv GI1_G1.
byphoare (:(glob A, glob E) = (glob A, glob E){m} /\ lam_ = lam ==> _) => //.
proc.
seq 1 : true 1.0 (lam*(1.0-lam)^qe)
        _ 0.0 
       (!IDCPA.id \in IDCPA.log /\ uniq IDCPA.log /\ size IDCPA.log = qe /\ lam_ = lam).
+ by call A_wf; auto.
+ islossless.
  + by apply (guess_ll (<:Wrap(A, QRO, IDCPA(Wrap(A, QRO), GPV(E, QRO)).E).Hc)
                       (<: Wrap(A, QRO, IDCPA(Wrap(A, QRO), GPV(E, QRO)).E).Oc)); islossless.
  + by apply enc_ll.
  by apply (choose_ll (<:Wrap(A, QRO, IDCPA(Wrap(A, QRO), GPV(E, QRO)).E).Hc)
                      (<: Wrap(A, QRO, IDCPA(Wrap(A, QRO), GPV(E, QRO)).E).Oc)); islossless.
+ rnd (fun t => t IDCPA.id /\ forall id', id' \in IDCPA.log => ! t id').
  by skip => /> &1 hid hu <-; apply pr_dbfun_l_eq.
+ by conseq (:false) => // />.
smt().
qed.

local lemma l1 &m lam:
  0.0 < lam <= 1.0 => 
  `|Pr[G(Init1).main(lam) @ &m : res] - 0.5| >= 
    lam * `|Pr[IDCPA_QROM(A,GPV(E)).main() @ &m : res] - 0.5| - lam^2 * qe%r.
proof.
  move=> [hlam0 hlam1]; have hlam' :  0.0 <= lam <= 1.0 by smt().
  pose eps := `|Pr[IDCPA_QROM(A, GPV(E)).main() @ &m : res] - 1%r / 2%r|.
  apply (ler_trans ((lam * (1.0 - qe%r*lam)) * eps)).
  + have -> : lam * (1%r - qe%r * lam) * eps = lam * eps - lam ^ 2 * qe%r * eps by ring.
    apply ler_sub => //; rewrite -mulrA ler_pmul2l; 1: by apply expr_gt0.
    by rewrite -{2}(mulr1 qe%r) ler_wpmul2l;[ smt(ge0_qe) | smt(mu_bounded)].
  have ->:  
   Pr[G(Init1).main(lam) @ &m : res] - 0.5 =
     (lam * (1.0-lam)^qe) * (Pr[IDCPA_QROM(A,GPV(E)).main() @ &m : res] - 0.5).
  + rewrite (pr_split lam Init1); 2: by sim.
    + islossless => *. 
    by rewrite pr_GI1 1:// pr_GI1t 1://; ring.
  have -> : `|lam * (1%r - lam) ^ qe * (Pr[IDCPA_QROM(A, GPV(E)).main() @ &m : res] - 1%r / 2%r)| = lam * (1%r - lam) ^ qe * eps.
  + rewrite /eps; smt(expr_ge0).
  apply ler_wpmul2r; 1:smt(); apply ler_wpmul2l; 1: smt().
  apply (le_binomial _ _ hlam' ge0_qe).
qed.

local module Init2 = {
  proc init(h:identity -> pkey, lam_:real) = {
    var bf, y;
    y <$ dpkey;
    bf <$ dbfun lam_;
    h <- fun m => if bf m then y else h m;
    return (bf, h);
  }
}.

local hoare hoare_choose : 
   Wrap(A, QRO, IDCPA(Wrap(A, QRO), GPV(E, QRO)).E).choose :
    IDCPA.log = [] /\
    QRO.ch = 0 ==>
    size IDCPA.log = Wrap.ce /\
    Wrap.ce <= cqe /\ Wrap.ch <= cqh /\
    QRO.ch = Wrap.ce + Wrap.ch.
proof.
  conseq (:IDCPA.log = [] /\ QRO.ch = 0 ==>
           size IDCPA.log = Wrap.ce /\ QRO.ch = Wrap.ce + Wrap.ch)
         (hoare_bound_c 
            (<:QRO)
            (<:IDCPA(Wrap(A, QRO), GPV(E, QRO)).E)). smt(). 
  proc; call (:size IDCPA.log = Wrap.ce /\ QRO.ch = Wrap.ce + Wrap.ch).
  + by proc; inline *; auto => /> /#.
  + by proc; inline *; auto => /> /#.
  by auto.
qed.

local hoare hoare_guess ke kh kch : 
   Wrap(A, QRO, IDCPA(Wrap(A, QRO), GPV(E, QRO)).E).guess :
    size IDCPA.log = Wrap.ce /\
    Wrap.ce = ke /\ Wrap.ch = kh /\
    QRO.ch = kch ==>
    size IDCPA.log = Wrap.ce /\
    Wrap.ce <= ke + gqe /\ Wrap.ch <= kh + gqh /\
    QRO.ch = kch + (Wrap.ce - ke) + (Wrap.ch - kh).
proof.
  conseq (:size IDCPA.log = Wrap.ce /\ Wrap.ce = ke /\ Wrap.ch = kh /\ QRO.ch = kch ==>
           size IDCPA.log = Wrap.ce /\ QRO.ch = kch + (Wrap.ce - ke) + (Wrap.ch - kh))
         (hoare_bound_g 
            (<:QRO)
            (<:IDCPA(Wrap(A, QRO), GPV(E, QRO)).E) ke kh). smt(). done.
  proc (size IDCPA.log = Wrap.ce /\ QRO.ch = kch + (Wrap.ce - ke) + (Wrap.ch - kh)).
  + smt(). + smt().
  + by proc; inline *; auto => /> /#.
  by proc; inline *; auto => /> /#.
qed.

local hoare hoare_bound : 
   IDCPA(Wrap(A, QRO), GPV(E, QRO)).main : QRO.ch = 0 ==> size IDCPA.log <= qe /\ QRO.ch <= q.
proof.
  proc.
  ecall (hoare_guess Wrap.ce Wrap.ch QRO.ch).
  inline GPV(E, QRO).enc; wp.
  call(:true).
  inline QRO.h; wp.
  rnd; call hoare_choose; inline *; auto => /> /#.
qed.

local lemma pr_size (p : bool -> bool) (I<:Init{-A,-E,-QRO}) &m lam: 
  Pr[G(I).main0(lam) @ &m : p res /\ G.bf IDCPA.id /\ forall id', id' \in IDCPA.log => !G.bf id'] = 
  Pr[G(I).main0(lam) @ &m : p res /\ good G.bf IDCPA.id IDCPA.log].
proof.
  rewrite /good /=.
  byequiv => //.
  conseq (_: _ ==> ={res, G.bf, IDCPA.id, IDCPA.log}) _ (_: true ==> size IDCPA.log <= qe) => //; last by sim.
  proc. call hoare_bound.
  by inline *; call (:true);auto.
qed.

local module ASCDr (H:QRO) = {
  proc main() = {
    var b;
    b <@ IDCPA(Wrap(A,H), GPV(E,H)).main();
    return (b, IDCPA.id, IDCPA.log);
  }
}.

local module ASCDt (H:QRO) = {
  proc main() = {
    var b;
    b <@ IDCPA(Wrap(A,H), GPV(E,H)).main();
    return (true, IDCPA.id, IDCPA.log);
  }
}.
 
local lemma l2 &m lam :
  0.0 <= lam <= 1.0 => 
  `|Pr[G(Init2).main(lam) @ &m : res] - Pr[G(Init1).main(lam) @ &m : res] | <=
   (2%r * q%r + qe%r + 1%r) / 4.0 * lam ^2.
proof.
  move=> lam_bound.
  rewrite (pr_split lam Init2).
  + by islossless. + by sim.
  rewrite (pr_split lam Init1).
  + by islossless. + by sim.
  rewrite (pr_size (fun _ => true) Init1) (pr_size (fun _ => true) Init2).
  rewrite (pr_size idfun Init1) (pr_size idfun Init2) /idfun /=.
  apply (ler_trans 
      (0.5 * `| Pr[G(Init1).main0(lam) @ &m : good G.bf IDCPA.id IDCPA.log] -
                Pr[G(Init2).main0(lam) @ &m : good G.bf IDCPA.id IDCPA.log] | 
           + `| Pr[G(Init1).main0(lam) @ &m : res /\ good G.bf IDCPA.id IDCPA.log] -
                Pr[G(Init2).main0(lam) @ &m : res /\ good G.bf IDCPA.id IDCPA.log] |)); 1: smt().
  have -> : Pr[G(Init1).main0(lam) @ &m : res /\ good G.bf IDCPA.id IDCPA.log] =
            Pr[SCD(ASCDr)._F0(lam) @ &m : res].
  + byequiv => //; proc; inline ASCDr(QRO).main Init1.init; swap{2} 3 2; swap{2} 1 1.
    by rnd{2}; wp; conseq (_: ={IDCPA.id, IDCPA.log} /\ G.bf{1} = SCD.bf{2} /\ b2{1} = b{2}) => //; sim.
  have ->: Pr[G(Init2).main0(lam) @ &m : res /\ good G.bf IDCPA.id IDCPA.log] =
         Pr[SCD(ASCDr)._F1(lam) @ &m : res].
  + byequiv => //; proc; inline ASCDr(QRO).main Init2.init. swap{2} 1 2. 
    by wp; conseq (_: ={IDCPA.id, IDCPA.log} /\ G.bf{1} = SCD.bf{2} /\ b2{1} = b{2}) => //; sim.
  have -> : Pr[G(Init1).main0(lam) @ &m : good G.bf IDCPA.id IDCPA.log] =
            Pr[SCD(ASCDt)._F0(lam) @ &m : res].
  + byequiv => //; proc; inline ASCDt(QRO).main Init1.init. swap{2} 3 2; swap{2} 1 1.
    by rnd{2}; wp; conseq (_: ={IDCPA.id, IDCPA.log} /\ G.bf{1} = SCD.bf{2} /\ b2{1} = b{2}) => //; sim.
  have ->: Pr[G(Init2).main0(lam) @ &m : good G.bf IDCPA.id IDCPA.log] =
         Pr[SCD(ASCDt)._F1(lam) @ &m : res].
  + byequiv => //; proc; inline ASCDt(QRO).main Init2.init. swap{2} 1 2. 
    by wp; conseq (_: ={IDCPA.id, IDCPA.log} /\ G.bf{1} = SCD.bf{2} /\ b2{1} = b{2}) => //; sim.
  have := advantage q lam ASCDr &m lam_bound _. 
  + proc; inline ASCDr(QRO).main; wp.
    by call hoare_bound; inline *; auto.
  have /# := advantage q lam ASCDt &m lam_bound _.
  proc; inline ASCDt(QRO).main; wp.
  by call hoare_bound; inline *; auto.
qed.

import Bool.
local module S = {
  proc sample1 () = {
    var r;
    r <$ dpkey; 
    return r;
  }
  proc sample2 (mpk:mpkey, msk:mskey) = {
    var z;
    z <$ sampleD;
    return f mpk z;
  }
}.

module type OrclPK  = {
  proc pkey(id:identity) : pkey
}.

quantum module type AdvIDCPA_QROM_aux (H : QRO, O : OrclIBE, P:OrclPK)  = {
  proc choose (mpk : mpkey): identity * msg * msg 
  
  proc guess (c : cipher): bool
}.

local lemma l3 &m lam : 
   Pr[G(Init2).main(lam) @ &m : res] = Pr[CPA(B(A), ES(E)).main(lam) @ &m : res].
proof.
byequiv => //; proc.
inline *.
seq 12 10 : 
  ((forall id', B.bf id' => pk = (mpk0, QRO.h id')){2} /\
   (forall id', !G.bf{1} id' => QRO.h{1} id' = f IDCPA.mpk{1} (B.he{2} id')) /\
   ={QRO.h, IDCPA.log, glob A, glob E} /\ G.bf{1} = B.bf{2} /\ IDCPA.mpk{1} = mpk0{2} /\ 
   (IDCPA.mpk,IDCPA.msk){1} \in kg).
+ conseq />.
  swap{1} 11 -10. swap{1} [4..5] 3. 
  wp.
  rnd (fun (h: identity -> pkey) => fun id => finv msk{2} (h id))
      (fun (h: identity -> skey) => fun id => f mpk{2} (h id)).
  rnd; wp.
  seq 1 1: (i{2} = lam_{1} /\ keys{1} = (mpk, msk){2} /\ keys{1} \in kg).
  + by auto => /> /#. 
  swap{1} 4 -3; wp.
  conseq (: i{2} = lam_{1} /\ keys{1} = (mpk{2}, msk{2}) /\ (keys{1} \in kg) /\
              y{1} = f mpk{2} sk0{2}).
  + move=> /> &1 &2 hin sk bf hbf; split.
    + by move=> he _; apply fun_ext => z; rewrite (finv_f _ _ hin).
    move=> _; split.
    + move=> *; apply dfskey_dfpkey.
    move=> _ h _; split.
    + by apply fun_ext => z; rewrite (f_finv _ _ hin).
    move=> _; split.
    + by move=> z _; rewrite (f_finv _ _ hin).
    by apply fun_ext => z; rewrite (f_finv _ _ hin).
  conseq (: keys{1} \in kg /\ keys{1} = (mpk, msk){2} ==> y{1} = f mpk{2} sk0{2}) => //.
  transitivity{1} {y <@ S.sample1(); }
     (true ==> ={y})
     (keys{1} \in kg /\ keys{1} = (mpk, msk){2} ==> y{1} = f mpk{2} sk0{2}) => //.
  + smt().
  + by inline *;auto.
  transitivity{1}{y <@ S.sample2(keys);}
     (keys{2} \in kg ==> ={y})
     (keys{1} = (mpk{2}, msk{2}) ==> y{1} = f mpk{2} sk0{2}) => //; last by inline *; auto.
  + smt().
  call (: arg{2} \in kg ==> ={res}) => //.
  bypr (res{1}) (res{2}) => //.
  move=> &1 &2 a harg. 
  have -> : Pr[S.sample1() @ &1 : res = a] = mu1 dpkey a.
  + by byphoare => //; proc; rnd; skip.
  have -> : Pr[S.sample2(mpk{2}, msk{2}) @ &2 : res = a] = mu1 (dmap sampleD (f mpk{2})) a.
  + by byphoare (_: arg = (mpk,msk){2} ==> res = a) => //; proc; rnd; skip => />; rewrite dmap1E.
  congr;apply eq_funi_ll. 
  + by apply is_full_funiform; [apply dpkey_fu | apply dpkey_uni].
  + by apply dpkey_ll.
  + by case: (arg{2}) harg; apply sampleDf_funi.
  by apply/dmap_ll/sampleD_ll.

seq 15 6 : ( (!G.bf IDCPA.id \/ exists m', m' \in IDCPA.log /\ G.bf m'){1} = 
              (!B.bf IDCPA.id \/ exists m', m' \in IDCPA.log /\ B.bf m'){2} /\
            (!(!G.bf IDCPA.id \/ exists m', m' \in IDCPA.log /\ G.bf m'){1} => 
             ={IDCPA.id,m1 ,m2} /\ (IDCPA.b, IDCPA.b', G.bf){1} = (b, b'0,B.bf){2})); last first.
+ wp; sp; if{1}.
  + by rcondf{2} 1 => *; auto => /> /#.
  rcondt{2} 1 => *; 1: by auto => /> /#.
  by rnd (fun b1 => !(b{2} ^^ b1)); skip => /> /#.

seq 5 2: 
  ( (forall (id' : identity), B.bf{2} id' => pk{2} = (mpk0{2}, QRO.h{2} id')) /\
    (forall (id' : identity), ! G.bf{1} id' => QRO.h{1} id' = f IDCPA.mpk{1} (B.he{2} id')) /\
     ={QRO.h} /\  G.bf{1} = B.bf{2} /\ IDCPA.mpk{1} = mpk0{2} /\ (IDCPA.mpk{1}, IDCPA.msk{1}) \in kg /\
    (exists m', m' \in IDCPA.log /\ G.bf m'){1} = (exists m', m' \in IDCPA.log /\ B.bf m'){2} /\
    (!(exists m', m' \in IDCPA.log /\ G.bf m'){1} => 
        ={IDCPA.id,m1 ,m2, glob A, glob E, IDCPA.log} /\ G.bf{1} = B.bf{2})).
+ wp.
  call (: (exists m', m' \in IDCPA.log /\ B.bf m'), 
          (={IDCPA.log, QRO.h} /\ G.bf{1} = B.bf{2} /\
           (forall id', !G.bf{1} id' => QRO.h{1} id' = f IDCPA.mpk{1} (B.he{2} id')) /\
          (IDCPA.mpk,IDCPA.msk){1} \in kg),
          (exists m', m' \in IDCPA.log /\ G.bf m'){1} =
          (exists m', m' \in IDCPA.log /\ B.bf m'){2}
          ).
  + by apply choose_ll.
  + by proc; inline *; wp; skip => />; smt(finv_f).
  + by move=> &2 ?; proc; inline *; auto; smt().
  + by move=> &1; proc; inline *; auto; smt().
  + by proc; inline*; auto. 
  + by move=> *;proc; inline*; auto => />.
  + by move=> *;proc; inline*; auto => />.
  by wp;skip => /> * /#. 
wp; case: ((!G.bf IDCPA.id \/ exists (m' : identity), (m' \in IDCPA.log) /\ G.bf m'){1}).
+ call{1} (: (!G.bf IDCPA.id \/ exists (m' : identity), (m' \in IDCPA.log) /\ G.bf m') ==> 
             (!G.bf IDCPA.id \/ exists (m' : identity), (m' \in IDCPA.log) /\ G.bf m')).
  conseq (:true ==> true) (: _ ==> _) => //.
  + proc (!G.bf IDCPA.id \/ exists (m' : identity), (m' \in IDCPA.log) /\ G.bf m') => //. 
    + by proc; inline *; auto; smt().
    by move=> *;proc; inline*;auto => />.
  by apply (guess_ll (<:Wrap(A, QRO, IDCPA(Wrap(A, QRO), GPV(E, QRO)).E).Hc)
                  (<:Wrap(A, QRO, IDCPA(Wrap(A, QRO), GPV(E, QRO)).E).Oc)); islossless.
+ call{2} (: (!B.bf IDCPA.id \/ exists (m' : identity), (m' \in IDCPA.log) /\ B.bf m') ==> 
             (!B.bf IDCPA.id \/ exists (m' : identity), (m' \in IDCPA.log) /\ B.bf m')).
  + conseq (:true ==> true) (: _ ==> _) => //.
    + proc (!B.bf IDCPA.id \/ exists (m' : identity), (m' \in IDCPA.log) /\ B.bf m') => //. 
      + by proc; inline *; auto; smt().
      by move=> *;proc; inline*;auto => />.
    by apply (guess_ll QRO (<:B(A).E0)); islossless.
  wp;call{1} enc_ll; call{2} enc_ll.
  by wp; rnd; skip => /> /#.
call (: (exists m', m' \in IDCPA.log /\ B.bf m'), 
        (={IDCPA.log, QRO.h} /\ G.bf{1} = B.bf{2} /\
         (forall id', !G.bf{1} id' => QRO.h{1} id' = f IDCPA.mpk{1} (B.he{2} id')) /\
        (IDCPA.mpk,IDCPA.msk){1} \in kg),
        (exists m', m' \in IDCPA.log /\ G.bf m'){1} =
        (exists m', m' \in IDCPA.log /\ B.bf m'){2}
        ).
+ by apply guess_ll.
+ by proc; inline *; wp; skip => />; smt(finv_f).
+ by move=> &2 ?; proc; inline *; auto; smt().
+ by move=> &1; proc; inline *; auto; smt().
+ by proc; inline*; auto => />.
+ by move=> *;proc; inline *; auto => />.
+ by move=> *;proc; inline *; auto => />.
wp; call(:true); wp; rnd; skip => /#.
qed.

local lemma l4 &m lam: 
  0.0 < lam <= 1.0 =>
  lam * `|Pr[IDCPA_QROM(A,GPV(E)).main() @ &m : res] - 0.5|
    - (2%r * q%r + 5.0* qe%r + 1%r) / 4.0 * lam ^2
    <= `|Pr[CPA(B(A), ES(E)).main(lam) @ &m : res]- 0.5|.
proof. move: (l1 &m) (l2 &m) (l3 &m) => /#. qed.

local lemma conclusion &m:
  let eps = `|Pr[IDCPA_QROM(A,GPV(E)).main() @ &m : res] - 0.5| in
  let lam = (2.0 * eps) / (2%r * q%r + 5.0*qe%r + 1%r) in 
  eps^2 / (2%r * q%r + 5.0*qe%r + 1%r) <=
     `|Pr[CPA(B(A), ES(E)).main(lam) @ &m : res]- 0.5|.
proof.
  move=> eps; case: (eps = 0%r).
  + by move: eps => />; rewrite expr2 /= /#.
  move=> heps lam.
  have h1 : 0%r < (2%r * q%r + 5%r * qe%r + 1%r) by smt(ge0_qh ge0_qe).
  have := l4 &m lam _.
  + rewrite ler_pdivr_mulr => //; smt(mu_bounded ge0_qe ge0_qh).
  apply/ler_trans/lerr_eq; rewrite -/eps /lam;field => //.
  smt(). 
qed.

end section.

