require import AllCore List Distr DBool DList DProd CHoareTactic.
require (*  *) T_QROM T_EUF T_PERM.
(*   *) import StdOrder RField RealOrder StdBigop Bigreal DInterval.

(* --------------------------------------------------------------------------- *)

clone import T_EUF as EUF.

clone import T_QROM as QROM with
  type from <- msg.

clone include T_PERM with 
   type pkey  <- pkey,
   type skey  <- skey,
   type dom   <- sign,
   type codom <- hash.

(* --------------------------------------------------------------------------- *)
(* Security definition of existencial unforgeability in the QROM  *)

module type Sign_QROM (H:QRO) = {
  proc kg() : pkey * skey 
  
  proc sign(sk : skey, m : msg) : sign 
  
  proc verify(pk : pkey, m : msg, s : sign) : bool 
}.

quantum module type AdvEUF_QROM (H:QRO) (S:OrclSign) = {
  proc main(pk:pkey) : msg * sign
}.

module Wrap (A:AdvEUF_QROM) (H:QRO) (S:OrclSign) = {
  var ch : int
  var cs : int

  module Hc = {
    quantum proc h {x:msg} = {
      quantum var h;
      ch <- ch+1;
      h <@ H.h{x};
      return h;
    }
  } 

  module Sc = {
    proc sign (m:msg) = {
      var s;
      cs <- cs+1;
      s <@ S.sign(m);
      return s;
    }
  }


  proc main(pk:pkey) = {
    var ms : msg * sign;
    ch <- 0; cs <- 0;
    ms <@ A(Hc, Sc).main(pk); 
    return ms;
  } 
}.

module EUF_QROM (A:AdvEUF_QROM) (S:Sign_QROM) = {
  proc main() = {
    var b;
    QRO.init();    
    b <@ EUF(Wrap(A, QRO), S(QRO)).main();
    return b;
  }
}.

(* --------------------------------------------------------------------------- *)
(* Security definition of existencial unforgeability in the QROM  *)

module (FDH:Sign_QROM) (H:QRO) = {
  proc kg () = {
    var k;
    k <$ kg;
    return k;
  }

  proc sign(sk:skey, m:msg) = {
    var h;
    h <@ H.h{m};
    return finv sk h;
  }

  proc verify(pk:pkey, m:msg, s:sign) = {
    var h;
    h <@ H.h{m};
    return h = f pk s;
  }

}.

(* --------------------------------------------------------------------------- *)
(* Maximal number of queries to the sign/hash oracle *)
op qs : { int | 0 < qs } as gt0_qs.
op qh : { int | 0 <= qh } as ge0_qh.

op q = qs + qh + 1.

(* --------------------------------------------------------------------------- *)
(* Generic start of the proof used for OW and ClawFree *)

section. 

declare module A <: AdvEUF_QROM { -QRO, -EUF, -Wrap}.

declare axiom hoare_bound (H<:QRO{-A,-Wrap}) (S<:OrclSign{-A,-Wrap}) : 
  hoare [Wrap(A, H, S).main : true  ==> Wrap.cs <= qs /\ Wrap.ch <= qh].

hoare hoare_bound1 : Wrap(A, QRO, EUF(Wrap(A, QRO), FDH(QRO)).Os).main : 
     QRO.ch = 0 /\ size EUF.log = 0 ==>
     QRO.ch <= qs + qh /\ size EUF.log <= qs.
proof.
  conseq (: true ==> Wrap.cs <= qs /\ Wrap.ch <= qh) 
         (: QRO.ch = 0 /\ size EUF.log = 0 ==> QRO.ch = Wrap.cs + Wrap.ch /\
                                                        size EUF.log = Wrap.cs).
  + smt().
  + proc.
    call (: QRO.ch = Wrap.cs + Wrap.ch /\ size EUF.log = Wrap.cs).
    + by proc; inline *; auto => /> *; split; ring.
    + by proc; inline *; auto => /> *; ring.
    by auto.
  by apply (hoare_bound QRO (<:EUF(Wrap(A, QRO), FDH(QRO)).Os)).
qed.
 
hoare EUF_QROM_bound : EUF_QROM(A,FDH).main : 
   true ==> res => ! (EUF.m \in EUF.log) /\ size EUF.log <= qs /\ QRO.ch <= q.
proof.
  proc. inline EUF(Wrap(A, QRO), FDH(QRO)).main FDH(QRO).verify QRO.h; wp.
  call hoare_bound1.
  by inline *;auto => /> /#.
qed.

end section.

abstract theory START.

module EUF_QROM' (A:AdvEUF_QROM) = {
  var bf : msg -> bool

  proc main(lam_:real) = {
    var b;
    bf <$ dbfun lam_;
    b <@ EUF_QROM(A, FDH).main();
    return b /\ (bf EUF.m /\ (forall m', m' \in EUF.log => !bf m') /\ size EUF.log <= qs );
  }
}.

section.
 
declare module A <: AdvEUF_QROM { -QRO, -EUF, - EUF_QROM'}.

declare axiom hoare_bound (H<:QRO{-A, -Wrap}) (S<:OrclSign{-A, -Wrap}) :
  hoare[ Wrap(A, H, S).main : true ==> Wrap.cs <= qs /\ Wrap.ch <= qh].

lemma l1 lam &m:
  0%r <= lam <= 1%r =>
  Pr[EUF_QROM'(A).main(lam) @ &m : res] >=
    lam * (1%r - lam)^qs * Pr[EUF_QROM(A,FDH).main() @ &m : res].
proof.
move=> lam_bound.
byphoare (:(glob A){m} = glob A /\ lam_ = lam ==> _) => //.
proc.
swap 1 1.
seq 1 : b Pr[EUF_QROM(A,FDH).main() @ &m : res] (lam * (1%r - lam) ^ qs) 
          _ 0%r (lam_ = lam /\ (b => !EUF.m \in EUF.log /\ size EUF.log <= qs)).
+ by call (EUF_QROM_bound A hoare_bound); skip => /> /#.
+ call (: (glob A){m} = glob A ==> res); 2: by auto.
  bypr => &m0 ?.
  byequiv (: ={glob A} ==> ={res}) => //; 1: sim.
+ rnd (fun t => t EUF.m /\ forall (m' : msg), m' \in EUF.log => ! t m').
  by skip => /> &hr h /h /> *; apply: pr_dbfun_l_pow.
+ by auto.
smt().
qed.

end section.
end START.

import MUFF.
(* --------------------------------------------------------------------------*)
op [lossless uniform full] dsign : sign distr.
(* FIXME: this should be provable because f is bijective *)
axiom dhash_dsign h s: mu1 dhash h = mu1 dsign s.

op dfsign : (msg -> sign) distr = dfun (fun _ => dsign).

lemma dfsign_ll: is_lossless dfsign.
proof. apply dfun_ll => ?;apply dsign_ll. qed.

lemma dfsign_uni: is_uniform dfsign.
proof. apply dfun_uni => ?; apply dsign_uni. qed.

lemma dfsign_fu: is_full dfsign.
proof. apply dfun_fu => ?; apply dsign_fu. qed.

hint solve 0 random : dfsign_ll dfsign_uni dfsign_fu.

lemma dfsign_dfhash (hs: msg -> sign) (hh:msg -> hash) : mu1 dfsign hs = mu1 dfhash hh.
proof. by rewrite !dfun1E;apply BRM.eq_big => //= x _; rewrite eq_sym; apply dhash_dsign. qed.

(* --------------------------------------------------------------------------- *)
(* First proof : reducing to claw free                                         *)
(* --------------------------------------------------------------------------- *)

abstract theory FDH_CF.

clone import T_ClawFree.

op lam : real.
axiom lam_bound : 0%r < lam < 1%r.

module B (A:AdvEUF_QROM) = { 
  import var EUF

  var hs : msg -> sign
  var bf : msg -> bool

  module Os = {
    proc sign(m:msg) = { 
      log <- m :: log;
      return hs m; 
    }
  }

  proc main(pk:pkey) = {
    var m, s;
    bf <$ dbfun lam;
    hs <$ dfsign;
    QRO.h <- (fun m => if bf m then P2.f pk (hs m) else f pk (hs m)); 
    log <- [];
    (m,s) <@ A(QRO, Os).main(pk);
    return (s, hs m); 
  }

}.

section.

declare module A <: AdvEUF_QROM { -EUF, -QRO, -B, -Wrap}.

declare axiom hoare_bound (H<:QRO{-A, -Wrap}) (S<:OrclSign{-A, -Wrap}) :
  hoare[ Wrap(A, H, S).main : true ==> Wrap.cs <= qs /\ Wrap.ch <= qh].

declare axiom A_ll (H <: QRO{-A}) (S <: OrclSign{-A}) : 
 islossless S.sign => islossless H.h => islossless A(H, S).main.

local clone import START.

import var EUF.

local lemma l3 &m : 
  Pr[EUF_QROM'(A).main(lam) @ &m : res] <= Pr[ClawFree(B(A)).main() @ &m : res].
proof.
  byequiv => //; proc.
  inline *; wp.
  call (: (exists m', m' \in log /\ B.bf m'), 
          (={log, QRO.h} /\ EUF_QROM'.bf{1} = B.bf{2} /\
          QRO.h{2} = (fun m => let hs = B.hs{2} m in if B.bf{2} m then P2.f pk{1} hs else f pk{1} hs) /\ 
          (pk,sk){1} \in kg),
          (exists m', m' \in log /\ EUF_QROM'.bf m'){1} = (exists m', m' \in log /\ B.bf m'){2}).
  + by apply A_ll.
  + by proc; inline *; auto => />; smt (finv_f).
  + by move=> *; proc; inline *; auto => /> /#.
  + by move=> *; proc; inline *;auto => /> /#.
  + by proc; inline *; auto.
  + by move=> *; proc; inline *; auto => /> /#.
  + by move=> *; proc; inline *; auto.
  swap{1} 4 -3; wp.
  rnd (fun h  => fun m => if B.bf m then P2.finv sk (h m) else finv sk (h m)){2}
      (fun hs => fun m => if B.bf m then P2.f pk (hs m) else f pk (hs m)){2}.
  auto => /> {&m} k hk t _; split.
  + move=> hs _; apply fun_ext; smt (P2.finv_f finv_f).
  smt (dfsign_dfhash P2.f_finv f_finv).
qed.

lemma conclusion &m : 
   Pr[EUF_QROM(A, FDH).main() @ &m : res] <= 
    Pr[ClawFree(B(A)).main() @ &m : res] / (lam * (1%r - lam) ^ qs).
proof.
  have : lam * (1%r - lam) ^ qs * Pr[EUF_QROM(A, FDH).main() @ &m : res] <= 
    Pr[ClawFree(B(A)).main() @ &m : res].
  + move: (l1 A hoare_bound lam &m) lam_bound (l3 &m) => /#.
  rewrite -ler_pdivl_mull; smt(expr_gt0 lam_bound).
qed.

end section.
end FDH_CF.

(* The minimun of the above bound is found for lam = 1/(qs+1) *)
abstract theory FDH_CF_instanciate.

clone include FDH_CF with
  op lam = 1%r/(qs+1)%r
  proof lam_bound by smt(gt0_qs).

end FDH_CF_instanciate.

(* --------------------------------------------------------------------------- *)
(* Second proof : reducing to OW, proof based on semi-constant                  *)
(* --------------------------------------------------------------------------- *)

abstract theory FDH_OW_semi_constant.

clone import T_OW with 
  type init <- real,
  op dcodom <- dhash.

module B(A:AdvEUF_QROM) : AdvOW = {
  import var EUF
  var hs : msg -> sign
  var bf : msg -> bool
  module Os = {
    proc sign(m:msg) = { 
      log <- m :: log;
      return hs m; 
    }
  }

  proc main(pk:pkey, y:hash, lam:real) : sign = {
    var m,s;
    bf <$ dbfun lam;
    hs <$ dfsign;
    QRO.h <- fun m => if bf m then y else f pk (hs m);
    EUF.log <- [];
    (m,s) <@ A(QRO, Os).main(pk);
    return s;
  }
}.

clone import SemiConstDistr with
    op k <- qs.

section OW.

declare module A <: AdvEUF_QROM { -QRO, -EUF, -B, -Wrap, -SCD}.

declare axiom A_ll (H <: QRO{-A}) (S <: OrclSign{-A}) : 
  islossless S.sign => islossless H.h => islossless A(H, S).main.

declare axiom hoare_bound (H<:QRO{-A, -Wrap}) (S<:OrclSign{-A, -Wrap}) :
  hoare[ Wrap(A, H, S).main : true ==> Wrap.cs <= qs /\ Wrap.ch <= qh].

local clone import START.

local module (ASCD:AdvSCD) (H:QRO) = {
  import var EUF

  module Os = {
    proc sign(m:msg) = {
      var hm;
      log <- m::log;
      hm  <@ H.h{m};
      return finv sk hm;
    }
  }

  proc main() = {
    var b, s, hm;
    (pk, sk) <$ kg;
    log <- [];
    (m,s) <@ Wrap(A, H, Os).main(pk);
    hm <@ H.h{m};
    b <- hm = f pk s;
    return (b, m, log);
  }
}.

import var EUF B SCD.

local lemma l3 lam &m : 
  Pr[EUF_QROM'(A).main(lam) @ &m : res] =
  Pr[SCD(ASCD)._F0(lam) @ &m : res].
proof.
  byequiv => //.
  proc; inline *; wp.
  call (: ={QRO.h, sk, log}). 
  + by proc ; inline *; auto.
  + by proc; inline *;auto => />;skip => />.
  swap{2} 4 1; auto; rnd{2}; auto => /> /#.
qed.

local hoare hoare_bound1 : Wrap(A, QRO, ASCD(QRO).Os).main : 
  QRO.ch = 0  ==>
  QRO.ch <= qs + qh.
proof.
  conseq (: true ==> Wrap.cs <= qs /\ Wrap.ch <= qh) 
         (: QRO.ch = 0 ==> QRO.ch = Wrap.cs + Wrap.ch).
  + smt().
  + proc.
    call (: QRO.ch = Wrap.cs + Wrap.ch).
    + by proc; inline *; auto => /> *; ring.
    + by proc; inline *; auto => /> *; ring.
    by auto.
  by apply (hoare_bound QRO (<:ASCD(QRO).Os)).
qed.

local lemma l4 lam &m :
  0.0 <= lam <= 1.0 => 
  `| Pr[SCD(ASCD)._F0(lam) @ &m : res] - 
     Pr[SCD(ASCD)._F1(lam) @ &m: res] | 
   <= (2%r * q%r + qs%r + 1%r)/ 6%r * lam^2.
proof.
  move=> lam_bound.
  apply (advantage q lam ASCD &m lam_bound _).
  proc.
  inline ASCD(QRO).main QRO.h; wp.
  call hoare_bound1; inline *; auto => /> /#.
qed.

local lemma l5 lam &m :
  Pr[SCD(ASCD)._F1(lam) @ &m: res] <= Pr[OW(B(A)).main(lam) @ &m : res].
proof.
  byequiv (: ={glob A} /\ p{1} = i{2} ==> res{1} => res{2}) => //.
  proc; inline *; wp.
  (* Proof using upto bad *)
  call (: (exists m', m' \in log /\ B.bf m'), 
          (={log, QRO.h} /\ SCD.bf{1} = B.bf{2} /\
           (forall m', !SCD.bf{1} m' => QRO.h{1} m' = f pk{1} (hs{2} m')) /\
          (pk,sk){1} \in kg),
          (exists m', m' \in log /\ SCD.bf m'){1} =
          (exists m', m' \in log /\ B.bf m'){2}
          ).
  + exact A_ll. 
  + by proc; inline *; auto => />; smt(finv_f).  
  + by move=> *; proc; inline *; auto => /> /#.
  + by move=> *; proc; inline *; auto => /> /#.
  + proc; inline *; auto => />; skip => /#.
  + by move=> *; proc; inline *; auto => /> /#.
  + by move=> *; proc; inline *; auto => /> /#.
  swap{1}6 -5. swap{1} 5 -3; wp.
  rnd (fun (h:msg -> hash) => fun m => finv EUF.sk{1} (h m))
      (fun (h:msg -> sign) => fun m => f EUF.pk{1} (h m)).
  rewrite /good; auto => /> &2 k hk h _ bf _; split.
  + by move=> *; apply fun_ext => ?; smt(finv_f).
  smt(dfsign_dfhash f_finv finv_f).
qed.

lemma conclusion lam &m :
  0.0 < lam < 1.0 => 
  Pr[EUF_QROM(A,FDH).main() @ &m : res] <=
  Pr[OW(B(A)).main(lam) @ &m : res] / (lam * (1%r - lam) ^ qs) + 
   (2*qh + 3*qs + 3)%r/ 6%r * lam / (1%r - lam) ^ qs. 
proof. 
  move=> lam_bound.
  have : lam * (1%r - lam) ^ qs * Pr[EUF_QROM(A,FDH).main() @ &m : res] <=
         Pr[OW(B(A)).main(lam) @ &m : res] + (2%r * q%r + qs%r + 1%r)/ 6%r * lam^2. 
  + by move: (l1 A hoare_bound lam &m) lam_bound (l3 lam &m) (l4 lam &m) (l5 lam &m) => /#. 
  rewrite /q !fromintD -ler_pdivl_mull; 1: smt (expr_gt0).
  move=> h; apply/(ler_trans _ _ _ h)/lerr_eq; field => //; smt (expr_gt0).
qed.

(* Proof of the Zhandry's bound *)
lemma conclusion_z &m :
  let eps = Pr[EUF_QROM(A,FDH).main() @ &m : res] in
  let k = (2.0*qh%r + 9.0 * qs%r + 3.0)/6.0 in
  let lam = eps / (2.0 * k) in 
  eps ^ 2 / (4.0 * k) <= Pr[OW(B(A)).main(lam) @ &m : res].
proof.
  move=> eps k lam.
  case: (Pr[EUF_QROM(A, FDH).main() @ &m : res] = 0.0).
  + by move=> -> /=; rewrite expr0z /=; smt(mu_bounded).
  rewrite -/eps => h0eps.
  apply: ler_trans (l5 lam &m).
  have : Pr[SCD(ASCD)._F0(lam) @ &m : res] - (2%r * q%r + qs%r + 1%r)/ 6%r * lam^2 <= 
             Pr[SCD(ASCD)._F1(lam) @ &m : res].
  + by have := l4 lam &m; smt (mu_bounded gt0_qs ge0_qh).
  apply: ler_trans.
  rewrite -(l3 lam &m).
  apply (ler_trans 
     (lam * (1%r - lam) ^ qs * eps - (2%r * q%r + qs%r + 1%r) / 6%r * lam ^ 2)); last first.
  + by have := l1 A hoare_bound lam &m;smt(mu_bounded gt0_qs ge0_qh).
  apply (@ler_trans
    (lam * eps - qs%r * lam ^2 - (2%r * q%r + qs%r + 1%r) / 6%r * lam ^ 2)).
  + by apply lerr_eq; rewrite /lam /q /k !fromintD; field => //; smt(gt0_qs ge0_qh).
  rewrite ler_add2.
  apply (ler_trans (lam * (1%r -qs%r*lam) * eps)); last first.
  + apply ler_wpmul2r; 1: smt(mu_bounded).
    apply ler_wpmul2l; 1: smt(mu_bounded gt0_qs ge0_qh).
    smt (le_binomial mu_bounded gt0_qs ge0_qh).
  rewrite expr2. 
  have /# :  qs%r * (lam * lam) * eps <= qs%r * (lam * lam).
  rewrite -{2}(mulr1 (qs%r * (lam * lam))).
  by apply ler_wpmul2l; smt(mu_bounded gt0_qs ge0_qh).
qed.

end section OW.

end FDH_OW_semi_constant.

(* --------------------------------------------------------------------------- *)
(* Third proof : reducing to OW, proof based on small-range                    *)
(* --------------------------------------------------------------------------- *)
(*
abstract theory FDH_OW_SmallRange.

(* FIXME: be undep of lam *)

clone import T_OW with 
  type init <- int,
  op dcodom <- dhash.

clone import SmallRange.

module B (A:AdvEUF_QROM) : AdvOW = {
  import var EUF
  var hs : msg -> sign

  module Os = {
    proc sign(m:msg) = { 
      log <- m :: log;
      return hs m; 
    }
  }

  proc main(pk_:pkey, y:hash, r:int) = {
    var s, fr, rs2, rs, rh;
    log <- [];
    rs2 <$ dlist dsign (r-1);
    rs  <- witness :: rs2;
    rh  <- y :: map (f pk_) rs2;
    fr  <$ difun r; 
    hs <- fun x => nth witness rs (fr x); 
    QRO.h <- fun x => nth witness rh (fr x);
    (m,s) <@ A(QRO, Os).main(pk_);
    return s; 
  }
}.

section OW.

declare module A : AdvEUF_QROM { -QRO, -EUF, -B, -SR, -Wrap}.

axiom hoare_bound (H<:QRO{-A, -Wrap}) (S<:OrclSign{-A, -Wrap}) :
  hoare[ Wrap(A, H, S).main : true ==> Wrap.cs <= qs /\ Wrap.ch <= qh].

axiom A_ll (H <: QRO{-A}) (S <: OrclSign{-A}) : 
  islossless S.sign => islossless H.h => islossless A(H, S).main.

module EUF_QROM' (A:AdvEUF_QROM) = {

  proc main(r_:int) = {
    var b;
    SR.fr <$ difun r_; 
    b <@ EUF_QROM(A, FDH).main();
    return b /\ (SR.fr EUF.m = 0 /\ (forall m', m' \in EUF.log => SR.fr m' <> 0) );
  }
}.

lemma l1 r &m:
  1 <= r => let lam = inv r%r in
  Pr[EUF_QROM'(A).main(r) @ &m : res] >=
    lam * (1%r - lam)^qs * Pr[EUF_QROM(A,FDH).main() @ &m : res].
proof.
move=> hr lam. 
byphoare (:(glob A){m} = glob A /\ r_ = r ==> _) => //.
proc.
swap 1 1.
seq 1 : b Pr[EUF_QROM(A,FDH).main() @ &m : res] (lam * (1%r - lam) ^ qs) 
          _ 0%r (r_ = r /\ (b => !EUF.m \in EUF.log /\ size EUF.log <= qs)).
+ by call (EUF_QROM_bound A hoare_bound); skip => /> /#.
+ call (: (glob A){m} = glob A ==> res); 2: by auto.
  bypr => &m0 ?.
  byequiv (: ={glob A} ==> ={res}) => //; 1: sim.
+ rnd (fun t => t EUF.m = 0  /\ forall (m' : msg), m' \in EUF.log => t m' <> 0).
  skip => /> &hr h /h /> *.
  have /= h1 := dfunE_mem_le lam (fun _ => [0..r-1]) [EUF.m{hr}] EUF.log{hr} (fun _ i => i = 0) _ _ _.
  + by rewrite /= dinter_ll /#.
  + by rewrite /= dinter1E /#.
  + smt(). 
  have -> : 
    (fun (t : msg -> int) => t EUF.m{hr} = 0 /\ forall (m' : msg), m' \in EUF.log{hr} => t m' <> 0) = 
    (fun (f : msg -> int) =>
       (forall (x : msg), x = EUF.m{hr} => f x = 0) /\ forall (x : msg), x \in EUF.log{hr} => f x <> 0).
  + by apply fun_ext => z /#.
  apply: ler_trans h1.
  by rewrite expr1 ler_wpmul2l 1:/# ler_wiexpn2l; smt(size_ge0).
+ by auto.
smt().
qed.

local module (ASRr:AdvSRr) (H:SRr) = {
  var bad : bool
  import var EUF

  module Os = {
    proc sign(m:msg) = {
      var i, hm;
      log <- m::log;
      (i,hm)  <@ H.h{m};
      bad <- bad \/ i = 0;
      return finv sk hm;
    }
  }

  module H' = {
    quantum proc h{x:msg} : hash = {
      quantum var i, hx;
      (i,hx) <@ H.h{x};
      return hx;
    }
  }

  proc main(r_:int) = {
    var s, i, hm, b;
    (pk, sk) <$ kg;
    log <- [];
    bad <- false;
    (m,s) <@ Wrap(A, H', Os).main(pk);
    (i,hm) <@ H.h{m};
    bad <- bad \/ i <> 0;
    b <- hm = f pk s /\ !m \in log /\ !bad;
    return b;

  }
}.

import var EUF B SR.

local lemma l2 r &m :
  0 < r => 
  Pr[EUF_QROM'(A).main(r) @ &m : res] =
  Pr[IND_SRr(SROr, ASRr).main(r) @ &m : res].
proof.
  move=> hr; byequiv => //.
  proc; inline *; wp.
  call (: ={QRO.h, SR.fr, log, EUF.sk} /\ (ASRr.bad = exists m', m' \in log /\ SR.fr m' = 0){2}). 
  + by proc ; inline *; auto => /> /#. 
  + by proc; inline *;auto => />;skip => />.
  auto => /> /#.
qed.

local hoare hoare_bound1 : Wrap(A, ASRr(SROr).H', ASRr(SROr).Os).main : 
  QRO.ch = 0  ==>
  QRO.ch <= qs + qh.
proof.
  conseq (: true ==> Wrap.cs <= qs /\ Wrap.ch <= qh) 
         (: QRO.ch = 0 ==> QRO.ch = Wrap.cs + Wrap.ch).
  + smt().
  + proc.
    call (: QRO.ch = Wrap.cs + Wrap.ch).
    + by proc; inline *; auto => /> *; ring.
    + by proc; inline *; auto => /> *; ring.
    by auto.
  by apply (hoare_bound (<:ASRr(SROr).H') (<: ASRr(SROr).Os)).
qed.

local lemma l3 r &m :
  0 < r =>  
  `| Pr[IND_SRr(SROr, ASRr).main(r) @ &m : res] - 
     Pr[IND_SRr(SRr , ASRr).main(r) @ &m : res] | 
   <= (54 * q^3)%r / r%r. 
proof.
  move=> h0r; apply (advantage_r q r ASRr &m h0r _).
  proc; inline ASRr(SROr).main SROr.h.
  wp; call hoare_bound1; inline *; auto => /> /#.
qed.

local clone import DList.Program with
  type t <- hash,
  op d <- dhash.

local lemma l4 r0_ &m :
  0 < r0_ => 
  Pr[IND_SRr(SRr , ASRr).main(r0_) @ &m : res] <= Pr[OW(B(A)).main(r0_) @ &m : res].
proof.
  move=> hr;
  byequiv (: ={glob A} /\ r{1} = r0_ /\ ={arg} ==> res{1} => res{2}) => //.
  proc; inline *; wp; symmetry.
  (* Proof using upto bad *)
  call (_: ASRr.bad, 
           ={QRO.h, EUF.log} /\ 
           (forall m, SR.fr{2} m <> 0 => B.hs{1} m = (finv EUF.sk (QRO.h m)){2})) => //.
  + by apply A_ll.
  + by proc; inline *; auto => /> /#.
  + by move=> *; islossless.
  + by move=> *; proc; inline *; auto => /> /#.
  + by proc; inline *; auto.
  + by move=> *; islossless. 
  + by move=> *; proc; inline *; auto.
  swap{2} 7 -5. 
  swap{1} [8..9] 1. swap{1} 5 -4. swap{1} [4..6] 2.
  wp; sp; rnd => /=.
  seq 1 1 : (#pre /\ ={sk} /\ pk{1} = EUF.pk{2} /\ ((pk,sk) \in kg){1}).
  + by rnd; skip => /> [].
  conseq (: rh{2} = (y :: map (f pk) rs2){1}  /\ size rs2{1} = r{1} - 1 ).
  + move=> /> &2 hpk rs2 y hsize fr /dfun_supp /= hfr; split.
    + move=> m' hm'; have /DInterval.supp_dinter hfrm' := hfr m'.
      rewrite (nth_map witness witness (f EUF.pk{2})); smt(finv_f).
    smt (finv_f f_finv mapP).
  transitivity * {2} { rh <@ Sample.sample(r0); } => //; 1:smt(); last by inline *;auto.
  transitivity {2} { rh <@ SampleCons.sample(r0); } 
    (r{1} = r0{2} /\ 0 <= r{1} - 1 /\ ={sk} /\ pk{1} = EUF.pk{2} /\ (pk,sk){1} \in kg ==> 
       rh{2} = (y :: map (f pk) rs2){1} /\ (size rs2 = r - 1){1})
    (={r0} /\ 0 < r0{1} ==> ={rh}) => //;1: smt(); last first.
  + by symmetry; call Sample_SampleCons_eq; skip.
  inline *; swap{2} 3 -1; wp; sp.
  rnd (map (f pk{1})) (map (finv sk{1})); rnd; skip => />.
  move=> &2 hr0 hk y hy; split.
  + move=> rs2 ?; rewrite -map_comp -{1}(map_id rs2); apply eq_map.
    by move=> x; rewrite /(\o) (f_finv _ _ hk).
  move=> _; split.
  + move=> rs hrs. rewrite !dlist1E 1,2:// size_map.
    case: (r0{2} - 1 = size rs) => // hsz.
    rewrite BRM.big_map; apply BRM.eq_big => //= h _. 
    by rewrite /(\o); apply dhash_dsign.
  move=> _ rs2; rewrite supp_dlist 1:// => -[] ^ hs -> /= ?; split.
  + by rewrite supp_dlist 1:// size_map hs /= allP => *; apply dhash_fu.
  move=> ?; rewrite -map_comp -{1}(map_id rs2); apply eq_map.
  by move=> x; rewrite /(\o) (finv_f _ _ hk).
qed.

lemma conclusion r0 &m : 
  1 < r0 => let lam = inv r0%r in
  Pr[EUF_QROM(A,FDH).main() @ &m : res] <=
  Pr[OW(B(A)).main(r0) @ &m : res] / (lam * (1%r - lam) ^ qs) + 
    (54 * q^3)%r / (1%r - lam) ^ qs. 
proof. 
  move=> h1r0 lam. 
  have h0r0 : 0 < r0 by smt(). 
  have : lam * (1%r - lam) ^ qs * Pr[EUF_QROM(A,FDH).main() @ &m : res] <=
         Pr[OW(B(A)).main(r0) @ &m : res] + (54 * q^3)%r * lam. 
  + have := l1 r0 &m _; 1: smt().
    by move: (l2 r0 &m h0r0) (l3 r0 &m h0r0) (l4 r0 &m h0r0) => /#.
  have lam_bound : 0.0 < lam < 1.0 by smt().
  rewrite -ler_pdivl_mull; 1: smt (expr_gt0).
  move=> h; apply/(ler_trans _ _ _ h)/lerr_eq; field => //; smt (expr_gt0).
qed.

(* The minimum is found in r0 = qs + 1 *)
*)
(* We can prove the Zhandry bound *)
(* Remark Zhandry use r = 2k / eps, this is not a integer.
   We are forced to use the floor and this make the final bound a little less good. *)

abstract theory FDH_OW_small_range.

clone import T_OW with
  type init <- int, 
  op dcodom <- dhash.

module B (A:AdvEUF_QROM) : AdvOW = {
  import var EUF
  var hs : msg -> sign

  module Os = {
    proc sign(m:msg) = { 
      log <- m :: log;
      return hs m; 
    }
  }

  proc main(pk_:pkey, y:hash, r:int) = {
    var s, i, fr, rs1, rs2, rs, rh;
    log <- [];
    i <$ [0 .. r-1];
    rs1 <$ dlist dsign i;
    rs2 <$ dlist dsign (r-i-1);
    rs  <- rs1 ++ witness :: rs2;
    rh  <- map (f pk_) rs1 ++ y :: map (f pk_) rs2;
    fr  <$ difun r; 
    hs <- fun x => nth witness rs (fr x); 
    QRO.h <- fun x => nth witness rh (fr x);
    (m,s) <@ A(QRO, Os).main(pk_);
    return s; 
  }
}.

clone import SmallRange.

clone import Collision with 
  type input <- unit.

section OW.

declare module A <: AdvEUF_QROM { -QRO, -EUF , -B, -Wrap, -SR}.

declare axiom hoare_bound (H<:QRO{-A, -Wrap}) (S<:OrclSign{-A, -Wrap}) :
  hoare[ Wrap(A, H, S).main : true ==> Wrap.cs <= qs /\ Wrap.ch <= qh].

declare axiom A_ll (H <: QRO{-A}) (S <: OrclSign{-A}) : 
  islossless S.sign => islossless H.h => islossless A(H, S).main.

local module G1 (H:QRO) = {
  var logs : (hash * msg) list
  var hm  : hash

  module FDH = {
    proc kg () = {
      var k;
      k <$ kg;
      return k;
    }
  
    proc sign(sk:skey, m:msg) = {
      var h;
      h <@ H.h{m};
      logs <- (h,m) :: logs;
      return finv sk h;
    }
  
    proc verify(pk:pkey, m:msg, s:sign) = {
      hm <@ H.h{m};
      return hm = f pk s;
    }
  
  }

  proc main() = {
    var b;
    logs <- [];
    b <@ EUF(Wrap(A, H), FDH).main();
    return b;
  }
}.

clone import T_PRF.

local lemma EUF_G1 &m : 
  Pr[EUF_QROM(A,FDH).main() @ &m : res] = Pr[IND_QRO(QRO,G1).main() @ &m : res].
proof.
  byequiv => //; proc; inline *.
  wp; call (: ={EUF.sk, EUF.log, QRO.h}).
  + by proc; inline *; auto.
  + by sim.
  auto => />.
qed.

local module G1_col (H:QRO) = {
  proc main() = {
    var b;
    b <@ G1(H).main();
    return (EUF.m, oget (assoc G1.logs G1.hm));
  }
}.

local hoare hoare_bound1 : Wrap(A, QRO, EUF(Wrap(A, QRO), G1(QRO).FDH).Os).main : 
  QRO.ch = 0  ==>
  QRO.ch <= qs + qh.
proof.
  conseq (: true ==> Wrap.cs <= qs /\ Wrap.ch <= qh) 
         (: QRO.ch = 0 ==> QRO.ch = Wrap.cs + Wrap.ch).
  + smt().
  + proc.
    call (: QRO.ch = Wrap.cs + Wrap.ch).
    + by proc; inline *; auto => /> *; ring.
    + by proc; inline *; auto => /> *; ring.
    by auto.
  by apply (hoare_bound QRO (<: EUF(Wrap(A, QRO), G1(QRO).FDH).Os)).
qed.

local lemma G1_split &m :
  let r1 = mu1 dhash witness in
  Pr[IND_QRO(QRO,G1).main() @ &m : res] <= 
    Pr[IND_QRO(QRO,G1).main() @ &m : res /\ ! (G1.hm \in unzip1 G1.logs) ] + 
    (27 *(q +2)^3)%r * r1.
proof.
  rewrite Pr[mu_split (G1.hm \in map fst G1.logs)].
  have : Pr[IND_QRO(QRO, G1).main() @ &m : res /\ (G1.hm \in unzip1 G1.logs)] <= 
         Pr[Col(G1_col).main() @ &m : res].
  + byequiv=> //; proc; inline *; wp.
    call (: ={EUF.sk, EUF.log, QRO.h, G1.logs} /\ 
             (G1.logs = map (fun m => (QRO.h m, m)) EUF.log){1}).
    + by proc; inline *; auto.
    + by sim />.
    auto => />; smt(assocP mapP).
  have /# := pr_col () q G1_col &m _.
  proc. 
  inline G1_col(QRO).main G1(QRO).main EUF(Wrap(A, QRO), G1(QRO).FDH).main
             G1(QRO).FDH.verify QRO.h; wp.
  by call hoare_bound1; inline *; auto => /> /#.
qed.

local module G2(H:SR) = {
  proc main (r:int) = {
     var b;
     b <@ G1(H).main();
     return b /\ !(G1.hm \in unzip1 G1.logs); 
  }  
}.

local lemma G1_SRO r &m :
  0 < r =>  
  Pr[IND_QRO(QRO,G1).main() @ &m : res /\ ! (G1.hm \in unzip1 G1.logs) ] = 
  Pr[IND_SR (SRO,G2).main(r) @ &m : res].
proof.
  move=> hr; byequiv => //; proc; inline G2(SRO).main; wp.
  sim : (b{1} = b0{2} /\ ={G1.hm, G1.logs}).
  inline *; auto => />; apply dfun_ll => /=; apply DInterval.dinter_ll => /#.
qed.

local hoare hoare_bound2 : Wrap(A, SRO, EUF(Wrap(A, SRO), G1(SRO).FDH).Os).main : 
  QRO.ch = 0  ==>
  QRO.ch <= qs + qh.
proof.
  conseq (: true ==> Wrap.cs <= qs /\ Wrap.ch <= qh) 
         (: QRO.ch = 0 ==> QRO.ch = Wrap.cs + Wrap.ch).
  + smt().
  + proc.
    call (: QRO.ch = Wrap.cs + Wrap.ch).
    + by proc; inline *; auto => /> *; ring.
    + by proc; inline *; auto => /> *; ring.
    by auto.
  by apply (hoare_bound SRO (<: EUF(Wrap(A, SRO), G1(SRO).FDH).Os)).
qed.

local lemma SRO_SR r0 &m : 
  0 < r0 => 
  `| Pr[IND_SR (SRO,G2).main(r0) @ &m : res] - Pr[IND_SR (SR,G2).main(r0) @ &m : res] | <=
  (27 * q^3)%r / r0%r.
proof.
  move=> hr; apply (advantage q r0 G2 &m hr).
  proc.
  inline G2(SRO).main G1(SRO).main EUF(Wrap(A, SRO), G1(SRO).FDH).main
             G1(SRO).FDH.verify QRO.h; wp.
  by call hoare_bound2; inline *; auto => /> /#.
qed.

local module G3 = {
  var i : int
  proc main (r:int) = {
    var b;
    b <@ IND_SR (SR,G2).main(r);
    i <$ [0..r-1];
    return b /\ SR.fr EUF.m = i;
  }
}.

local lemma G3_SR r0 &m : 
  0 < r0 =>
  Pr[G3.main(r0) @ &m : res] = 1.0/r0%r * Pr[IND_SR (SR,G2).main(r0) @ &m : res].
proof.
move=> hr.
byphoare (:(glob A){m} = glob A /\ r = r0 ==> _) => //.
proc.
seq 1 : b Pr[IND_SR(SR,G2).main(r0) @ &m : res] (inv r0%r)
          _ 0%r (r = r0 /\ 0 <= SR.fr EUF.m < r).
+ inline *; wp.
  conseq (: forall x, 0 <= SR.fr x < r).
  + by move=> /> ? m0 /(_ m0.`1) />.
  call (: true) => //; auto => /> rh _ fr /dfun_supp /= h _ _ x. 
  by have /DInterval.supp_dinter /# := h x.
+ call (: (glob A){m} = glob A /\ r = r0 ==> res); 2: by auto.
  bypr => &m0 h.
  byequiv (: ={glob A, arg} ==> ={res, EUF.m, EUF.log, SR.fr}) => //; 1: by sim.
  by move: h => />.
+ by conseq />; rnd (pred1 (SR.fr EUF.m)); skip => />; smt (DInterval.dinter1E).
+ by conseq (:false) => /> //.
smt().
qed.

local clone import DList.Program with
  type t <- hash,
  op d <- dhash.

local module S = {
  proc sample2(n1:int, n2:int) = {
    var rh1, y, rh2;
    (rh1,y,rh2) <@ Sample.sample2(n1,n2); 
    return rh1 ++ y :: rh2;
  }
}.

local lemma G3_OW r_ &m:
  0 < r_ =>
  Pr[G3.main(r_) @ &m : res] <= Pr[OW(B(A)).main(r_) @ &m : res].
proof.
  move=> h0r; byequiv=> //; proc; inline *.
  swap{1} -27; wp.
  symmetry.
  call (_: exists m', m' \in EUF.log /\ SR.fr m' = G3.i, 
           ={QRO.h, EUF.log} /\ 
           (G1.logs = map (fun m => (QRO.h m, m)) EUF.log){2} /\
           (forall m, SR.fr{2} m <> G3.i{2} => 
              B.hs{1} m = (finv EUF.sk (QRO.h m)){2}),
          (G1.logs = map (fun m => (QRO.h m, m)) EUF.log){2}) => //.
  + by apply A_ll.
  + by proc; inline *; auto => /> /#.
  + by move=> *; proc; auto.
  + by move=> *; proc; inline *; auto => /> /#.
  + by proc; inline *; auto.
  + by move=> *; proc; auto. 
  + by move=> *; proc; inline *; auto.
  swap{2} 10 -9; wp.
  swap{1} [10..11] 1.
  swap{1} 5 -4.
  swap{1} [4..6] 4; wp.
  swap{2} [3..4] -2; sp.
  swap{1} 2 2.
  rnd.
  seq 2 2 : (#pre /\ k{2} = (pk,sk){1} /\ G3.i{2} = i0{1} /\ 0 <= G3.i{2} < r_ /\
          k{2} \in kg).
  + by auto => />; smt(DInterval.supp_dinter).
  conseq (: SR.rh{2} = (map (f pk) rs1 ++ y :: map (f pk) rs2){1} /\ 
            size rs1{1} = i0{1} /\ size rs2{1} = r{1} - i0{1} - 1).
  + move=> /> &1 h0i hir hk rs1 rs2 y <<- ? fr /dfun_supp /= hfr; split.
    + move=> m' hm'; rewrite !nth_cat size_map /=.
      have /DInterval.supp_dinter hfrm' := hfr m'.
      case: (fr m' < size rs1) => ?.
      + by rewrite (nth_map witness witness (f pk{1}) (fr m')) 1:/# (finv_f _ _ hk). 
      rewrite (nth_map witness witness (f pk{1})); smt(finv_f).
    smt (finv_f f_finv nth_cat size_map mapP map_comp).
  transitivity * {2} { SR.rh <@ Sample.sample(r1); } => //; 1:smt(); last by inline *;auto.
  transitivity {2} { SR.rh <@ S.sample2(G3.i, r - G3.i - 1); } 
    (={r} /\ i0{1} = G3.i{2} /\ (pk,sk){1} \in kg /\ 0 <= G3.i{2} < r{2} ==> 
       SR.rh{2} = map (f pk{1}) rs1{1} ++ y{1} :: map (f pk{1}) rs2{1} /\
       size rs1{1} = i0{1} /\ size rs2{1} = r{1} - i0{1} - 1)
    (r1{2} = r{1} /\ 0 <= r{1} /\ 0 <= G3.i{1} < r{1} ==> ={SR.rh}) => //;1: smt(); last first.
  + symmetry; inline S.sample2; wp; ecall (Sample_Sample2 n1{2} n2{2}); wp; skip => /> /#.
  inline *; wp; sp.
  rnd (map (f pk{1})) (map (finv sk{1})); rnd; rnd (map (f pk{1})) (map (finv sk{1})); skip => />.
  move=> &1 &2 hk hi0 hir; split. 
  + move=> rs1 ?; rewrite -map_comp -{1}(map_id rs1); apply eq_map.
    by move=> x; rewrite /(\o) (f_finv _ _ hk).
  move=> _; split.
  + move=> rs hrs. rewrite !dlist1E 1,2:// size_map.
    case: (G3.i{2} = size rs) => // hsz.
    rewrite BRM.big_map; apply BRM.eq_big => //= h _. 
    by rewrite /(\o); apply dhash_dsign.
  move=> _ rs1; rewrite supp_dlist 1:// => -[] <<- ?; split.
  + rewrite supp_dlist 1:// size_map /= allP => *; apply dhash_fu.
  move=> _; split.
  + rewrite -map_comp -{1}(map_id rs1); apply eq_map.
    by move=> x; rewrite /(\o) (finv_f _ _ hk).
  move=> _ y hy; split.
  + move=> rs2 ?; rewrite -map_comp -{1}(map_id rs2); apply eq_map.
    by move=> x; rewrite /(\o) (f_finv _ _ hk).
  move=> _; split.
  + move=> rs hrs. rewrite !dlist1E 1,2:/# size_map.
    case: (r{2} - size rs1 - 1 = size rs) => // hsz.
    rewrite BRM.big_map; apply BRM.eq_big => //= h _. 
    by rewrite /(\o); apply dhash_dsign.
  move=> _ rs2; rewrite supp_dlist 1:/# => -[] hrs2 ?; split.
  + rewrite supp_dlist 1:/# size_map hrs2 /= allP => *; apply dhash_fu.
  move=> _; split => //.
  rewrite -map_comp -{1}(map_id rs2); apply eq_map.
  by move=> x; rewrite /(\o) (finv_f _ _ hk).
qed.

(* Remark: 
   [mu1 dhash witness] is the probability of obtaining an element in dhash, 
   this is negligeable.
   Now assume that the hypothesis: (3 * k)%r * rhash <= eps 
   We have eps <  (3 * k)%r * rhash.
   So eps is negligeable.
*)
  
lemma conclusion &m : 
  let eps = Pr[EUF_QROM(A,FDH).main() @ &m : res] in
  let k = 54 * (q + 2)^3 in
  let r = 3 * floor (k%r / eps) in 
  let rhash = mu1 dhash witness in
  (3 * k)%r * rhash <= eps =>
  eps ^2 / (6 * k)%r <= Pr[OW(B(A)).main(r) @ &m : res].
proof.
  move=> eps k r rhash hhe.
  have h0rhash: 0.0 < rhash.
  + admit.
  have gt0_q3 : 1 <= (q + 2) ^ 3 by apply IntOrder.exprn_ege1 => //; smt (gt0_qs ge0_qh).
  have heps : 0%r < eps by smt().
  have gt0_r : 0 < r. 
  + smt(floor_bound mu_bounded).
  apply: ler_trans (G3_OW r &m gt0_r).
  rewrite (G3_SR r &m gt0_r).
  apply (ler_trans (eps/(3*k)%r * Pr[IND_SR(SR, G2).main(r) @ &m : res])); last first.
  + apply ler_wpmul2r; 1: smt(mu_bounded).
    have h0k: 0%r < k%r by smt().
    have hepsk : 0%r <= eps/k%r by smt().
    have -> : eps/(3*k)%r = inv((3*k)%r/eps) by smt().
    by rewrite /= lef_pinv; smt (floor_bound).
  have -> : eps ^ 2 / (6 * k)%r = eps / (3 * k)%r * (eps/2%r) by field => //; smt(). 
  apply ler_wpmul2l; 1: smt().
  apply (ler_trans (Pr[IND_SR(SRO, G2).main(r) @ &m : res] - (27*(q+2)^3)%r/r%r)); last first.
  + by have := SRO_SR r &m gt0_r; smt (IntOrder.ler_pexp gt0_qs ge0_qh).
  apply (ler_trans (eps - (27 * (q + 2) ^ 3)%r / r%r - (27 * (q + 2) ^ 3)%r / r%r));
    last first.
  + rewrite ler_add2r.
    have := EUF_G1 &m; rewrite -/eps => ->.
    have /= := G1_split &m. rewrite -/rhash.
    have -> := G1_SRO r &m gt0_r.
    have /#: (27 * (q + 2) ^ 3)%r * rhash <=  (27 * (q + 2) ^ 3)%r / r%r.
    apply ler_wpmul2l; 1:smt().
    apply (ler_trans (eps / (3*k)%r)). 
    + by apply ler_pdivl_mulr; [ smt() | rewrite mulrC].
    have -> : eps/(3*k)%r = inv((3*k)%r/eps) by smt().
    by rewrite /= lef_pinv; smt (floor_bound).
  have -> : eps - (27 * (q + 2) ^ 3)%r / r%r - (27 * (q + 2) ^ 3)%r / r%r =
            eps - k%r/r%r by smt().
  have /# : k%r / r%r <= eps/2%r.
  rewrite -/k ler_pdivl_mulr 1:// mulrC mulrA ler_pdivr_mulr 1:/#.
  rewrite (mulrC eps) -ler_pdivr_mulr 1:// -mulrA mulrC -ler_pdivl_mulr 1://. 
  have : 3%r <= k%r / eps.
  + apply (ler_trans k%r); 1: smt().
    rewrite ler_pdivl_mulr 1://; have /#: eps <= 1%r by smt(mu_bounded). 
  smt (floor_bound).
qed.

end section OW.

end FDH_OW_small_range.
