require import AllCore List Distr DBool CHoareTactic.
require (*  *) T_QROM T_EUF T_PERM.
(*   *) import StdOrder RField RealOrder StdBigop Bigreal.

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

module EUF_QROM (A:AdvEUF_QROM) (S:Sign_QROM) = {
  proc main() = {
    var b;
    QRO.init();
    b <@ EUF(A(QRO), S(QRO)).main();
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

(* --------------------------------------------------------------------------- *)
(* Generic start of the proof used for OW and ClawFree *)

import DBB.

lemma pr_dfbool_l lam m (l:msg list) q : 
  0%r <= lam <= 1%r =>
  !m \in l => size l <= q =>  
  lam*(1%r-lam)^q <= 
    mu (dbfun lam) (fun t => t m /\ forall m', m' \in l => !t m').
proof.
  move=> lam_bound hm hl.
  apply (ler_trans (lam ^ 1 * (1%r - lam) ^ size l)).
  rewrite RField.expr1; apply ler_wpmul2l; 1: by case: lam_bound.
  apply ler_wiexpn2l; [1:smt ()| 2: smt(size_ge0)].
  apply (ler_trans _ _ _ (dbfunE_mem_le lam [m] l lam_bound _)); 1: smt().
  by apply mu_le => /#.
qed.

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

declare module A : 
  AdvEUF_QROM { -QRO, -EUF, -EUF_QROM'}[main : `{Inf, #H.h : qh, #S.sign : qs}].

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
+ inline *; wp.
  conseq (:size EUF.log <= qs) => />.
  (* FIXME: Adrien can we use complexity info here *)
  admit.
+ call (: (glob A){m} = glob A ==> res); 2: by auto.
  bypr => &m0 ?.
  byequiv (: ={glob A} ==> ={res}) => //; 1: sim.
+ rnd (fun t => t EUF.m /\ forall (m' : msg), m' \in EUF.log => ! t m').
  by skip => /> &hr h /h /> *; apply: pr_dfbool_l.
+ by auto.
smt().
qed.

end section.
end START.

import MUFF.
(* --------------------------------------------------------------------------*)
op [lossless uniform full] dsign : sign distr.
(* FIXME: this should be provable because f is bijective *)
axiom dhash_dsign : mu1 dhash witness = mu1 dsign witness.

op dfsign : (msg -> sign) distr = dfun (fun _ => dsign).

lemma dfsign_ll: is_lossless dfsign.
proof. apply dfun_ll => ?;apply dsign_ll. qed.

lemma dfsign_uni: is_uniform dfsign.
proof. apply dfun_uni => ?; apply dsign_uni. qed.

lemma dfsign_fu: is_full dfsign.
proof. apply dfun_fu => ?; apply dsign_fu. qed.

hint solve 0 random : dfsign_ll dfsign_uni dfsign_fu.

lemma dfsign_dfhash (hs: msg -> sign) (hh:msg -> hash) : mu1 dfsign hs = mu1 dfhash hh.
proof.
  rewrite !dfun1E;apply BRM.eq_big => //= x _.
  rewrite (is_full_funiform _ dsign_fu dsign_uni _ witness).
  by rewrite (is_full_funiform _ dhash_fu dhash_uni _ witness) dhash_dsign.
qed.

(* --------------------------------------------------------------------------*)
(* Proof assuming that f in OW *)

abstract theory FDH_OW_semi_constant.

op lam : real.
axiom lam_bound : 0%r < lam < 1%r.

clone import T_OW with 
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

  proc main(pk:pkey, y:hash) : sign = {
    var m,s;
    bf <$ dbfun lam;
    hs <$ dfsign;
    QRO.h <- fun m => if bf m then y else f pk (hs m);
    EUF.log <- [];
    (m,s) <@ A(QRO, Os).main(pk);
    return s;
  }
}.

op q = qs + qh + 1.

section OW.

declare module A : AdvEUF_QROM { -QRO, -EUF, -B}
                     [main : `{Inf, #H.h : qh, #S.sign : qs}].

axiom A_ll (H <: QRO{-A}) (S <: OrclSign{-A}) : 
  islossless S.sign => islossless H.h => islossless A(H, S).main.

local clone import START.
local clone import SemiConstDistr with
    op k <- qs.

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
    (m,s) <@ A(H,Os).main(pk);
    hm <@ H.h{m};
    b <- hm = f pk s;
    return (b, m, log);
  }
}.

import var EUF B SCD.

local lemma l3 &m : 
  Pr[EUF_QROM'(A).main(lam) @ &m : res] =
  Pr[SCD(ASCD)._F0(lam) @ &m : res].
proof.
  byequiv => //.
  proc; inline *; wp.
  call (: ={QRO.h, sk, log}). 
  + by proc ; inline *; auto. 
  + by proc; inline *;auto => />;skip => />.
  swap{2} 3 1; auto; rnd{2}; do 3! rnd; skip => /> /#.
qed.

local lemma l4 &m : 
  `| Pr[SCD(ASCD)._F0(lam) @ &m : res] - 
     Pr[SCD(ASCD)._F1(lam) @ &m: res] | 
   <= (2%r * q%r + qs%r + 1%r)/ 6%r * lam^2.
proof.
  apply (advantage q lam ASCD _ &m _); last by smt(lam_bound). 
  move=> kH H hkH.
  proc; wp.
  call(:true).
  call(:true; 
     time 
       [H.h : [N kH],
        ASCD(H).Os.sign : [Inf; H.h: 1]]).
  + move=> kh ks *; proc.
    by call(:true); auto.  
  + move=> kh ks *. 
    (* FIXME Adrien: time [] optionel ? *)
    by proc (true) : time [ ].
  by wp; rnd; skip => />; apply kg_ll.
qed.

local lemma l5 &m :
  Pr[SCD(ASCD)._F1(lam) @ &m: res] <= Pr[OW(B(A)).main() @ &m : res].
proof.
  byequiv (: ={glob A} /\ p{1} = lam ==> res{1} => res{2}) => //.
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
  swap{1}5 -4. swap{1} 4 -2; wp.
  rnd (fun (h:msg -> hash) => fun m => finv sk{1} (h m))
      (fun (h:msg -> sign) => fun m => f pk{1} (h m)).
  rewrite /good; auto; rnd; skip => /> k hk h _ bf _; split.
  + by move=> *; apply fun_ext => ?; smt(finv_f).
  smt(dfsign_dfhash f_finv finv_f).
qed.

lemma conclusion &m : 
  Pr[EUF_QROM(A,FDH).main() @ &m : res] <=
  Pr[OW(B(A)).main() @ &m : res] / (lam * (1%r - lam) ^ qs) + 
   (2*qh + 3*qs + 3)%r/ 6%r * lam / (1%r - lam) ^ qs. 
proof. 
  have : lam * (1%r - lam) ^ qs * Pr[EUF_QROM(A,FDH).main() @ &m : res] <=
         Pr[OW(B(A)).main() @ &m : res] + (2%r * q%r + qs%r + 1%r)/ 6%r * lam^2. 
  + by move: (l1 A lam &m) lam_bound (l3 &m) (l4 &m) (l5 &m) => /#. 
  rewrite /q !fromintD -ler_pdivl_mull; 1: smt (expr_gt0 lam_bound).
  move=> h; apply/(ler_trans _ _ _ h)/lerr_eq; field => //; smt (expr_gt0 lam_bound).
qed.

end section OW.

end FDH_OW_semi_constant.

(* The minimun of the above bound is found for lam = 1/(qs+1) *)
abstract theory FDH_OW_SC_instanciate.

clone include FDH_OW_semi_constant with
  op lam = 1%r/(qs+1)%r
  proof lam_bound by smt(gt0_qs).

end FDH_OW_SC_instanciate.

(* --------------------------------------------------------------------------*)
(* Proof assuming that f is a claw free permutation *)

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

declare module A : AdvEUF_QROM { -EUF, -QRO, -B}
                    [main : `{Inf, #H.h : qh, #S.sign : qs}].

axiom A_ll (H <: QRO{-A}) (S <: OrclSign{-A}) : 
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
  swap{1} 3 -2; wp.
  rnd (fun h  => fun m => if B.bf m then P2.finv sk (h m) else finv sk (h m)){2}
      (fun hs => fun m => if B.bf m then P2.f pk (hs m) else f pk (hs m)){2}.
  auto; rnd; skip => /> {&m}.
  move => k hk t _; split.
  + move=> hs _; apply fun_ext; smt (P2.finv_f finv_f).
  smt (dfsign_dfhash P2.f_finv f_finv).
qed.

lemma conclusion &m : 
   Pr[EUF_QROM(A, FDH).main() @ &m : res] <= 
    Pr[ClawFree(B(A)).main() @ &m : res] / (lam * (1%r - lam) ^ qs).
proof.
  have : lam * (1%r - lam) ^ qs * Pr[EUF_QROM(A, FDH).main() @ &m : res] <= 
    Pr[ClawFree(B(A)).main() @ &m : res].
  + move: (l1 A lam &m) lam_bound (l3 &m) => /#.
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

abstract theory FDH_OW_small_range.

clone import T_OW with 
  op dcodom <- dhash.

module B (* (A:AdvEUF_QROM) : AdvOW *) = {
  import var EUF
  var hs : msg -> sign
(*
  module Os = {
    proc sign(m:msg) = { 
      log <- m :: log;
      return hs m; 
    }
  }

  proc main(pk:pkey, y:hash) : sign = {
    var m,s;
    bf <$ dbfun lam;
    hs <$ dfsign;
    QRO.h <- fun m => if bf m then y else f pk (hs m);
    EUF.log <- [];
    (m,s) <@ A(QRO, Os).main(pk);
    return s;
  }
*)
}.

op q = qs + qh + 1.

clone T_QROM as SQRO with
  type from <- msg,
  type hash <- sign,
  op dhash <- dsign,
  op MUFF.FinT.enum <- QROM.MUFF.FinT.enum
  proof dhash_ll by apply dsign_ll,
        dhash_uni by apply dsign_uni,
        dhash_fu by apply dsign_fu,    
        MUFF.FinT.enum_spec by apply QROM.MUFF.FinT.enum_spec.

import SQRO.SmallRange. 

section OW.

declare module A : AdvEUF_QROM { -QRO, -SQRO.QRO, -EUF , -B}
                     [main : `{Inf, #H.h : qh, #S.sign : qs}].

axiom A_ll (H <: QRO{-A}) (S <: OrclSign{-A}) : 
  islossless S.sign => islossless H.h => islossless A(H, S).main.

local module G1 (S:SQRO.QRO) = {
  import var EUF QRO B
  module Os = {
    proc sign(m:msg) = { 
      var s;
      s <@ S.h{m};
      log <- m :: log;
      return s; 
    }
  }

  module RO = {
    quantum proc h {m:msg} = {
      quantum var s;
      s <@ S.h{m};
      return f pk s;
    }
  }

  proc main() = {
    var s, s';
    (pk, sk) <$ kg;
    log <- [];
    (m,s) <@ A(RO, Os).main(pk);
    s' <@ S.h{m};
    return f pk s' = f pk s /\ !m \in log;
  }
}.

local lemma SROdfhash_dfsign : SQRO.dfhash = dfsign.
proof. done. qed. 

local lemma l1 &m r : 
  Pr[EUF_QROM(A,FDH).main() @ &m : res] = Pr[IND_SR(SRO,G1).main(r) @ &m : res].
proof.
  byequiv => //; proc; inline *;wp.
  call (: ={EUF.pk, EUF.sk, EUF.log} /\ (EUF.pk, EUF.sk){1} \in kg /\
           QRO.h{1} = (fun m => f EUF.pk (SQRO.QRO.h m)){2}).
  + by proc; inline *; auto => /> &2 /finv_f /= ->.
  + by proc; inline *; auto.
  sp; wp; swap 2 -1.
  rnd (fun (h:msg -> hash) => fun m => finv EUF.sk{2} (h m))
      (fun (h:msg -> sign) => fun m => f EUF.pk{2} (h m)).
  rnd; skip => /> ks hks; rewrite SROdfhash_dfsign; smt (fun_ext finv_f f_finv dfsign_dfhash).
qed.

local lemma l2 &m r : 
  0 <= r => 
  `| Pr[IND_SR(SRO,G1).main(r) @ &m : res] - Pr[IND_SR(SR,G1).main(r) @ &m : res]| 
   <= 27%r * q%r^3 / r%r.
proof.
  apply (SQRO.SmallRange.advantage q r G1).
  admit.
qed.





lemma conclusion &m : 
  Pr[EUF_QROM(A,FDH).main() @ &m : res] <=
  Pr[OW(B(A)).main() @ &m : res] / (lam * (1%r - lam) ^ qs) + 
   (2*qh + 3*qs + 3)%r/ 6%r * lam / (1%r - lam) ^ qs. 
proof. 



