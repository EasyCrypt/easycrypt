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
    h <@ H.h|m>;
    return finv sk h;
  }

  proc verify(pk:pkey, m:msg, s:sign) = {
    var h;
    h <@ H.h|m>;
    return h = f pk s;
  }

}.

(* --------------------------------------------------------------------------- *)
(* Maximal number of queries to the sign/hash oracle *)
op qs : { int | 0 <= qs } as ge0_qs.
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
    return b /\ (bf EUF.m /\ forall m', m' \in EUF.log => !bf m');
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
  by skip => /> &hr h /h [] ??; apply: pr_dfbool_l.
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

abstract theory FDH_OW.

op lam : real.
axiom lam_bound : 0%r <= lam <= 1%r.

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
  type result <- bool * msg list * msg.

local module (ASCD:AdvSCD) (H:QRO) = {
  import var EUF

  module Os = {
    proc sign(m:msg) = {
      var hm;
      log <- m::log;
      hm  <@ H.h|m>;
      return finv sk hm;
    }
  }

  proc main() = {
    var b, s, hm;
    (pk, sk) <$ kg;
    log <- [];
    (m,s) <@ A(H,Os).main(pk);
    hm <@ H.h|m>;
    b <- hm = f pk s;
    return (b, log, m);
  }
}.

op P (r:(bool * msg list * msg) * (msg -> bool)) = 
  let (r,t) = r in
  let (b, log, m) = r in 
  b /\ !m \in log /\ (t m /\ forall m', m' \in log => !t m').

import var EUF B SCD.

local lemma l3 &m : 
  Pr[EUF_QROM'(A).main(lam) @ &m : res] =
  Pr[SCD(ASCD).main1(lam) @ &m : P res].
proof.
  byequiv => //.
  proc; inline *; wp.
  call (: ={QRO.h, sk, log}).
  + by proc; inline *; auto.
  + by sim. 
  by auto; rnd{2}; auto => />.
qed.

local lemma l4 &m : 
  `| Pr[SCD(ASCD).main1(lam) @ &m : P res] - 
     Pr[SCD(ASCD).main2(lam) @ &m: P res] | 
   <= 8%r/3%r * q%r^4 * lam^2.
proof.
  apply (advantage q lam ASCD); last by apply lam_bound.
  move=> kH H hkH.
  proc; wp.
  call(:true).
  call(:true; 
    time 
     [(H.h : [N kH]),
      (ASCD(H).Os.sign : [Inf; H.h: 1])]).
  + move=> kh ks *; proc.
    call(:true); auto => /=.
    (* FIXME Adrien: pourquoi -1 *)
    (* FIXME benjamin: add rewrite rule for inf *)
    case: (cost(_: {m : msg, hm : hash})[true : finv sk hm]) => //.
  + move=> kh ks *. 
    (* FIXME Adrien: time [] optionel ? *)
    by proc (true) : time [ ].
  + move=> /=.
    by case: (cost(_: {b:bool, s:sign, hm:hash})[true : hm = f pk s]).
  wp; rnd => //=.
  + admit.
  (* FIXME Adrien: pourquoi is_lossless ? *)
  admit.
qed.

local lemma l5 &m :
  Pr[SCD(ASCD).main2(lam) @ &m: P res] <= Pr[OW(B(A)).main() @ &m : res].
proof.
  byequiv (: ={glob A} /\ p{1} = lam ==> P res{1} => res{2}) => //.
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
  + by proc; inline *; auto => /> /#.
  + by move=> *; proc; inline *; auto => /> /#.
  + by move=> *; proc; inline *; auto => /> /#.
  swap{1}5 -4. swap{1} 4 -2; wp.
  rnd (fun (h:msg -> hash) => fun m => finv sk{1} (h m))
      (fun (h:msg -> sign) => fun m => f pk{1} (h m)).
  rewrite /P; auto => |> k hk h _ bf _; split.
  + by move=> *; apply fun_ext => ?; smt(finv_f).
  smt(dfsign_dfhash f_finv finv_f).
qed.

lemma conclusion &m : 
  lam * (1%r - lam) ^ qs * Pr[EUF_QROM(A,FDH).main() @ &m : res] <=
  Pr[OW(B(A)).main() @ &m : res] + 8%r / 3%r * q%r ^ 4 * lam ^ 2. 
proof. move: (l1 A lam &m lam_bound) (l3 &m) (l4 &m) (l5 &m) => /#. qed.

end section OW.

end FDH_OW.

(* --------------------------------------------------------------------------*)
(* Proof assuming that f is a claw free permutation *)

abstract theory FDH_CF.

clone import T_ClawFree.

op lam : real.
axiom lam_bound : 0%r <= lam <= 1%r.

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
  auto => /> {&m}.
  move => k hk t _; split.
  + move=> hs _; apply fun_ext; smt (P2.finv_f finv_f).
  smt (dfsign_dfhash P2.f_finv f_finv).
qed.

lemma conclusion &m : 
  lam * (1%r - lam) ^ qs * Pr[EUF_QROM(A, FDH).main() @ &m : res] <= 
    Pr[ClawFree(B(A)).main() @ &m : res].
proof. move: (l1 A lam &m lam_bound) (l3 &m) => /#. qed.

end section.
end FDH_CF.





