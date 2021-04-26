require import AllCore List Distr DBool DList DProd CHoareTactic.
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

(* FIXME: move this in EUF ? *)
section. 

declare module A : 
  AdvEUF_QROM { -QRO, -EUF}[main : `{Inf, #H.h : qh, #S.sign : qs}].

hoare EUF_QROM_bound : EUF_QROM(A,FDH).main : 
   true ==> res => ! (EUF.m \in EUF.log) /\ size EUF.log <= qs.
proof.
  proc; inline *; wp.
  conseq (:size EUF.log <= qs) => />.
  (* FIXME: Adrien can we use complexity info here *)
  admit.
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
 
declare module A : 
  AdvEUF_QROM { -QRO, -EUF, - EUF_QROM'}[main : `{Inf, #H.h : qh, #S.sign : qs}].

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
+ by call (EUF_QROM_bound A); skip => />.
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

(* --------------------------------------------------------------------------*)
(* Proof assuming that f in OW *)

abstract theory FDH_OW_semi_constant.

(* FIXME: be undep of lam *)
op lam : real.
axiom lam_bound : 0%r < lam < 1%r.

clone import T_OW with 
  type init <- unit,
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

  proc main(pk:pkey, y:hash, i:unit) : sign = {
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
  rewrite /good; auto => /> k hk h _ bf _; split.
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
  type init <- int, 
  op dcodom <- dhash.

op q = qs + qh + 1.

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

section OW.

declare module A : AdvEUF_QROM { -QRO, -EUF , -B}
                     [main : `{Inf, #H.h : qh, #S.sign : qs}].

axiom A_ll (H <: QRO{-A}) (S <: OrclSign{-A}) : 
  islossless S.sign => islossless H.h => islossless A(H, S).main.

local clone import SmallRange.

local module G1(SR:SR) = {
  proc main (r:int) = {
    var b;
    b <@ EUF(A(SR), FDH(SR)).main();
    return b;
  }
}.

local lemma l1 r &m :
  0 < r => 
  Pr[EUF_QROM(A,FDH).main() @ &m : res] = Pr[IND_SR(SRO,G1).main(r) @ &m : res].
proof.
  move=> hr; byequiv => //; proc; inline *; wp; sim.
  rnd{2}; auto => />; apply dfun_ll => /=; apply DInterval.dinter_ll => /#.
qed.

local lemma l2 r &m :
  0 < r => 
  `| Pr[IND_SR(SRO,G1).main(r) @ &m : res] - Pr[IND_SR(SR,G1).main(r) @ &m : res] | <= 27%r * q%r^3 / r%r.
proof.
  apply (SmallRange.advantage q r G1).
  admit.
qed.

local clone import Collision with 
  type input <- int,
  type hash <- int.

local module G2 (H:QROd) = {
  module RO = { 
    quantum proc h {x:msg} = { 
      quantum var i;
      i <@ H.h{x};
      return (nth witness SR.rh i);
    }
  }

  proc main(r:int) = {
    var b; 
    SR.rh <$ dlist dhash r; 
    b <@ EUF(A(RO), FDH(RO)).main();
    return EUF.m :: EUF.log;
  }
}.

local lemma l3 r &m:
  0 < r => 
  Pr[IND_SR(SR,G1).main(r) @ &m : res] <= 
    Pr[IND_SR(SR,G1).main(r) @ &m : res /\ !SR.fr EUF.m \in map SR.fr EUF.log ] + 
    q%r^3 / r%r.
proof.
  have -> : Pr[IND_SR(SR,G1).main(r)@ &m : res] =
     Pr[IND_SR(SR,G1).main(r) @ &m : res /\ !SR.fr EUF.m \in map SR.fr EUF.log \/ 
                                     res /\ SR.fr EUF.m \in map SR.fr EUF.log].
  + rewrite Pr[mu_eq] => /#.
  move=> hr;rewrite Pr[mu_disjoint];1: smt().
  apply ler_add2l.
  have := pr_col (inv r%r) [0..r-1] r q G2 _ &m _.
  + admit.
  + by move=> m; rewrite DInterval.dinter1E /#.
  apply ler_trans.
  byequiv => //; proc; inline *; wp.
  conseq (: SR.fr{1} = QROd.h{2} /\ ={EUF.log, EUF.m}) _ (: _ ==> size EUF.log <= qs).
  + move=> />. smt (mapP ge0_qh).
  + admit.
  call (: QRO.h{1} = (fun x => nth witness SR.rh{1} (QROd.h{2} x)) /\ 
            ={EUF.log, EUF.sk, SR.rh}).
  + by proc; inline *; auto.
  + by proc; inline *; auto.
  by swap{2} [2..3]-1; auto => />.
qed.

local module G3 = {
  var i : int

  proc main(r:int) = {
    var b;
    b <@ IND_SR(SR,G1).main(r);
    b <- b /\ !SR.fr EUF.m \in map SR.fr EUF.log;
    i <$ [0..r-1];
    return (b /\ SR.fr EUF.m = i);
  }
}.

local lemma l4 r_ &m : 
  0 < r_ =>
  Pr[G3.main(r_) @ &m : res] >= inv(r_%r) * 
    Pr[IND_SR(SR,G1).main(r_) @ &m : res /\ !SR.fr EUF.m \in map SR.fr EUF.log ].
proof. 
move=> hr.
byphoare (:(glob A){m} = glob A /\ r = r_ ==> _) => //.
proc.
seq 2 : b Pr[IND_SR(SR,G1).main(r_) @ &m : res /\ !SR.fr EUF.m \in map SR.fr EUF.log] (inv r%r)
          _ 0%r (r = r_ /\ 0 <= SR.fr EUF.m < r).
+ inline *; wp.
  conseq (: forall x, 0 <= SR.fr x < r); 1: by move=> /> m0 ? /(_ m0) />.
  call (: true) => //; auto => /> rh _ fr /dfun_supp /= h _ _ x. 
  by have /DInterval.supp_dinter /# := h x.
+ wp.
  call (: (glob A){m} = glob A /\ r = r_ ==> res /\ !SR.fr EUF.m \in map SR.fr EUF.log); 2: by auto.
  bypr => &m0 h.
  byequiv (: ={glob A, arg} ==> ={res, EUF.m, EUF.log, SR.fr}) => //; 1: by sim.
  by move: h => />.
+ by conseq />; rnd (pred1 (SR.fr EUF.m)); skip => />; smt (DInterval.dinter1E).
+ by auto.
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

local lemma l5 &m r_ :
  0 < r_ =>
  Pr[G3.main(r_) @ &m : res] <= Pr[OW(B(A)).main(r_) @ &m : res].
proof.
  move=> hr; byequiv => //; proc; symmetry.
  inline *; swap{2} -20; wp. 
  call (_: exists m', m' \in EUF.log /\ SR.fr m' = G3.i, 
           ={QRO.h, EUF.log} /\ 
           (forall m, SR.fr{2} m <> G3.i{2} => B.hs{1} m = (finv EUF.sk (QRO.h m)){2})) => //.
  + by apply A_ll.
  + by proc; inline *; auto => /> /#.
  + by move=> *; islossless.
  + by move=> *; proc; inline *; auto => /> /#.
  + by proc; inline *; auto.
  + by move=> *; islossless. 
  + by move=> *; proc; inline *; auto.
  swap{2} 8 -7; wp. swap{2} [3..4] -2.
  swap{1} 5 -4; sp. swap{1} 11 -2. swap{1} [6..9] -3. swap{1} 2 2; wp.
  seq 2 2 : (#pre /\ (pk,sk){1} = k{2} /\ i0{1} = G3.i{2} /\ (pk,sk){1} \in kg /\ 0 <= G3.i{2} < r_).
  + by conseq />; auto => />; smt(DInterval.supp_dinter).
  rnd; conseq (: SR.rh{2} = (map (f pk) rs1 ++ y :: map (f pk) rs2){1} /\ size rs1{1} = i0{1} /\
                 size rs2{1} = r{1} - i0{1} - 1).
  + move=> /> &1 &2 hk ?? rs1 rs2 y <<- ? fr /dfun_supp /= hfr; split.
    + move=> m' hm'; rewrite !nth_cat size_map /=.
      have /DInterval.supp_dinter hfrm' := hfr m'.
      case: (fr m' < size rs1) => ?.
      + by rewrite (nth_map witness witness (f pk{1}) (fr m')) 1:/# (finv_f _ _ hk). 
      rewrite (nth_map witness witness (f pk{1})); smt(finv_f).
    smt (finv_f f_finv nth_cat size_map mapP).
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
  + admit.
  move=> _ rs1; rewrite supp_dlist 1:// => -[] <<- ?; split.
  + rewrite supp_dlist 1:// size_map /= allP => *; apply dhash_fu.
  move=> _; split.
  + rewrite -map_comp -{1}(map_id rs1); apply eq_map.
    by move=> x; rewrite /(\o) (finv_f _ _ hk).
  move=> _ y hy; split.
  + move=> rs2 ?; rewrite -map_comp -{1}(map_id rs2); apply eq_map.
    by move=> x; rewrite /(\o) (f_finv _ _ hk).
  move=> _; split.
  + admit.
  move=> _ rs2; rewrite supp_dlist 1:/# => -[] hrs2 ?; split.
  + rewrite supp_dlist 1:/# size_map hrs2 /= allP => *; apply dhash_fu.
  move=> _; split => //.
  rewrite -map_comp -{1}(map_id rs2); apply eq_map.
  by move=> x; rewrite /(\o) (finv_f _ _ hk).
qed.

lemma conclusion &m : 
  let k = 28%r * q%r^3 in
  let eps = Pr[EUF_QROM(A,FDH).main() @ &m : res] in
  let r = 3 * floor (k / eps) in 
  eps ^2 / (6%r * k) <= Pr[OW(B(A)).main(r) @ &m : res].
proof.
  move=> /=. 
  case: (Pr[EUF_QROM(A, FDH).main() @ &m : res] = 0.0).
  + by move=> -> /=; rewrite expr0z /=; smt(mu_bounded).
  have gt0_q3 : 1%r <= q%r ^ 3 by apply exprn_ege1 => //; smt (gt0_qs ge0_qh).
  move=> eps0; have heps : 0%r < Pr[EUF_QROM(A, FDH).main() @ &m : res] by smt(mu_bounded).
  have gt0_r : 0 < 3 * floor((28%r * q%r^3) / Pr[EUF_QROM(A, FDH).main() @ &m : res]).
  + have : 1%r <= (28%r * q%r^3) / Pr[EUF_QROM(A, FDH).main() @ &m : res]; last by smt(floor_gt).
    rewrite ler_pdivl_mulr //=; smt(mu_bounded). 
  move: eps0 heps gt0_r.
  pose k := 28%r * q%r^3.
  pose eps := Pr[EUF_QROM(A,FDH).main() @ &m : res].
  pose r := 3 * floor(k/eps); move => eps0 heps gt0_r.
  apply : ler_trans (l5 &m r gt0_r).
  apply : ler_trans (l4 r &m gt0_r).
  apply (ler_trans (inv r%r * (Pr[IND_SR(SRO, G1).main(r) @ &m : res] - 28%r*q%r ^ 3 / r%r))); last first.
  + by move: (l2 r &m gt0_r) (l3 r &m gt0_r) => /#.
  rewrite -(l1 r &m gt0_r) -/eps. 
  apply (ler_trans ((eps/(3%r*k))*(eps/2%r))); 1: by rewrite expr2; smt().
  have h0k: 0%r < k by smt().
  have hepsk : 0%r <= eps/k by smt().
  have hepsr : eps / (3%r*k) <= inv r%r. 
  + have -> : eps/(3%r*k) = inv(3%r*k/eps) by smt().
    by rewrite lef_pinv; smt (floor_bound).
  apply ler_pmul => //; 1,2:smt(). 
  have /# : 28%r * q%r ^ 3 / r%r <= eps/2%r.
  rewrite -/k ler_pdivl_mulr 1:// mulrC mulrA ler_pdivr_mulr 1:/#.
  rewrite (mulrC eps) -ler_pdivr_mulr 1:// -mulrA mulrC -ler_pdivl_mulr 1://. 
  have : 3%r <= k / eps.
  + apply (ler_trans k); 1: smt().
    rewrite ler_pdivl_mulr 1://; have /#: eps <= 1%r by smt(mu_bounded). 
  smt (floor_bound).
qed.

end section OW.

end FDH_OW_small_range.
