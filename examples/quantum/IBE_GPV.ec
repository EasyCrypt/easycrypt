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
  type hash <- pkey.

clone include T_CPA with
   type msg    <- msg,
   type cipher <- cipher,
   type pkey   <- pkey,
   type skey   <- skey.

(* --------------------------------------------------------------------------- *)
(* Security definition of IBE scheme in the QROM  *)

module type IBEScheme_QROM (H:QRO) = {
  proc kg() : mpkey * mskey
  proc extract(msk:mskey, id:identity) : skey
  proc enc(id:identity, m:msg) : cipher
  proc dec(sk:skey, c:cipher) : msg option
}.

quantum module type AdvIDCPA_QROM (H:QRO) (O:OrclIBE) = {
  proc choose (mpk:mpkey) : identity * msg * msg
  proc guess (c:cipher) : bool
}.

module IDCPA_QROM (A:AdvIDCPA_QROM) (S:IBEScheme_QROM) = {
  proc main() = {
    var b;
    QRO.init();
    b <@ IDCPA(A(QRO), S(QRO)).main();
    return b;
  }
}.

module type EncScheme0  = {
  proc enc (pk : pkey, m : msg): cipher   
  proc dec (sk : skey, c : cipher): msg option 
}.

module ES(E:EncScheme0) : EncScheme = {
  proc kg() : pkey * skey = {
    var mpk, msk, sk;
    (mpk, msk) <$ kg;
    sk <$ sampleD;
    return (f mpk sk, sk);
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
     
  proc enc(id:identity, m:msg) : cipher = {
    var pk, c;
    pk <@ H.h{id};
    c <@ E.enc(pk, m);
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

(* --------------------------------------------------------------------------- *)

section.

declare module E: EncScheme0 {-IDCPA, -QRO}.

declare module A : 
  AdvIDCPA_QROM { -IDCPA, -QRO, -E }[choose : `{Inf, #H.h : cqh, #O.extract : cqe},
                                 guess  : `{Inf, #H.h : gqh, #O.extract : gqe}].

(* FIXME: share this with FDH *)
import DBB.

lemma pr_dfbool_l lam m (l:identity list) q : 
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

local module IDCPA_QROM' (A:AdvIDCPA_QROM) (E:EncScheme0) = {
  var bf : identity -> bool

  proc main(lam_:real) = {
    var b;
    bf <$ dbfun lam_;
    b <@ IDCPA_QROM(A, GPV(E)).main();
    return b /\ (bf IDCPA.id /\ forall id', id' \in IDCPA.log => !bf id');
  }
}.

local lemma l1 lam &m:
  0%r <= lam <= 1%r =>
  Pr[IDCPA_QROM'(A,E).main(lam) @ &m : res] >=
    lam * (1%r - lam)^qe * Pr[IDCPA_QROM(A,GPV(E)).main() @ &m : res].
proof.
move=> lam_bound.
byphoare (:(glob A, glob E){m} = (glob A, glob E) /\ lam_ = lam ==> _) => //.
proc.
swap 1 1.
seq 1 : b Pr[IDCPA_QROM(A,GPV(E)).main() @ &m : res] (lam * (1%r - lam) ^ qe) 
          _ 0%r (lam_ = lam /\ (b => !IDCPA.id \in IDCPA.log /\ size IDCPA.log <= qe)).
+ inline *; wp.
  conseq (:size IDCPA.log <= qe) => />.
  (* FIXME: Adrien can we use complexity info here *)
  admit.
+ call (: (glob A, glob E){m} = (glob A, glob E) ==> res); 2: by auto.
  bypr => &m0 h.
  byequiv (: ={glob A, glob E} ==> ={res}) => //; 1: sim; move: h => />.
+ rnd (fun t => t IDCPA.id /\ forall id', id' \in IDCPA.log => ! t id').
  by skip => /> &hr h /h [] ??; apply: pr_dfbool_l.
+ by auto.
smt().
qed.

