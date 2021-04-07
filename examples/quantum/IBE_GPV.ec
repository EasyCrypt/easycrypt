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

(* --------------------------------------------------------------------------- *)
(* GPV scheme                                                                  *)

module GPV (E:EncScheme) (H:QRO) = {
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
op qe : { int | 0 <= qe } as ge0_qe.
op qh : { int | 0 <= qh } as ge0_qh.

(* --------------------------------------------------------------------------- *)

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

module IDCPA_QROM' (A:AdvIDCPA_QROM) (E:EncScheme) = {
  var bf : identity -> bool

  proc main(lam_:real) = {
    var b;
    bf <$ dbfun lam_;
    b <@ IDCPA_QROM(A, GPV(E)).main();
    return b /\ (bf IDCPA.id /\ forall id', id' \in IDCPA.log => !bf id');
  }
}.


