require import AllCore List DBool SmtMap.

abstract theory SKE.

type key.
type plaintext.
type ciphertext.

module type SKE = {
  proc * init(): unit {}
  proc kg(): key
  proc enc(k:key,p:plaintext): ciphertext 
  proc dec(k:key,c:ciphertext): plaintext option
}.

module Correctness (S:SKE) = {
  proc main (p:plaintext) = {
    var k, c, q;
    S.init();
    k <@ S.kg();
    c <@ S.enc(k,p);
    q <@ S.dec(k,c);
    return q = Some p;
  } 
}.

end SKE.

abstract theory SKE_RND.

clone include SKE.

module type Oracles = {
  proc * init() : unit
  proc enc(p:plaintext): ciphertext 
  proc dec(c:ciphertext): plaintext option
}.

module type CCA_Oracles = {
  include Oracles [-init]
}.

module type CCA_Adv (O:CCA_Oracles) = {
  proc main() : bool 
}.

module type CPA_Oracles = {
  include Oracles [-init, dec]
}.

module type CPA_Adv (O:CPA_Oracles) = {
  proc main() : bool 
}.

module CCA_game(A:CCA_Adv, O:Oracles) = {
  proc main() = {
    var b;
    O.init();
    b <@ A(O).main();
    return b;
  }
}.

module CPA_game(A:CPA_Adv, O:Oracles) = CCA_game(A,O).

module Mem = {
  var k   : key
  var log :  (ciphertext, plaintext) fmap
  var lc  : ciphertext list
}.

(* ------------------------------------------------------------------ *)
(* Real word: simply call the encryption/decryption with the key      *)

module RealOrcls (S:SKE) : CCA_Oracles = {

  proc init() = {
    S.init();
    Mem.k <@ S.kg();
  }

  proc enc(p:plaintext) = {
    var c;
    c <@ S.enc(Mem.k,p);
    return c;
  }

  proc dec(c:ciphertext) = {
    var p;
    p <@ S.dec(Mem.k,c);
    return p;
  } 
}.

module CPA_CCA_Orcls(O:CPA_Oracles) : CCA_Oracles = {
  proc init () = {
    Mem.log <- empty;
    Mem.lc  <- [];
  }

  proc enc(p:plaintext) = {
    var c;
    c <@ O.enc(p);
    Mem.log.[c] <- p;
    return c;
  }

  proc dec(c:ciphertext) = {
     Mem.lc <- if c \in Mem.log then Mem.lc else c :: Mem.lc;
    return Mem.log.[c];
  } 
}.

module CCA_CPA_Adv(A:CCA_Adv, O:CPA_Oracles) = {
  proc main () = {
    var b;
    CPA_CCA_Orcls(O).init();
    b <@ A(CPA_CCA_Orcls(O)).main();
    return b;
  }
}.
      
(* ------------------------------------------------------------------- *)
(* In this game we log the answers to the encryption queries.          *)
(* We prove that if the scheme is correct this does not change.        *)

abstract theory CCA_CPA_UFCMA.

(* We assume that we have a deterministic and stateless algorithm for the decryption *)

type globS.
op enc : globS -> key -> plaintext -> ciphertext.
op dec : globS -> key -> ciphertext -> plaintext option.
op valid_key : key -> bool.
axiom dec_enc : 
  forall k, valid_key k =>
    forall gs p, dec gs k (enc gs k p) = Some p.

module type StLOrcls = {
  proc * init () : globS
  proc kg () : key
}.

module StLSke (StL:StLOrcls) : SKE = {
  var gs : globS

  proc init () = { 
    gs <- StL.init();
  }
 
  proc kg = StL.kg

  proc enc(k:key, p:plaintext) = {
    return enc gs k p;
  }

  proc dec(k:key, c:ciphertext) = {
    return dec gs k c;
  }

}.

module UFCMA(A:CCA_Adv, StL:StLOrcls) = 
  CPA_game(CCA_CPA_Adv(A), RealOrcls(StLSke(StL))).
(* event : exists c, c \in Mem.lc /\ dec StLSke.gs Mem.k c <> None *)

section PROOFS.

  declare module St : StLOrcls { StLSke, Mem }.
  axiom valid_kg : hoare [St.kg : true ==> valid_key res].

  declare module A  : CCA_Adv { StLSke, Mem, St }.
  axiom A_ll : forall (O <: CCA_Oracles{A}), islossless O.enc => islossless O.dec => islossless A(O).main.

  equiv eqv_CCA_UFCMA : CCA_game(A, RealOrcls(StLSke(St))).main ~ UFCMA(A, St).main :
     ={glob A} ==> !(exists c, c \in Mem.lc /\ dec StLSke.gs Mem.k c <> None){2} => ={res}.
  proof.
    proc; inline *; wp.
    call (_: (exists c, c \in Mem.lc /\ dec StLSke.gs Mem.k c <> None),
              ={StLSke.gs, Mem.k} /\ 
              valid_key Mem.k{1} /\
              (forall c, c \in Mem.log => dec StLSke.gs Mem.k c = Mem.log.[c]){2}).
    + by apply A_ll.
    + proc; inline *; conseq />.
      by auto => />; smt (mem_set get_setE dec_enc).
    + by move=> _ _; islossless.
    + by move=> _; conseq />; islossless.
    + by proc; inline *; auto => /> /#.
    + by move=> _ _; islossless.
    + by move=> _; proc; auto => /#.
    wp; conseq (_: ={glob A} ==> ={glob A, StLSke.gs, Mem.k}) (_: true ==> valid_key Mem.k) _ => />.
    + smt (mem_empty).
    + by call valid_kg.
    by sim.
  qed.

  lemma CCA_CPA_UFCMA &m : 
    Pr[CCA_game(A, RealOrcls(StLSke(St))).main() @ &m : res] <=
     Pr[CPA_game(CCA_CPA_Adv(A), RealOrcls(StLSke(St))).main() @ &m : res] + 
     Pr[UFCMA(A, St).main() @ &m : (exists c, c \in Mem.lc /\ dec StLSke.gs Mem.k c <> None)].
  proof. byequiv eqv_CCA_UFCMA => /> /#. qed.
  
end section PROOFS.

end CCA_CPA_UFCMA.

end SKE_RND.

