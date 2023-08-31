require import Bool Core List DBool.

type key.
type plaintext.
type ciphertext.

module type Scheme = {
  proc init(): unit {}
  proc kg(): key
  proc enc(k:key,p:plaintext): ciphertext
  proc dec(k:key,c:ciphertext): plaintext option
}.

module type CPA_Oracles = {
  proc enc(p:plaintext): ciphertext
}.

module type CCA_Oracles = {
  proc enc(p:plaintext): ciphertext
  proc dec(c:ciphertext): plaintext option
}.

module type Adv_INDCPA (O:CPA_Oracles) = {
  proc choose(): plaintext * plaintext
  proc guess(c:ciphertext): bool
}.

module type Adv_INDCCA (O:CCA_Oracles) = {
  proc choose(): plaintext * plaintext
  proc guess(c:ciphertext): bool
}.

module Wrap (S:Scheme) = {
  var k:key
  var qs:ciphertext list

  proc init(): unit = {
    S.init();
    k  <@ S.kg();
    qs <- [];
  }

  proc enc(p:plaintext): ciphertext = {
    var r:ciphertext;

    r <@ S.enc(k,p);
    return r;
  }

  proc dec(c:ciphertext): plaintext option = {
    var r:plaintext option;

    qs <- c::qs;
    r  <@ S.dec(k,c);
    return r;
  }

  proc queried_challenge(c:ciphertext): bool = {
    return mem qs c;
  }
}.

module INDCPA (S:Scheme, A:Adv_INDCPA) = {
  module O = Wrap(S)
  module A = A(O)

  proc main(): bool = {
    var b, b':bool;
    var p, p0, p1:plaintext;
    var c:ciphertext;

    O.init();
    (p0,p1) <@ A.choose();
    b       <$ {0,1};
    p       <- if b then p1 else p0;
    c       <@ O.enc(p);
    b'      <@ A.guess(c);
    return (b = b');
  }
}.

module INDCCA (S:Scheme, A:Adv_INDCCA) = {
  module O = Wrap(S)
  module A = A(O)

  proc main(): bool = {
    var b, b', qc:bool;
    var p, p0, p1:plaintext;
    var c:ciphertext;

    O.init();
    (p0,p1) <@ A.choose();
    b       <$ {0,1};
    p       <- if b then p1 else p0;
    c       <@ O.enc(p);
    b'      <@ A.guess(c);
    qc      <@ O.queried_challenge(c);
    return (b = b' /\ !qc);
  }
}.

module ToCCA (A : Adv_INDCPA) (O : CCA_Oracles) = A(O).

lemma CCA_implies_CPA (S <: Scheme {-INDCPA}) (A <: Adv_INDCPA {-S, -INDCPA}) &m:
     equiv [S.init ~ S.init: true ==> ={glob S}]
  => Pr[INDCPA(S,A).main() @ &m: res] = Pr[INDCCA(S,ToCCA(A)).main() @ &m: res].
proof.
move=> init_is_init.
byequiv (: ={glob A} ==> ={res})=> //; proc.
call{2} (: Wrap.qs = [] ==> !res); first by proc; skip => /#.
conseq (: _ ==> Wrap.qs{2} = [] /\ (b = b'){1} = (b = b'){2}); first smt().
call (: ={glob Wrap, glob S} /\ Wrap.qs{2} = []).
+ by proc; call (: true).
call (: ={glob Wrap, glob S}).
+ by call (: true).
wp; rnd.
call (_: ={glob Wrap, glob S} /\ Wrap.qs{2} = []).
+ by proc; call (: true).
call (: ={glob A} ==> ={glob Wrap, glob S} /\ Wrap.qs{2} = [])=> //.
by proc; wp; call (: true); call init_is_init.
qed.
