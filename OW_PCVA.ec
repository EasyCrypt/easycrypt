require import Bool Core Int List Distr.
require import DBool.

type pkey, skey, ptxt, ctxt.

op dptxt : ptxt distr.
axiom dptxt_ll : is_lossless dptxt.
axiom dptxt_uni : is_uniform dptxt.
axiom dptxt_full : is_full dptxt.

module type Scheme = {
  (* Key generation *)
  proc kg () : pkey * skey

  (* Encryption *)
  proc enc (pk : pkey, m : ptxt) : ctxt

  (* Decryption *)
  proc dec (sk : skey, c : ctxt) : ptxt option
}.

module type OraclesT = {
  (* Plaintext checking oracle for *valid* cipher-texts *)
  proc ptxt_check (m : ptxt, c : ctxt) : bool

  (* Cipher-text validity oracle, except for the challenge cipher-text. *)
  proc ctxt_val (c : ctxt) : bool
}.

module type Inverter (S : Scheme) (O : OraclesT) = {
  proc invert(pk : pkey, c : ctxt) : ptxt
}.

module Oracles (S : Scheme) = {
  var sk : skey
  var c0 : ctxt

  proc init (sk : skey, c0 : ctxt) : unit = {
    sk <- sk;
    c0 <- c0;
  }

  proc ptxt_check (m : ptxt, c : ctxt) : bool = {
    var m0;

    m0 <@ S.dec (sk, c);    
    return is_none m0 \/ oget m0 = m;
  }

  proc ctxt_val (c : ctxt) : bool = {
    var m = None;
    if (c <> c0) {
      m <@ S.dec (sk,c);
    }

    return !is_none m;
  }
}.

module OW (S : Scheme) (I : Inverter) = {
  proc main(): bool ={
    var pk, sk, m, c, m';
    var is_inv : bool;

    (pk,sk) <@ S.kg();
    m       <$ dptxt;
    c       <@ S.enc (pk, m);
    Oracles(S).init(sk, c);

    (* The adversary tries to invert C *)
    m'      <@ I(S, Oracles(S)).invert(pk, c);

    (* We check if m' is the invert of c using the oracle.
       If the schema is correct here, i.e. if dec sk c = m, this corresponds
       to checking whether m = m'. *)
    is_inv  <@ Oracles(S).ptxt_check (m',c);
    return is_inv;
  }
}.
