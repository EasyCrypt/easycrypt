require import AllCore List Distr.
require (*--*) ROM PKE_CPA KEM_CCA.

(* Types of public/private keys, plain-texts, ciphertexts, randomness and 
   hashes. *)
type pkey, skey, ptxt, ctxt, rand, hash.

op drand : rand distr.
axiom drand_ll : is_lossless drand.
axiom drand_uni : is_uniform drand.
axiom drand_full : is_full drand.

op dptxt : ptxt distr.
axiom dptxt_ll : is_lossless dptxt.
axiom dptxt_uni : is_uniform dptxt.
axiom dptxt_full : is_full dptxt.

(* Key generation *)
op kg : (pkey * skey) distr.

(* Encryption, deterministic and randomized version. *)
op d_enc (pk:pkey, m:ptxt, r:rand) : ctxt.

op enc (pk:pkey, m:ptxt) : ctxt distr = dmap drand (d_enc pk m).

op dec (pk:skey, m:ctxt) : ptxt option.


(**********************************************************)
(* Gamma-spread hypothesis necessary condition *)
op gamma : int.

module GammaCol = {
  proc col (pk : pkey, m : ptxt, c : ctxt) : bool = {
    var c';
    c' <$ enc pk m;
    return (c = c');
  }
}.

axiom gamma_spread_coll (pk : pkey) (m : ptxt) (c : ctxt) &m:
  Pr[GammaCol.col(pk, m, c) @ &m : res = true] <= 2%r^(-gamma).


(**********************************************************)
(* OW-PCVA Security Game *)

module type OW_OraclesT = {
  (* Plaintext checking oracle for *valid* cipher-texts *)
  proc ptxt_check (m : ptxt, c : ctxt) : bool

  (* Cipher-text validity oracle, except for the challenge cipher-text. *)
  proc ctxt_val (c : ctxt) : bool
}.

module type Inverter (O : OW_OraclesT) = {
  proc invert(pk : pkey, c : ctxt) : ptxt
}.


module OW_Oracles = {
  var sk : skey
  var c0 : ctxt

  proc init (sk : skey, c0 : ctxt) : unit = {
    sk <- sk;
    c0 <- c0;
  }

  proc ptxt_check (m : ptxt, c : ctxt) : bool = {
    var m0;

    m0 <- dec sk c;    
    return is_none m0 \/ oget m0 = m;
  }

  proc ctxt_val (c : ctxt) : bool = {
    var m = None;
    if (c <> c0) {
      m <- dec sk c;
    }

    return !is_none m;
  }
}.

module OW_Gen (I : Inverter) = {
  proc main(): bool ={
    var pk, sk, m, c, m';
    var is_inv : bool;

    (pk,sk) <$ kg;
    m       <$ dptxt;
    c       <$ enc pk m;
    OW_Oracles.init(sk, c);

    (* The adversary tries to invert C *)
    m'      <@ I(OW_Oracles).invert(pk, c);

    (* We check if m' is the invert of c using the oracle.
       If the schema is correct here, i.e. if dec sk c = m, this corresponds
       to checking whether m = m'. *)
    is_inv  <@ OW_Oracles.ptxt_check (m',c);
    return is_inv;
  }
}.


(**********************************************************)
(* PKE IND-CPA *)
clone import PKE_CPA as IND_CPA with
  type pkey <- pkey,
  type skey <- skey,
  type ptxt <- ptxt,
  type ctxt <- ctxt.


(**********************************************************)
(* KEM IND-CCA *)
clone import KEM_CCA as IND_CCA with
  type pkey  <- pkey,
  type skey  <- skey,
  type Key   <- hash,
  type encap <- ctxt.
  

print IND_CCA.
