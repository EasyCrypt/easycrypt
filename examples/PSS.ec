require import Fun.
require import Int.

(*** General definitions *)
(** Lengths *)
op k:int.
axiom leq0_k: 0 < k.

op k0:int.
axiom leq0_k0: 0 < k0.

op k1:int.
axiom leq0_k1: 0 < k1.

axiom constraints:
  k0 + k1 <= k - 1.

op kg:int = k - k1 - 1.
lemma leq0_kg1: 0 < kg by [].

op kg2:int = k - k0 - k1 - 1.
lemma leq0_kg2: 0 <= kg2 by [].

op k':int = k - 1.
lemma leq0_k': 0 <= k' by [].

(** Types *)
require AWord.
require import ABitstring.

type message = bitstring.

(* Signatures *)
type signature.
clone import AWord as Signature with
  type word <- signature,
  op length <- k.

(* Nonce *)
type salt.
clone import AWord as Salt with
  type word <- salt,
  op length <- k0.
op sample_salt = Salt.Dword.dword.

(* Output of H *)
type htag.
clone import AWord as HTag with
  type word <- htag,
  op length <- k1.
op sample_htag = HTag.Dword.dword.

(* Output of G *)
type gtag.
clone import AWord as GTag with
  type word <- gtag,
  op length = kg.
op sample_gtag = GTag.Dword.dword.

(* Output of G2 [G1 produces an HTag] *)
type g2tag.
clone import AWord as G2Tag with
  type word <- g2tag,
  op length = kg2.

(* Domain of RSA *)
op sample_plain: signature distr. (* Whereby we sample only with the first byte/bit set to 0 *)

(** Instantiating *)
require PKS.
require OW.
require RandOrcl.

clone export OW as RSA with
  type t <- signature,
  op sample_t <- sample_plain,
  op f_dom = (lambda (pk:pkey) (x:signature), cpTrue x),
  op f_rng = (lambda (pk:pkey) (x:signature), cpTrue x),
  op finv_dom = (lambda (sk:skey) (x:signature), cpTrue x),
  op finv_rng = (lambda (sk:skey) (x:signature), cpTrue x)
  proof f_rng_sub_finv_dom by smt,
        finv_rng_sub_f_dom by smt,
        f_dom_sample_t by smt.

clone export RandOrcl as H with
  type from <- message,
  type to <- htag,
  op dsample <- sample_htag,
  op default = HTag.zeros.

clone export RandOrcl as G with
  type from <- htag,
  type to <- gtag,
  op dsample <- sample_gtag,
  op default = GTag.zeros.

clone export PKS as PKSi with
  type pkey <- pkey,
  type skey <- skey,
  type message <- message,
  type signature <- signature.

(*** Defining PSS *)
print theory GTag.
module PSS(G:G.Oracle,H:H.Oracle): Scheme = {
  fun init(): unit = {
    G.init();
    H.init();
  }

  fun g1(x:htag):salt = {
    var r:gtag;
    r  = G.o(x);
    return Salt.from_bits (sub (to_bits r) 0 k0);
  }

  fun g2(x:htag):g2tag = {
    var r:gtag;
    r  = G.o(x);
    return G2Tag.from_bits (sub (to_bits r) k0 kg2);
  }

  (* Keygen: make it a wrapped pop *)
  fun keygen():(pkey * skey) = {
    var (pk, sk):(pkey * skey);
    (pk,sk) = $keypairs;
    return (pk,sk);
  }

  (* Sign *)
  fun sign(sk:skey, m:message):signature = {
    var r:salt;
    var rMask:salt;
    var maskedR:salt;
    var w:htag;
    var gamma:g2tag;
    var y:signature;

    r = $sample_salt;
    w  = H.o(m || (to_bits r));
    rMask  = g1(w);
    maskedR = rMask ^ r;
    gamma  = g2(w);
    y = Signature.from_bits (zeros 1 || (to_bits w) || (to_bits maskedR) || (to_bits gamma));
    return (finv sk y); (* For fault injection, we will later refine this; we should make it a function so it can be reasoned about separately *)
  }

  (* Verify *)
  fun verify(pk:pkey, m:message, s:signature):bool = {
    var y:signature;
    var w:htag;
    var w':htag;
    var maskedR:salt;
    var gamma:g2tag;
    var gamma':g2tag;
    var rMask:salt;
    var r:salt;
    var b:bool;

    y = (f pk s);
    b = (sub (to_bits y) 0 1 <> zeros 1);
    w = HTag.from_bits (sub (to_bits y) 1 k1);
    maskedR = Salt.from_bits (sub (to_bits y) (k1 + 1) k0);
    gamma = G2Tag.from_bits (sub (to_bits y) (k1 + k0 + 1) kg2);
    rMask  = g1(w);
    r = rMask ^ maskedR;
    w'  = H.o(m || to_bits r);
    gamma'  = g2(w);
    return (w = w' /\ gamma = gamma' /\ !b);
  }
}.
