require import AllCore List Distr.
require (*--*) PROM PKE_CPA KEM_CCA OW_PCVA.

(* Types of public/private keys, plain-texts, ciphertexts, randomness and 
   hashes. *)
type pkey, skey, ptxt, ctxt, rand, hash.

op drand : rand distr.
axiom drand_ll : is_lossless drand.
axiom drand_funi : is_funiform drand.

op dptxt : ptxt distr.
axiom dptxt_ll : is_lossless dptxt.
axiom dptxt_funi : is_uniform dptxt.

hint solve 0 random : drand_ll drand_funi dptxt_ll dptxt_funi.


(**********************************************************)
(* PKE Scheme with deterministic randomness *)

  (* Key generation *)
op kg : (pkey * skey) distr.

  (* Encryption, deterministic and randomized version. *)
op d_enc (pk:pkey, m:ptxt, r:rand) : ctxt.

op enc (pk:pkey, m:ptxt) : ctxt distr = dmap drand (d_enc pk m).

op dec (sk:skey, c:ctxt) : ptxt option.

op pk_of_sk (sk:skey) : pkey.

axiom pk_of_sk_sound (sk : skey) (pk, pk' : pkey) :
  support kg (pk, sk) => pk_of_sk sk = pk' => pk = pk'.

module Scheme = {
  proc kg () : pkey * skey = { 
    var psk;
    psk <$ kg;
    return psk;
 }

  proc enc (pk:pkey, m:ptxt) : ctxt = {
    var c;
    c <$ enc pk m;
    return c;
 }

  proc d_enc (pk:pkey, m:ptxt, r:rand) : ctxt = {
    return (d_enc pk m r);
 }

  proc dec (sk:skey, c:ctxt) : ptxt option = {
    return (dec sk c);
 }
}.


(**********************************************************)
(* Gamma-spread hypothesis necessary condition *)
op gamma : int.

axiom gamma_spread_coll (pk : pkey) (m : ptxt) (c : ctxt):
  exists (sk : skey), support kg (pk, sk) =>
  mu1 (enc pk m) c <= 2%r^(-gamma).


(**********************************************************)
(* OW-PCVA Security Game *)
clone import OW_PCVA as OW_PCVA_CPA with
  type pkey <- pkey,
  type skey <- skey,
  type ptxt <- ptxt,
  type ctxt <- ctxt.


(**********************************************************)
(* PKE IND-CPA *)
clone import PKE_CPA as IND_CPA with
  type pkey <- pkey,
  type skey <- skey,
  type ptxt <- ptxt,
  type ctxt <- ctxt.

print IND_CPA.


(**********************************************************)
(* KEM IND-CCA *)
clone import KEM_CCA as KEM_INC_CCA with
  type pkey  <- pkey,
  type skey  <- skey,
  type Key   <- hash,
  type encap <- ctxt.


(**********************************************************)
(* PROM *)
type string.

op s_ptxt (m : ptxt) : string.
op s_cptxt (c : ctxt) (m : ptxt) : string.

axiom s_ptxt_inj (m1 m2 : ptxt) : s_ptxt m1 = s_ptxt m2 => m1 = m2.
axiom s_cptxt_inj (c1 c2 : ctxt) (m1 m2 : ptxt) :
  s_cptxt c1 m1 = s_cptxt c1 m2 => m1 = m2 /\ c1 = c2.

op to_rand (h : hash) : rand.
axiom t_rand_inj (h1 h2 : hash) : to_rand h1 = to_rand h2 => h1 = h2.

op dhash (m : string) : hash distr.
axiom dhash_ll : forall m, is_lossless (dhash m).

hint solve 0 random : dhash_ll.

clone import PROM.GenEager as ROM with 
  type from <- string,
  type to <- hash,
  op sampleto <- dhash,
  type input <- unit,
  type output <- bool
  proof *. 
  realize sampleto_ll by solve (random). 


(**********************************************************)
(* Correction Assumption *)

module type Adv = {
  proc a (sk : skey, pk : pkey) : ptxt
}.

module Cor (A : Adv) = {
  proc main () = {
    var pk, sk, r, m;
    
    (pk,sk) <$ kg;
    m   <@ A.a(sk, pk);
    r   <$ drand; 
    return (dec sk (d_enc pk m r) <> Some m);
  }
}.

(* Probability of error. *)
op delt : real.

(* Correction assumption. *)
axiom corr_assum (A <: Adv) &m : Pr[Cor(A).main() @ &m: res] <= delt.


(**********************************************************)
(* Equivalence between the correction game and an alternative formulation, 
  using a submit oracle. *)

module type Submit = {
  proc sub (m : ptxt) : rand
}.

module type AdvS (S : Submit) = {
  proc a (sk : skey, pk : pkey) : unit
}.

module CorS (A : AdvS) = {
  var m : ptxt
  var r : rand
  var b : bool
  
  module S : Submit = {
    proc sub (m0 : ptxt) = {
      if (!b) {
        m <- m0;
        b <- true;
      }
      return r; }}

  proc main () = {
    var pk, sk;
    
    m <- witness;
    b <- false;
    r <$ drand;

    (pk,sk) <$ kg;
    A(S).a(sk, pk);
    return (dec sk (d_enc pk m r) <> Some m);
  }
}.


(* Cor to CorS *)

module B (A : Adv) (S : Submit) = {
  proc a (sk : skey, pk : pkey) = {
    var m;
    m <@ A.a(sk,pk);
    S.sub (m);    
  }
}.

lemma Cor_to_CorS (A <: Adv {-CorS}) : 
    equiv [CorS(B(A)).main ~ Cor(A).main: ={glob A} ==> ={res}].
proof.
  by proc; inline*; wp; swap {2} -2; call (_: true); auto.
qed.


(* CorS to Cor *)

module C (A : AdvS) = {
  var m : ptxt
  var b : bool

  module S : Submit = {
    proc sub (m0 : ptxt) : rand = {
      if (!b) {
        m <- m0;
        b <- true;
      }
      return witness; }}

  proc a (sk : skey, pk : pkey) = {
    m <- witness;
    b <- false;
    A(S).a(sk,pk);
    return m;
  }
}.

lemma CorS_to_Cor (A <: AdvS {-CorS, -C}) : 
    equiv [CorS(A).main ~ Cor(C(A)).main: ={glob A} ==> ={res}].
proof.
 proc; inline*; swap {2} -7; wp. 
 call (_: C.b,                  (* bad *)
          C.b{2} = CorS.b{1} /\ C.m{2} = CorS.m{1},  (* if not bad *)
          C.b{2} = CorS.b{1} /\ C.m{2} = CorS.m{1}). (* if bad *)
 admit.   (* TODO: add the losslessness assumptions*)
 proc; auto.
 move => &2 h; proc; rcondf ^if; auto.
 move => &1; proc; rcondf ^if; auto.
 auto => />; smt ().
qed.


(**********************************************************)
(* Transformation T : IND_CPA ==> OW_PCVA *)

module T (H : ROM.RO) = {
  proc kg () : pkey * skey = { 
    var psk;
    psk <$ kg;
    return psk;
  }

  proc enc (pk:pkey, m:ptxt) : ctxt = {
    var h, r, c;
    h <@ H.get(s_ptxt m);
    r <- to_rand h;
    c <- d_enc pk m r;
    return c;
  }

  proc dec (sk:skey, c:ctxt) : ptxt option = {
    var m, c'; 

    (* We decrypt c *)
    m <- dec sk c;
    (* We re-encrypt c, and check that this yields the same message. *)
    if (!is_none m){      
      c' <@ enc (pk_of_sk sk, oget m);
      m <- (c = c')? m : None;
    }
    
    return m;
  }
}.


(**********************************************************)
(* Game hop G0 => G1 *)

module type InverterO (H : RO) (S : Scheme) (O : OraclesT) = {
  proc invert(pk : pkey, c : ctxt) : ptxt
}.

print RO.

module LH (H : RO) : RO = {
  var log: (string * hash) list

  proc init () = {
    log <- [];
    H.init ();
  }

  proc get(x : string) = {
  var r;
    
  r    <@ H.o(x);
  logH <- (x,r)::logH;
  return r;
  }
}

  module G' = {
    proc o(x : htag) = {
      var r;

      r    <@ G.o(x);
      logG <- (x,r)::logG;
      return r;
    }
  }

module Oracles0 (H : RO) = OW_PCVA_CPA.Oracles (T (H)).

module Oracles1 (H : RO) = {
  var sk : skey
  var c0 : ctxt

  proc init (sk : skey, c0 : ctxt) : unit = {
    sk <- sk;
    c0 <- c0;
  }

  proc ptxt_check (m : ptxt, c : ctxt) : bool = {
    var m0, c0;

    m0 <- dec sk c;
    if (!is_none m0) {
      c0 <@ T(H).enc (pk_of_sk sk, oget m0);
    }
    return is_none m0 \/ (oget m0 = m /\ c0 = c);
  }

  proc ctxt_val (c : ctxt) : bool = {
    var m = None;
    if (c <> c0) {
      m <@ S.dec (sk,c);
    }

    return !is_none m;
  }
}.


module Game0 (A : InverterO) (H : RO) (
