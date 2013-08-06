require import Fun.
require import Int.
require import Real.
require import FSet.
require import Option.

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
axiom htagL: mu sample_htag cpTrue = 1%r.

(* Output of G *)
type gtag.
clone import AWord as GTag with
  type word <- gtag,
  op length = kg.
op sample_gtag = GTag.Dword.dword.
axiom gtagL: mu sample_gtag cpTrue = 1%r.

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
require RandomOracle.

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

clone export RandomOracle as Ht with
  type from <- message,
  type to <- htag,
  op dsample <- sample_htag.

clone export RandomOracle as Gt with
  type from <- htag,
  type to <- gtag,
  op dsample <- sample_gtag.

clone export PKS as PKSi with
  type pkey <- pkey,
  type skey <- skey,
  type message <- message,
  type signature <- signature.

(*** Defining PSS *)
module PSS(G:Gt.Oracle,H:Ht.Oracle): Scheme = {
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

(** EF-CMA security of PSS *)
(* A CMA adversary with access to two random oracles *)
module type CMA_2RO(G:Gt.ARO,H:Ht.ARO,S:AdvOracles) = {
  fun forge(pk:pkey): message * signature
}.

section.
declare module G:Gt.Oracle {EF_CMA.WrapEF}.
axiom correct_G: mu sample_gtag cpTrue = 1%r =>
  equiv [Gt.Correct(G).call2 ~ Gt.Correct(G).call1: ={glob G, x} ==> ={glob G} /\ res{1} = (res,res){2}].
local module CorrectG = Correct(G).

declare module H:Ht.Oracle {EF_CMA.WrapEF,G}.

declare module Adv:CMA_2RO {G,H,EF_CMA.WrapEF(PSS(G,H))}.
axiom AdvL (G<:Gt.Oracle) (H<:Ht.Oracle):
  islossless G.o => islossless H.o =>
  islossless Adv(G,H,EF_CMA.WrapEF(PSS(G,H))).forge.

(* Folding in the two calls to G *)
local module PSS'(G:Gt.Oracle,H:Ht.Oracle): Scheme = {
  fun init(): unit = {
    G.init();
    H.init();
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
    var g,g':gtag;
    var rMask:salt;
    var maskedR:salt;
    var w:htag;
    var gamma:g2tag;
    var y:signature;

    r = $sample_salt;
    w  = H.o(m || (to_bits r));
    (g,g') = CorrectG.call2(w);
    rMask = Salt.from_bits (sub (to_bits g) 0 k0);
    maskedR = rMask ^ r;
    gamma  = G2Tag.from_bits (sub (to_bits g') k0 kg2);
    y = Signature.from_bits (zeros 1 || (to_bits w) || (to_bits maskedR) || (to_bits gamma));
    return (finv sk y); (* For fault injection, we will later refine this; we should make it a function so it can be reasoned about separately *)
  }

  (* Verify *)
  fun verify(pk:pkey, m:message, s:signature):bool = {
    var y:signature;
    var g, g':gtag;
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
    (g,g') = CorrectG.call2(w);
    rMask  = Salt.from_bits (sub (to_bits g) 0 k0);
    r = rMask ^ maskedR;
    w'  = H.o(m || to_bits r);
    gamma'  = G2Tag.from_bits (sub (to_bits g') k0 kg2);
    return (w = w' /\ gamma = gamma' /\ !b);
  }
}.

local equiv PSS_PSS':
  PKSi.EF_CMA.EF_CMA(EF_CMA.WrapEF(PSS(G,H)),Adv(G,H)).main ~
  PKSi.EF_CMA.EF_CMA(EF_CMA.WrapEF(PSS'(G,H)),Adv(G,H)).main:
  ={glob Adv} ==> ={res}.
proof.
fun.
call (_: ={EF_CMA.WrapEF.qs, m} ==> ={res});
  first by fun; wp.
call (_: ={glob H, glob G, EF_CMA.WrapEF.pk, m, s} ==> ={res});
  first by fun; call (_: ={glob H, glob G, EF_CMA.WrapEF.pk, pk, m, s} ==> ={res})=> //;
             fun; inline PSS(G,H).g1 PSS(G,H).g2 CorrectG.call2;
                  swap{1} 11 -4; swap{1} 12 -3; eqobs_in; wp; eqobs_in.
call (_: ={glob H, glob G, glob EF_CMA.WrapEF}).
  fun; call (_: ={glob H, glob G, EF_CMA.WrapEF.sk, sk, m} ==> ={glob H, glob G, EF_CMA.WrapEF.sk, res});
    last by wp.
    fun; inline PSS(G,H).g1 PSS(G,H).g2 CorrectG.call2;
         swap{1} 7 -3; swap{1} 8 -2; eqobs_in; wp; eqobs_in.
  by fun (={glob G, glob EF_CMA.WrapEF}).
  by fun (={glob H, glob EF_CMA.WrapEF}).
call (_: true ==> ={glob H, glob G, glob EF_CMA.WrapEF, res})=> //.
  by fun; eqobs_in.
qed.

local module PSS''(G:Gt.Oracle,H:Ht.Oracle): Scheme = {
  fun init(): unit = {
    G.init();
    H.init();
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
    var g:gtag;
    var rMask:salt;
    var maskedR:salt;
    var w:htag;
    var gamma:g2tag;
    var y:signature;

    r = $sample_salt;
    w  = H.o(m || (to_bits r));
    g = CorrectG.call1(w);
    rMask = Salt.from_bits (sub (to_bits g) 0 k0);
    maskedR = rMask ^ r;
    gamma  = G2Tag.from_bits (sub (to_bits g) k0 kg2);
    y = Signature.from_bits (zeros 1 || (to_bits w) || (to_bits maskedR) || (to_bits gamma));
    return (finv sk y); (* For fault injection, we will later refine this; we should make it a function so it can be reasoned about separately *)
  }

  (* Verify *)
  fun verify(pk:pkey, m:message, s:signature):bool = {
    var y:signature;
    var g:gtag;
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
    g = CorrectG.call1(w);
    rMask  = Salt.from_bits (sub (to_bits g) 0 k0);
    r = rMask ^ maskedR;
    w'  = H.o(m || to_bits r);
    gamma'  = G2Tag.from_bits (sub (to_bits g) k0 kg2);
    return (w = w' /\ gamma = gamma' /\ !b);
  }
}.

local equiv PSS'_PSS'':
  PKSi.EF_CMA.EF_CMA(EF_CMA.WrapEF(PSS'(G,H)),Adv(G,H)).main ~
  PKSi.EF_CMA.EF_CMA(EF_CMA.WrapEF(PSS''(G,H)),Adv(G,H)).main:
  ={glob Adv} ==> ={res}.
proof.
fun;
call (_: ={EF_CMA.WrapEF.qs, m} ==> ={res});
  first by fun; wp.
call (_: ={glob H, glob G, EF_CMA.WrapEF.pk, m, s} ==> ={res});
  first by fun; call (_: ={glob H, glob G, EF_CMA.WrapEF.pk, pk, m, s} ==> ={res})=> //;
             fun; eqobs_in; (call (correct_G _); first by apply gtagL); wp.
call (_: ={glob H, glob G, glob EF_CMA.WrapEF}).
  fun; call (_: ={glob H, glob G, EF_CMA.WrapEF.sk, sk, m} ==> ={glob H, glob G, EF_CMA.WrapEF.sk, res});
    last by wp.
    fun; eqobs_in; (call (correct_G _); first by apply gtagL); wp;
    call (_: ={glob H, x} ==> ={glob H, res});
      first by fun (true).
    by rnd.
  by fun (={glob G, glob EF_CMA.WrapEF}).
  by fun (={glob H, glob EF_CMA.WrapEF}).
call (_: true ==> ={glob H, glob G, glob EF_CMA.WrapEF, res})=> //;
  by fun; eqobs_in.
qed.

(** Back to the real proof *)
(* A CMA adversary with access to two random oracles *)
module type PartialOracles(G:Gt.Oracle,H:Ht.Oracle) = {
  fun init(): pkey
  fun sign(m:message): signature
  fun fresh(m:message): bool
}.

local module G0o(G:Gt.Oracle,H:Ht.Oracle): PartialOracles(G H) = {
  var pk:pkey
  var sk:skey

  var qs:message set

  fun init(): pkey = {
    G.init();
    H.init();
    qs = empty;
    (pk,sk) = $keypairs;
    return pk;
  }

  fun sign(m:message): signature = {
    var r:salt;
    var g:gtag;
    var rMask:salt;
    var maskedR:salt;
    var w:htag;
    var gamma:g2tag;
    var y:signature;

    qs = add m qs;
    r = $sample_salt;
    w  = H.o(m || (to_bits r));
    g = G.o(w);
    rMask  = Salt.from_bits (sub (to_bits g) 0 k0);
    maskedR = rMask ^ r;
    gamma  = G2Tag.from_bits (sub (to_bits g) k0 kg2);
    y = Signature.from_bits (zeros 1 || (to_bits w) || (to_bits maskedR) || (to_bits gamma));
    return finv sk y;
  } 

  fun fresh(m:message): bool = {
    return !mem m qs;
  }
}.

local module G0(G:Gt.Oracle,H:Ht.Oracle,O:PartialOracles,A:CMA_2RO) = {
  module O = O(G,H)
  module A = A(G,H,O)

  fun main(): bool = {
    var pk:pkey;
    var m:message;
    var s:signature;
    var y:signature;
    var w:htag;
    var w':htag;
    var g:gtag;
    var maskedR:salt;
    var gamma:g2tag;
    var gamma':g2tag;
    var rMask:salt;
    var r:salt;
    var forged, fresh:bool;

    pk = O.init();
    (m,s) = A.forge(pk);

    y = (f pk s);
    forged = (sub (to_bits y) 0 1 <> zeros 1);
    w = HTag.from_bits (sub (to_bits y) 1 k1);
    maskedR = Salt.from_bits (sub (to_bits y) (k1 + 1) k0);
    gamma = G2Tag.from_bits (sub (to_bits y) (k1 + k0 + 1) kg2);
    g = G.o(w);
    rMask  = Salt.from_bits (sub (to_bits g) 0 k0);
    r = rMask ^ maskedR;
    w'  = H.o(m || to_bits r);
    gamma'  = G2Tag.from_bits (sub (to_bits g) k0 kg2);
    forged =  w = w' /\ gamma = gamma' /\ !forged;

    fresh = O.fresh(m);
    return forged /\ fresh;
  }
}.

local module PSSi = PSS(G,H).
local module PSSo = EF_CMA.WrapEF(PSSi).

local lemma PSS''_G0_fresh:
  equiv [EF_CMA.WrapEF(PSS''(G,H)).fresh ~ G0o(G,H).fresh: ={m} /\ PSSo.qs{1} = G0o.qs{2} ==> ={res}]
by by fun.

(*local lemma PSS_G0_verify:
  equiv [PSSo.verify ~ G0o'.verify: ={m,s,glob G,glob H} /\ PSSo.pk{1} = G0o'.pk{2} ==> ={res}].
proof.
fun; inline PSS(G,H).verify;
seq 12 9: (={w,w',gamma,gamma'} /\ b0{1} = b{2}); last by wp.
eqobs_in.
qed.*)

local lemma PSS''_G0_sign:
  equiv [EF_CMA.WrapEF(PSS''(G,H)).sign ~ G0o(G,H).sign:
    ={m,glob G, glob H} /\ EF_CMA.WrapEF.qs{1} = G0o.qs{2} /\ EF_CMA.WrapEF.sk{1} = G0o.sk{2} ==>
    ={glob G,glob H, res} /\ EF_CMA.WrapEF.qs{1} = G0o.qs{2} /\ EF_CMA.WrapEF.sk{1} = G0o.sk{2}].
proof.
fun; inline PSS''(G,H).sign CorrectG.call1.
seq 12 8: (={glob G, glob H, y} /\
           EF_CMA.WrapEF.qs{1} = G0o.qs{2} /\
           EF_CMA.WrapEF.sk{1} = G0o.sk{2} /\
           sk{1} = G0o.sk{2}).
  by eqobs_in.
  by wp.
qed.

local module PSSo'' = EF_CMA.WrapEF(PSS''(G,H)).

local equiv PSS''_G0_init: PSSo''.init ~ G0o(G,H).init:
  true ==>
  ={glob G, glob H, res} /\
  PSSo''.qs{1} = G0o.qs{2} /\
  PSSo''.pk{1} = G0o.pk{2} /\
  PSSo''.sk{1} = G0o.sk{2} /\
  G0o.pk{2} = res{2}.
proof.
fun; inline PSS''(G,H).init PSS''(G,H).keygen PSS(G,H).init.
wp; rnd; wp.
seq 2 2: (={glob G, glob H})=> //.
call (_: true ==> ={glob H})=> //;
  first by fun (true).
call (_: true ==> ={glob G})=> //;
  first by fun (true).
qed.

(** We really *really* **really** want to be able to prove PSS_G0
    in one step, which requires being able to use correct_G to discharge
    an objective of the form:


    pre: x{1} = w{2} /\ x0{1} = w{2}

    g = G.o(x)                       (1)  g = G.o(x)
    g' = G.o(x0)                     (2)

    post: (g,g'){1} = (g,g){2} *)
local equiv PSS''_G0:
  PKSi.EF_CMA.EF_CMA(PSSo'',Adv(G,H)).main ~ G0(G,H,G0o,Adv).main:
    ={glob Adv} ==> ={res}.
proof.
fun;
call PSS''_G0_fresh.
seq 2 2: (={glob G, glob H, m, s} /\
          EF_CMA.WrapEF.qs{1} = G0o.qs{2} /\
          EF_CMA.WrapEF.pk{1} = G0o.pk{2} /\
          G0o.pk{2} = pk{2}).
  call (_: ={glob G, glob H} /\
           EF_CMA.WrapEF.qs{1} = G0o.qs{2} /\
           EF_CMA.WrapEF.pk{1} = G0o.pk{2} /\
           EF_CMA.WrapEF.sk{1} = G0o.sk{2}).
    by conseq* PSS''_G0_sign.
    by conseq* (_: ={glob H, x} ==> ={glob H, res})=> //; fun (true).
    by conseq* (_: ={glob G, x} ==> ={glob G, res})=> //; fun (true).
  by call PSS''_G0_init.
inline EF_CMA.WrapEF(PSS''(G,H)).verify PSS''(G,H).verify CorrectG.call1.
conseq * (_: ={glob H, glob G, m, s} /\ EF_CMA.WrapEF.pk{1} = G0o.pk{2} /\ G0o.pk{2} = pk{2} ==>
             ={glob H, glob G, forged} /\ EF_CMA.WrapEF.pk{1} = G0o.pk{2})=> //.
wp.
call (_: ={glob H, x} ==> ={glob H, res});
  first by fun (true).
wp.
call (_: ={glob G, x} ==> ={glob G, res});
  first by fun (true).
by wp; skip.
qed.

(** First real proof step *)
local module G2o(G:Gt.Oracle,H:Ht.Oracle): PartialOracles(G H) = {
  var pk:pkey
  var sk:skey

  var qs:message set

  fun init(): pkey = {
    G.init();
    H.init();
    qs = empty;
    (pk,sk) = $keypairs;
    return pk;
  }

  fun sign(m:message): signature = {
    var r:salt;
    var g:gtag;
    var rMask:salt;
    var maskedR:salt;
    var w:htag;
    var gamma:g2tag;
    var y:signature;

    qs = add m qs;
    r = $sample_salt;
    w  = H.o(m || (to_bits r));
    g = G.o(w);
    rMask  = Salt.from_bits (sub (to_bits g) 0 k0);
    maskedR = rMask ^ r;
    gamma  = G2Tag.from_bits (sub (to_bits g) k0 kg2);
    y = Signature.from_bits (zeros 1 || (to_bits w) || (to_bits maskedR) || (to_bits gamma));
    return finv sk y;
  } 

  fun fresh(m:message): bool = {
    return !mem m qs;
  }
}.

local module G2(G:Gt.Oracle,H:Ht.Oracle,O:PartialOracles,A:CMA_2RO) = {
  module O = O(G,H)
  module A = A(G,H,O)

  fun main(): bool = {
    var pk:pkey;
    var m:message;
    var s:signature;
    var y:signature;
    var w:htag;
    var w':htag;
    var g:gtag;
    var maskedR:salt;
    var gamma:g2tag;
    var gamma':g2tag;
    var rMask:salt;
    var r:salt;
    var forged, fresh:bool;

    pk = O.init();
    (m,s) = A.forge(pk);

    y = (f pk s);
    forged = (sub (to_bits y) 0 1 <> zeros 1);
    w = HTag.from_bits (sub (to_bits y) 1 k1);
    maskedR = Salt.from_bits (sub (to_bits y) (k1 + 1) k0);
    gamma = G2Tag.from_bits (sub (to_bits y) (k1 + k0 + 1) kg2);
    g = G.o(w);
    rMask  = Salt.from_bits (sub (to_bits g) 0 k0);
    r = rMask ^ maskedR;
    w'  = H.o(m || to_bits r);
    gamma'  = G2Tag.from_bits (sub (to_bits g) k0 kg2);
    forged =  w = w' /\ gamma = gamma' /\ !forged;

    fresh = O.fresh(m);
    return forged /\ fresh;
  }
}.

(* PROOF GOES HERE *)


(* We bound the probability, for all lossless
   adversary A of type CMA_2RO of
   PSS_CMA(A(G',H')).main returning true. *)
declare module I:Inverter.
local lemma local_conclusion &m:
  Pr[PKSi.EF_CMA.EF_CMA(PSSo,Adv(G,H)).main() @ &m: res] <= Pr[RSA.OW(I).main() @ &m: res].
admit.
qed.

lemma conclusion &m: exists (I<:Inverter),
  Pr[PKSi.EF_CMA.EF_CMA(PKSi.EF_CMA.WrapEF(PSS(G,H)),Adv(G,H)).main() @ &m: res] <= Pr[RSA.OW(I).main() @ &m: res].
proof.
exists I; apply (local_conclusion &m).
qed.
end section.