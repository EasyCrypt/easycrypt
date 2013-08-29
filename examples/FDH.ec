require import Fun.
require import Bool.
require import Int.
require import Real.
require import FSet.
require import ISet.
  import Finite.
require import Map.
require import Pair.

(*** General definitions *)
(** Lengths *)
op k:int.
axiom leq0_k: 0 < k.

op qS:int.
axiom leq0_qS: 0 <= qS.

op qH:int.
axiom leq0_qH: 0 <= qH.

(** Types *)
require AWord.
require import ABitstring.

type message = bitstring.

(* Signatures *)
type signature.
clone import AWord as Signature with
  type word <- signature,
  op length <- k.

(* Domain of RSA *)
op sample_plain: signature distr. (* Whereby we sample only with the first byte/bit set to 0 *)

(** Instantiating *)
require PKS.
require OW.
require RandomOracle.

clone import OW as RSA with
  type t <- signature,
  op sample_t <- sample_plain,
  op f_dom = (lambda (pk:pkey) (x:signature), true),
  op f_rng = (lambda (pk:pkey) (x:signature), true),
  op finv_dom = (lambda (sk:skey) (x:signature), true),
  op finv_rng = (lambda (sk:skey) (x:signature), true)
  proof f_rng_sub_finv_dom by smt,
        finv_rng_sub_f_dom by smt,
        f_dom_sample_t by smt.

clone import RandomOracle as Ht with
  type from <- message,
  type to <- signature,
  op dsample <- Signature.Dword.dword.
  module H = Ht.ROM.RO.

clone import PKS as PKSi with
  type pkey <- pkey,
  type skey <- skey,
  type message <- message,
  type signature <- signature.
  import EF_CMA.

module FDH(H:Oracle): Scheme = {
  fun init(): unit = {
    H.init();
  }

  fun keygen(): pkey * skey = {
    var (pk,sk): pkey * skey;
    (pk,sk) = $keypairs;
    return (pk,sk);
  }

  fun sign(sk:skey, m:message): signature = {
    var h:signature;
    h = H.o(m);
    return finv sk h;
  }

  fun verify(pk:pkey, m:message, s:signature): bool = {
    var h:signature;
    h = H.o(m);
    return h = f pk s;
  }
}.

module type CMA_ROM(H:ARO,O:AdvOracles) = {
  fun forge(pk:pkey): message * signature
}.

module type FDHOracles = {
  fun init(): pkey {*}
  fun sign(m:message): signature
  fun fresh(m:message): bool
}.

(** Partially Inlined Oracles for G0 and G1 **)
module FDH_O(H:Oracle): FDHOracles = {
  var pk:pkey
  var sk:skey
  var qs:message FSet.set

  fun init(): pkey = {
    H.init();
    qs = FSet.empty;
    (pk,sk) = $keypairs;
    return pk;
  }

  fun sign(m:message): signature = {
    var h:signature;
    qs = add m qs;
    h = H.o(m);
    return finv sk h;
  }

  fun fresh(m:message): bool = {
    return !mem m qs;
  }
}.

(** G0: Inlining the verification algorithm *)
module G0(Adv:AdvCMA) = {
  module O = FDH_O(H)
  module A = Adv(O)

  fun main(): bool = {
    var pk:pkey;
    var m:message;
    var s, h:signature;
    var fresh:bool;

    pk = O.init();
    (m,s) = A.forge(pk);
    h = H.o(m);
    fresh = O.fresh(m);
    return h = f pk s /\ fresh;
  }
}.

equiv FDH_G0_equiv (A <: CMA_ROM {H, Number, Wrap, FDH_O}):
  EF_CMA(Wrap(FDH(H)),A(H)).main ~ G0(A(Number(H))).main:
    ={glob A} ==> ={res}.
proof strict.
fun.
call (_: ={m} /\
         Wrap.qs{1} = FDH_O.qs{2} ==>
         ={res});
  first by fun; wp.
inline Wrap(FDH(ROM.RO)).verify FDH(ROM.RO).verify; wp.
call (_: ={glob H});
  first by eqobs_in.
wp.
call (_: ={glob H} /\
         Wrap.pk{1} = FDH_O.pk{2} /\
         Wrap.sk{1} = FDH_O.sk{2} /\
         Wrap.qs{1} = FDH_O.qs{2}).
  fun; inline FDH(ROM.RO).sign; wp;
       call (_: ={glob H}); first by eqobs_in.
       by wp.
  fun*; inline Number(ROM.RO).o; wp;
        call (_: ={glob H}); first by eqobs_in.
        by wp.
call (_: true ==>
         ={res, glob H} /\
         Wrap.pk{1} = res{1} /\
         Wrap.pk{1} = FDH_O.pk{2} /\
         Wrap.sk{1} = FDH_O.sk{2} /\
         Wrap.qs{1} = FDH_O.qs{2})=> //.
fun; inline FDH(ROM.RO).keygen FDH(ROM.RO).init;
     wp; rnd; wp;
     call (_: true ==> ={glob H})=> //;
       first by fun; eqobs_in.
qed.

(** G1: Indexing the random oracle and setting things up *)
module G1(Adv:AdvCMA) = {
  module O = FDH_O(Number(H))
  module A = Adv(O)

  var m:message
  var t:(int,bool) map

  fun main(): bool = {
    var pk:pkey;
    var s,h:signature;
    var forged:bool;
    var i:int;

    pk = O.init();
    i = 0;
    (m,s) = A.forge(pk);
    h = H.o(m);
    forged = (h = f pk s);
    while (i < qH)
    {
      t.[i] = ${0,1};
      i = i + 1;
    }
    return forged;
  }
}.

lemma G0_G1_equiv (A <: CMA_ROM {H, Number, FDH_O}):
  equiv [G0(A(H)).main ~ G1(A(Number(H))).main:
           ={glob A} ==>
           res{1} = (res /\ !mem G1.m FDH_O.qs){2}].
proof strict.
fun.
seq 3 4: (={pk, h, s, glob H, glob FDH_O} /\
          m{1} = G1.m{2} /\
          i{2} <= qH); first last.
  while{2} true (qH - i{2});
    first progress=> //; wp; rnd; first by apply Dbool.lossless.
          by skip; smt.
  inline G0(A(ROM.RO)).O.fresh; wp; skip; smt.
call (_: ={glob H}); first by eqobs_in.
call (_: ={glob H, glob FDH_O}).
  fun; inline Number(ROM.RO).o; wp;
       call (_: ={glob H}); first by eqobs_in.
       by wp.
  fun*; inline Number(ROM.RO).o; wp;
        call (_: ={glob H}); first by eqobs_in.
        by wp.
wp.
call (_: true ==>
         ={glob H, glob FDH_O, res}).
  fun; inline Number(ROM.RO).init; eqobs_in.
skip; progress=> //; smt.
qed.
