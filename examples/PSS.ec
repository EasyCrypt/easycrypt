require import RandOrcl.
require import Array.
require import Bitstring.
require import Map.
require import Set.
require import Int.
require import Distr.
require import Bool.

theory SignatureScheme.

  type pkey.
  type skey.

  module type SigScheme_ROM = {
    fun init(): unit (* This is unfortunate, but the ROM needs to be initialized *)
    fun h(x:bitstring): bitstring
    fun keygen(): (pkey * skey)
    fun sign(sk:skey, m:bitstring): bitstring
    fun verify(pk:pkey, m:bitstring, s:bitstring): bool
  }.

  op qH:int.
  op qS:int.

  module type SigScheme_Oracles_ROM = {
    fun init(): pkey
    fun wasQueried(m:bitstring): bool
    fun h(x:bitstring): bitstring
    fun sign(m:bitstring): bitstring
    fun verify(pk:pkey, m:bitstring, s:bitstring): bool (* In theory, we don't give this one to the adversary. Check with P-Y for bug in functor application *)
  }.

  module Sig_Oracles_ROM(S:SigScheme_ROM): SigScheme_Oracles_ROM = {
    var qs:bitstring set
    var cH:int
    var cS:int
    var sk:skey

    fun init():pkey = {
      var pk:pkey;
      S.init();
      (pk,sk)  = S.keygen();
      return pk; }

    fun wasQueried(m:bitstring):bool = { return mem m qs; }

    fun h(x:bitstring):bitstring = {
      var r:bitstring = zeros(0);
      if (cH < qH)
      {
        cH = cH + 1;
        r  = S.h(x);
      }
      return r;
    }

    fun sign(m:bitstring):bitstring = {
      var r:bitstring = zeros(0);
      if (cS < qS)
      {
        cS = cS + 1;
        qs = add m qs;
        r  = S.sign(sk,m);
      }
      return r;
    }

    fun verify(pk:pkey, m:bitstring, s:bitstring):bool = {
      var b:bool;
      b  = S.verify(pk,m,s);
      return b;
    }
  }.

  module type SigAdversary_ROM(Sig:SigScheme_Oracles_ROM) = {
    fun a(pk:pkey): (bitstring * bitstring)
  }.

  module EF_CMA(S:SigScheme_ROM, Adv:SigAdversary_ROM) = {
    module O = Sig_Oracles_ROM(S)
    module A = Adv(O)

    fun main(): bool = {
      var pk:pkey;
      var m:bitstring;
      var s:bitstring;
      var forged:bool;
      var queried:bool;
      pk  = O.init();
      (m,s)  = A.a(pk);
      forged  = O.verify(pk,m,s);
      queried  = O.wasQueried(m);
      return forged /\ !queried;
    }
  }.

(* Note: This is not necessarily the standard, this is PSS as presented in Coron 2006 (or something). *)
op k:int.
op k0:int.
op k1:int.

op keypairs: (pkey * skey) distr.
op rsa: pkey -> bitstring -> bitstring.
op rsa': skey -> bitstring -> bitstring.

module PSS:SigScheme_ROM = {
  (* H *)
  var mH:(bitstring,bitstring) map
  fun h(x:bitstring): bitstring = {
    var r:bitstring;
    r = $Dbitstring.dbitstring(k1);
    if (!in_dom x mH) mH = mH.[x <- r];
    return proj mH.[x]; (* Yurk. We need to deal with this *)
  }

  (* G *)
  var mG:(bitstring,bitstring) map
  fun g(x:bitstring):bitstring = {
    var r:bitstring;
    r = $Dbitstring.dbitstring(k - k1 - 1);
    if (!in_dom x mG) mG = mG.[x <- r];
    return proj mG.[x];
  }

  (* init *)
  fun init(): unit = {
    mG = Map.empty;
    mH = Map.empty;
  }

  fun g1(x:bitstring):bitstring = {
    var r:bitstring;
    r  = g(x);
    return sub r 0 k0;
  }

  fun g2(x:bitstring):bitstring = {
    var r:bitstring;
    r  = g(x);
    return sub r k0 (k - k0 - k1 - 1);
  }

  (* Keygen: make it a wrapped pop *)
  fun keygen():(pkey * skey) = {
    var pk, sk:(pkey * skey);
    (pk,sk) = $keypairs;
    return (pk,sk);
  }

  (* Sign *)
  fun sign(sk:skey, m:bitstring):bitstring = {
    var r:bitstring;
    var rMask:bitstring;
    var maskedR:bitstring;
    var w:bitstring;
    var gamma:bitstring;
    var y:bitstring;

    r = $Dbitstring.dbitstring(k0);
    w  = h(m || r);
    rMask  = g1(w);
    maskedR = rMask ^^ r;
    gamma  = g2(w);
    y = zeros(1) || w || maskedR || gamma;
    return (rsa' sk m); (* For fault injection, we will later refine this; we should make it a function so it can be reasoned about separately *)
  }

  (* Verify *)
  fun verify(pk:pkey, m:bitstring, s:bitstring):bool = {
    var y:bitstring;
    var w:bitstring;
    var w':bitstring;
    var maskedR:bitstring;
    var gamma:bitstring;
    var gamma':bitstring;
    var rMask:bitstring;
    var r:bitstring;
    var b:bool;
    y = (rsa pk s);
    b = y.[0];
    w = sub y 1 k1;
    maskedR = sub y (k1 + 1) k0;
    gamma = sub y (k1 + k0 + 1) (k - k1 - k0 - 1);
    rMask  = g1(w);
    r = rMask ^^ maskedR;
    w'  = h(m || r);
    gamma'  = g2(w);
    return (w = w' /\ gamma = gamma' /\ !b);
  }
}.

module PSS_Oracles = Sig_Oracles_ROM(PSS).
