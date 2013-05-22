require import Int.
require import Bitstring.
require import Set.

(* A library of definitions for EF-CMA signatures schemes based on the ROM. *)
(* Some further things could be parameterized.                              *)
(* The Scheme game is not specific to existential forgeries,                *)
(* although the others are.                                                 *)

(** Parameters *)
type pkey.
type skey.
op keygen: (pkey * skey) distr.

(** Module Types *)
(* A ROM-based signature scheme provides the following oracles *)
module type Scheme_ROM = {
  fun init(): unit
  fun h(x:bitstring): bitstring
  fun keygen(): (pkey * skey)
  fun sign(sk:skey, m:bitstring): bitstring
  fun verify(pk:pkey, m:bitstring, s:bitstring): bool
}.

module type EF_Oracles_ROM = {
  fun init(): pkey
  fun wasQueried(m:bitstring): bool
  fun h(x:bitstring): bitstring
  fun sign(m:bitstring): bitstring
}.

op qH:int.
op qS:int.

module EF_Wrap_ROM(S:Scheme_ROM):EF_Oracles_ROM = {
  var qs:bitstring set
  var cH:int
  var cS:int
  var sk:skey

  fun init():pkey = {
    var pk:pkey;
    S.init();
    (pk,sk) := S.keygen();
    return pk;
  }

  fun wasQueried(m:bitstring):bool = { return mem m qs; }

  fun h(x:bitstring):bitstring = {
    var r:bitstring = zeros(0);
    if (cH < qH)
    {
      cH = cH + 1;
      r := S.h(x);
    }
    return r;
  }

  fun sign(m:bitstring):bitstring = {
    var r:bitstring = zeros(0);
    if (cS < qS)
    {
      cS = cS + 1;
      qs = add m qs;
      r := S.sign(sk,m);
    }
    return r;
  }
}.

module type Adversary_ROM(Sig:EF_Oracles_ROM) = {
  fun a(pk:pkey): (bitstring * bitstring)
}.

module EF_CMA(S:Scheme_ROM, Adv:Adversary_ROM) = {
  module O = EF_Wrap_ROM(S)
  module A = Adv(O)

  fun main(): bool = {
    var pk:pkey;
    var m:bitstring;
    var s:bitstring;
    var forged:bool;
    var queried:bool;
    pk := O.init();
    (m,s) := A.a(pk);
    forged := S.verify(pk,m,s);
    queried := O.wasQueried(m);
    return forged /\ !queried;
  }
}.
