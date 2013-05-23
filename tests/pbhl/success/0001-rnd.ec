

require import RandOrcl.
require import Array.
require import Bitstring.
require import Map.
require import Set.
require import Int.
require import Distr.
require import Bool.


theory EncryptionScheme.

  type pkey.
  type skey.

  module type EncScheme_ROM = {
   fun init(): unit 
   fun h(x:bitstring): bitstring
   fun kg() : (pkey * skey)
   fun enc(pk:skey, m:bitstring): bitstring
   fun dec(sk:pkey, c:bitstring): bitstring
  }.

  op qH : int.
  op qD : int.
  
  module type EncScheme_CPAOracles_ROM = {
   fun h(x:bitstring): bitstring
  }.
  
  module type EncScheme_CCAOracles_ROM = {
   fun h(x:bitstring): bitstring
   fun dec(sk:pkey, c:bitstring): bitstring
  }.

  
  module Enc_Oracles_ROM(S:EncScheme_ROM): EncScheme_CPAOracles_ROM = {
   var lh : bitstring set
   fun h(x : bitstring) : bitstring ={
    var y : bitstring = zeros(0);
    if (card lh < qH) {
     y := S.h(x);
    }
    return y;
   }
  }.

  module type CPAAdversary_ROM(E:EncScheme_CPAOracles_ROM) = {
   fun a1(pk:pkey): (bitstring * bitstring)
   fun a2(c : bitstring): bool
  }.

  module CPA(S:EncScheme_ROM, Adv:CPAAdversary_ROM) = {
   module O = Enc_Oracles_ROM(S)
   module A = Adv(O)
    fun main(): bool = {
    var pk:pkey;
    var sk:skey;
    var m0 : bitstring;
    var m1 : bitstring;
    var c : bitstring;
    var b : bool;
    var b' : bool;
    var s:bitstring;
    (pk,sk) := S.kg();
    (m0,m1) := A.a1(pk);
    b = $Dbool.dbool;
    c := S.enc(sk,b?m0:m1);
    b':= A.a2(c);
    return b = b';
   }
  }.



require Logic.

module M = {
  fun f (w x:int) : int = {
    var y : int;
    var z : int;
    y = 1;
    z = x;
    x = y;
    y = z; 
    return x;
  }
}.




