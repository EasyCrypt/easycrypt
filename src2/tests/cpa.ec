theory RO.
  type from.
  type to.
  pop sample : () -> to.

  cnst qHA : int.

  module type ROA = {
    var lA : form list
    fun HA (x:from) : to 
  }

  module type RO = { 
    var m : (from,to) map
      
    fun H(x:from) : to 
    var lA : from list
    fun HA(x:from) : to
    fun init () : unit 
  }

  module RO = {
    var m : (from,to) map
      
    fun H(x:from) : to = {
      var r : to = sample();
      if (!in_dom(x,m)) m[x] = r;
      return m[x]
    }

    var lA : from list
    fun HA(x:from) : to = {
      var r : to;
      if (length(lA < qHA)) {
        r = H(x);
        lA = x::lA;
      }
      return r
    }
    fun init () : unit = {
      m = empty_map;
      lA = empty_map;
    }
  }
      
end.  

theory PKE_ROM.  
  type pkey.
  type skey.
  type message.
  type cipher.

  module type ePKE(O:RO.RO) = {
    fun KG() : pkey * skey     (* { O.m, O.lA, O.H, O.HA } *)
    fun Enc(pk:pkey, m:message) : cipher (* {  O.m, O.lA, O.H, O.HA } *)
  }.

(*  module type PKE(O:RO.RO) = {
    extend ePKE
    fun Dec(sk:spkey, c:cipher) : message option { O.H }
  }  *)
  
end.
    

theory CPA_ROM1.
  use import PKE_ROM.
  use RO.
 
  module type IAdv (O:RO.ROA) = {
    fun A1 (pk:pkey) : message * message {O.HA}
    fun A2 (pk:pkey, c:cipher) : bool {O.HA}
  }.

  declare module PKE:ePKE.
  declare module Adv:IAdv.

  module CPA = {
    use RO.RO
    module PKE = PKE(RO.RO)
    module A = Adv(RO.RO)
    fun Main() : bool = {
      var m0,m1, mb :message;
      var c : cipher;
      var b, b' : bool;
      var pk:pkey;
      var sk:skey;
      RO.init();
      (pk,sk) = PKE.KG();
      (m0,m1) = A.A1(pk);
      b = {0,1};
      mb = if b then m1 else m0;
      c = PKE.Enc(pk, mb);
      b' = A.A2(pk,c)
      return b = b';
    }
  }.

  module CPA'(PKE:ePKE, Adv:IAdv) = {
    use RO.RO
    module PKE = PKE(RO.RO)
    module A = Adv(RO.RO)
    fun Main() : bool = {
      var m0,m1, mb :message;
      var c : cipher;
      var b, b' : bool;
      var pk:pkey;
      var sk:skey;
      RO.init();
      (pk,sk) = PKE.KG();
      (m0,m1) = A.A1(pk);
      b = {0,1};
      mb = if b then m1 else m0;
      c = PKE.Enc(pk, mb);
      b' = A.A2(pk,c)
      return b = b';
    }
  }.

  cnst AdvCpa = | CPA.Main[res] - 1%r/2%r|. 

end.

print CPA_ROM1.CPA.
print CPA_ROM1.AdvCpa.


 

    


    