require import PKS.

(* Do the same for 0 and 1 ROM *)

theory EF_CMA.
  clone import PKS.

  module type CMA(O:Oracles) = {
    fun a(pk:pkey): (message * signature)
  }.

  module EF_CMA(S:Scheme, Adv:CMA) = {
    module O = Wrap(S)
    module A = Adv(O)

    fun main(): bool = {
      var pk:pkey;
      var m:message;
      var s:signature;
      var forged:bool;
      var fresh:bool;
      pk = O.init();
      (m,s)   = A.a(pk);
      forged  = S.verify(pk,m,s);
      fresh   = O.fresh(m);
      return forged /\ fresh;
    }
  }.
end EF_CMA.

theory EF_CMA_ROM.
  clone import PKS_ROM as PKS.

  module type CMA(H:PKS.RandOrcl.ARO, O:Oracles) = {
    fun a(pk:pkey): (message * signature)
  }.

  module EF_CMA(H:PKS.RandOrcl.Oracle, S:Scheme, Adv:CMA) = {
    module O = Wrap(H,S)
    module H' = PKS.RandOrcl.WRO_Set.ARO(H)
    module A = Adv(H',O)

    fun main(): bool = {
      var pk:pkey;
      var m:message;
      var s:signature;
      var forged:bool;
      var fresh:bool;
      pk = O.init();
      (m,s)   = A.a(pk);
      forged  = S.verify(pk,m,s);
      fresh   = O.fresh(m);
      return forged /\ fresh;
    }
  }.
end EF_CMA_ROM.

theory EF_CMA_2ROM.
  clone import PKS_2ROM as PKS.

  module type CMA(G:Gt.ARO, H:Ht.ARO, O:Oracles) = {
    fun a(pk:pkey): (message * signature)
  }.

  module EF_CMA(G:Gt.Oracle, H:Ht.Oracle, S:Scheme, Adv:CMA) = {
    module O = Wrap(G,H,S)
    module G' = Gt.WRO_Set.ARO(G)
    module H' = Ht.WRO_Set.ARO(H)
    module A = Adv(G',H',O)

    fun main(): bool = {
      var pk:pkey;
      var m:message;
      var s:signature;
      var forged:bool;
      var fresh:bool;
      pk = O.init();
      (m,s)   = A.a(pk);
      forged  = S.verify(pk,m,s);
      fresh   = O.fresh(m);
      return forged /\ fresh;
    }
  }.
end EF_CMA_2ROM.
