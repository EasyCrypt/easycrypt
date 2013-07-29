(* Definitions for Public-Key Signatures Schemes *)
require import FSet.

theory PKS.
  type pkey.
  type skey.
  type message.
  type signature.

  module type Scheme = {
    fun keygen(): (pkey * skey)
    fun sign(sk:skey, m:message): signature
    fun verify(pk:pkey, m:message, s:signature): bool
  }.

  module type Oracles = { fun sign(m:message): signature }.

  module Wrap(S:Scheme): Oracles = {
    var qs: message set
    var pk: pkey
    var sk: skey

    fun init(): pkey = {
      qs = empty;
      (pk,sk) = S.keygen();
      return pk;
    }

    fun sign(m:message): signature = {
      var s:signature;
      qs = add m qs;
      s = S.sign(sk,m);
      return s;
    }

    fun fresh(m:message): bool = {
      return !mem m qs;
    }
  }.
end PKS.

theory PKS_ROM.
  type pkey.
  type skey.
  type message.
  type signature.

  require        RandOrcl.
    clone import RandOrcl.

  module type Scheme = {
    fun keygen(): (pkey * skey)
    fun sign(sk:skey, m:message): signature
    fun verify(pk:pkey, m:message, s:signature): bool
  }.

  module type Oracles = {
    fun sign(m:message): signature
  }.

  module Wrap(H:Oracle,S:Scheme): Oracles = {
    var qs: message set
    var pk: pkey
    var sk: skey

    fun init(): pkey = {
      H.init();
      qs = empty;
      (pk,sk) = S.keygen();
      return pk;
    }

    fun sign(m:message): signature = {
      var s:signature;
      qs = add m qs;
      s = S.sign(sk,m);
      return s;
    }

    fun fresh(m:message): bool = {
      return !mem m qs;
    }
  }.
end PKS_ROM.

theory PKS_2ROM.
  type pkey.
  type skey.
  type message.
  type signature.

  require        RandOrcl.
    clone RandOrcl as Gt.
    clone RandOrcl as Ht.

  module type Scheme = {
    fun keygen(): (pkey * skey)
    fun sign(sk:skey, m:message): signature
    fun verify(pk:pkey, m:message, s:signature): bool
  }.

  module type Oracles = {
    fun sign(m:message): signature
  }.

  module Wrap(G:Gt.Oracle,H:Ht.Oracle,S:Scheme): Oracles = {
    var qs: message set
    var pk: pkey
    var sk: skey

    fun init(): pkey = {
      H.init();
      G.init();
      qs = empty;
      (pk,sk) = S.keygen();
      return pk;
    }

    fun sign(m:message): signature = {
      var s:signature;
      qs = add m qs;
      s = S.sign(sk,m);
      return s;
    }

    fun fresh(m:message): bool = {
      return !mem m qs;
    }
  }.
end PKS_2ROM.