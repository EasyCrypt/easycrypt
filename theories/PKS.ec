(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2015 - IMDEA Software Institute
 * Copyright (c) - 2012--2015 - Inria
 * 
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* Definitions for Public-Key Signatures Schemes *)
require import FSet.
require import Pair.

type pkey.
type skey.
type message.
type signature.

module type Scheme = {
  proc * init(): unit {}
  proc keygen(): (pkey * skey)
  proc sign(sk:skey, m:message): signature
  proc verify(pk:pkey, m:message, s:signature): bool
}.

module type AdvOracles = { proc sign(m:message): signature }.

module type AdvCMA(O:AdvOracles) = {
  proc forge(pk:pkey): (message * signature)
}.

theory EF_CMA.
  module type Oracles = {
    proc * init(): pkey {}
    proc sign(m:message): signature
    proc verify(m:message,s:signature): bool
    proc fresh(m:message): bool
    proc queries(): int
  }.

  (* A wrapper providing oracles for existential
     unforgeability from a PKS scheme. *)
  module Wrap(S:Scheme): Oracles = {
    var qs: message set
    var pk: pkey
    var sk: skey

    proc init(): pkey = {
      S.init();
      qs = empty;
      (pk,sk) = S.keygen();
      return pk;
    }

    proc sign(m:message): signature = {
      var s:signature;
      qs = add m qs;
      s = S.sign(sk,m);
      return s;
    }

    proc verify(m:message,s:signature): bool = {
      var b:bool;
      b = S.verify(pk,m,s);
      return b;
    }

    proc fresh(m:message): bool = {
      return !mem m qs;
    }

    proc queries(): int = {
      return card qs;
    }
  }.

  module EF_CMA(O:Oracles, A:AdvCMA) = {
    module A = A(O)

    proc main(): bool = {
      var pk:pkey;
      var m:message;
      var s:signature;
      var forged, fresh:bool;

      pk = O.init();
      (m,s) = A.forge(pk);
      forged = O.verify(m,s);
      fresh = O.fresh(m);
      return forged /\ fresh;
    }
  }.
end EF_CMA.

theory NM_CMA.
  module type Oracles = {
    proc * init(): pkey {}
    proc sign(m:message): signature
    proc verify(m:message,s:signature): bool
    proc fresh(m:message,s:signature): bool
    proc queries(): int
  }.

  (* A wrapper providing oracles for
     non-malleability from a PKS scheme. *)
  module Wrap(S:Scheme): Oracles = {
    var qs: (message * signature) set
    var pk: pkey
    var sk: skey

    proc init(): pkey = {
      S.init();
      qs = empty;
      (pk,sk) = S.keygen();
      return pk;
    }

    proc sign(m:message): signature = {
      var s:signature;
      s = S.sign(sk,m);
      qs = add (m,s) qs;
      return s;
    }

    proc verify(m:message,s:signature): bool = {
      var b:bool;
      b = S.verify(pk,m,s);
      return b;
    }

    proc fresh(m:message,s:signature): bool = {
      return !mem (m,s) qs;
    }

    proc queries(): int = {
      return card qs;
    }
  }.

  module NM_CMA(O:Oracles, A:AdvCMA) = {
    module A = A(O)

    proc main(): bool = {
      var pk:pkey;
      var m:message;
      var s:signature;
      var forged, fresh:bool;

      pk = O.init();
      (m,s) = A.forge(pk);
      forged = O.verify(m,s);
      fresh = O.fresh(m,s);
      return forged /\ fresh;
    }
  }.
end NM_CMA.
