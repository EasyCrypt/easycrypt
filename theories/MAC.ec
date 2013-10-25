require import FSet.

type key.
type message.
type tag.

module type Scheme = {
  fun init(): unit {*}
  fun keygen(): key
  fun mac(k:key,m:message): tag
  fun verify(k:key,m:message,t:tag): bool
}.

module type Oracles = {
  fun mac(m:message): tag
  fun verify(m:message,t:tag): bool
}.

module Wrap(S:Scheme) = {
  var qs:message set
  var k:key

  fun init(): unit = {
    qs = empty;
    S.init();
    k = S.keygen();
  }

  fun mac(m:message): tag = {
    var r:tag;

    qs = add m qs;
    r = S.mac(k,m);
    return r;
  }

  fun verify(m:message,t:tag): bool = {
    var r:bool;

    r = S.verify(k,m,t);
    return r;
  }

  fun fresh(m:message): bool = {
    return (!mem m qs);
  }
}.

module type Adv_CMA(O:Oracles) = {
  fun forge(): (message * tag)
}.

module CMA(S:Scheme,A:Adv_CMA) = {
  module O = Wrap(S)
  module A = A(O)

  fun main(): bool = {
    var m:message;
    var t:tag;
    var forged,fresh:bool;

    O.init();
    (m,t) = A.forge();
    forged = O.verify(m,t);
    fresh = O.fresh(m);
    return forged /\ fresh;
  }
}.