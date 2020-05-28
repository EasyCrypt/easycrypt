(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

require import FSet.

type key.
type message.
type tag.

module type Scheme = {
  proc * init(): unit {}
  proc keygen(): key
  proc mac(k:key,m:message): tag
  proc verify(k:key,m:message,t:tag): bool
}.

module type Oracles = {
  proc mac(m:message): tag
  proc verify(m:message,t:tag): bool
}.

module Wrap(S:Scheme) = {
  var qs:message fset
  var k:key

  proc init(): unit = {
    qs <- fset0;
    S.init();
    k  <@ S.keygen();
  }

  proc mac(m:message): tag = {
    var r:tag;

    qs <- qs `|` fset1 m;
    r  <@ S.mac(k,m);
    return r;
  }

  proc verify(m:message,t:tag): bool = {
    var r:bool;

    r <@ S.verify(k,m,t);
    return r;
  }

  proc fresh(m:message): bool = {
    return (!mem qs m);
  }
}.

module type Adv_CMA(O:Oracles) = {
  proc forge(): (message * tag)
}.

module CMA(S:Scheme,A:Adv_CMA) = {
  module O = Wrap(S)
  module A = A(O)

  proc main(): bool = {
    var m:message;
    var t:tag;
    var forged,fresh:bool;

    O.init();
    (m,t)  <@ A.forge();
    forged <@ O.verify(m,t);
    fresh  <@ O.fresh(m);
    return forged /\ fresh;
  }
}.
