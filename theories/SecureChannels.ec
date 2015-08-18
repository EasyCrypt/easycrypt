(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2015 - IMDEA Software Institute
 * Copyright (c) - 2012--2015 - Inria
 * 
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

require import Bool.
require import Int.
require import Option.
require import FSet.

type key.
type message.
type container.

module type Scheme = {
  proc init(): unit
  proc kg(): key
  proc send(k:key,m:message): container
  proc recv(k:key,c:container): message option
}.

theory MultiUser.
  require import Array.

  const users:int.
  axiom users_pos: 0 < users.

  module type Oracles = {
    proc send(i:int,m0:message,m1:message): container option
    proc recv(i:int,c:container): message option
  }.

  module Wrap(S:Scheme) = {
    var qs:message set
    var ks:key array
    var b:bool
    var auth:bool

    proc initKeys(): unit = {
      var i:int;

      i = 0;
      while (i < users)
      {
        ks.[i] = S.kg();
        i = i + 1;
      }
    }

    proc init(): unit = {
      qs = FSet.empty;
      auth = false;
      S.init();
      b = ${0,1};
      initKeys();
    }

    proc send(i:int,m0:message,m1:message): container option = {
      var r:container option;
      var c:container;

      if (0 <= i < users)
      {
        qs = add m0 (add m1 qs);
        c = S.send(ks.[i],b ? m1 : m0);
        r = Some c;
      }
      else
        r = None;

      return r;      
    }

    proc recv(i:int,c:container): message option = {
      var r:message option;

      if (0 <= i < users)
      {
        r = S.recv(ks.[i],c);
        if (r <> None /\ !mem (oget r) qs)
          auth = true;
      }
      else
        r = None;
      return r;
    }

    proc guess(b':bool): bool = {
      return b' = b;
    }

    proc auth(): bool = {
      return auth;
    }
  }.

  module type Adv_LOR(O:Oracles) = {
    proc guess(): bool
  }.

  module LOR(S:Scheme,A:Adv_LOR) = {
    module O = Wrap(S)
    module A = A(O)

    proc main(): bool = {
      var b',sec,auth:bool;

      O.init();
      b' = A.guess();
      sec = O.guess(b');
      auth = O.auth();
      return sec \/ auth;
    }
  }.
end MultiUser.

(* Reduce multi-user to single-user *)