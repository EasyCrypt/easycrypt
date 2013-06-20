require import Int.
require import Map.

type from.
type to.

op dsample : to distr. (* Distribution to use on the target type *)
op qO : int.           (* Maximum number of calls by the adversary *)
op default : to.       (* Default element to return on error by wrapper *)

(* A signature for random oracles from "from" to "to". *)
module type Oracle =
{
  fun init():unit
  fun o(x:from):to
}.

module type ARO = { fun o(x:from):to }.

theory ROM.
  (* Bare random oracle for use in schemes *)
  module RO:Oracle = {
    var m : (from, to) map

    fun init() : unit = {
      m = empty;
    }
  
    fun o(x:from) : to = {
      var y : to;
      y = $dsample;
      if (!in_dom x m) m.[x] = y;
      return proj (m.[x]);
    }
  }.
end ROM.

(* Wrappers for use by an adversary:
     - counting requests,
     - tracking the set of requests,
     - tracking the sequence of requests *)
theory WRO_Int.
  module ARO(R:Oracle):Oracle = {
    var log:int

    fun init():unit = {
      R.init();
      log = 0;
    }

    fun o(x:from): to = {
      var r:to;
      if (log < qO)
      {
        log = log + 1;
        r = R.o(x);
      }
      else
        r = default;
      return r;
    }
  }.
end WRO_Int.

theory WRO_Set.
  require import Set.
  module ARO(R:Oracle):Oracle = {
    var log:from set

    fun init():unit = {
      R.init();
      log = Set.empty;
    }

    fun o(x:from): to = {
      var r:to;
      if (card log < qO)
      {
        log = add x log;
        r = R.o(x);
      }
      else
        r = default;
      return r;
    }
  }.
end WRO_Set.

theory WRO_List.
  require import NewList.
  module ARO(R:Oracle):Oracle = {
    var log:from list

    fun init():unit = {
      R.init();
      log = [];
    }

    fun o(x:from): to = {
      var r:to;
      if (length log < qO)
      {
        log = x :: log;
        r = R.o(x);
      }
      else
        r = default;
      return r;
    }
  }.
end WRO_List.

theory IND_RO.
  module type ARO = { fun o(x:from): to }.
  module type RO_adv(X:ARO) = { fun a(): bool }.

  module IND_RO(R:Oracle,A:RO_adv) = {
    module Adv = A(R)

    fun main(): bool = {
      var b:bool;
      R.init();
      b = Adv.a();
      return b;
    }
  }.
end IND_RO.