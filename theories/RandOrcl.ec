require import Int.
require import Map.
require import Distr.

type from.
type to.

op dsample : to distr. (* Distribution to use on the target type *)
op qO : int.           (* Maximum number of calls by the adversary *)
axiom leq0_qO: 0 <= qO.
op default : to.       (* Default element to return on error by wrapper *)

(* A signature for random oracles from "from" to "to". *)
module type Oracle =
{
  fun init():unit {*}
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

  lemma lossless_init : islossless RO.init.
  proof strict.
  by fun; wp; skip.
  qed.

  lemma lossless_o:
    mu dsample cpTrue = 1%r => islossless RO.o.
  proof strict.
  by intros=> Hd; fun; wp; rnd.
  qed.
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

  lemma lossless_init (R <: Oracle):
    islossless R.init =>
    islossless ARO(R).init.
  proof strict.
  by intros=> HR; fun; wp; call HR; skip.
  qed.

  lemma lossless_o (R <: Oracle):
    islossless R.o =>
    islossless ARO(R).o.
  proof strict.
  by intros=> HR; fun; wp; if; [call HR | ]; wp; skip.
  save.

  lemma RO_lossless_init: islossless ARO(ROM.RO).init.
  proof strict.
  by apply (lossless_init ROM.RO); apply ROM.lossless_init.
  qed.

  lemma RO_lossless_o:
    mu dsample cpTrue = 1%r =>
    islossless ARO(ROM.RO).o.
  proof strict.
  intros=> Hs; apply (lossless_o ROM.RO); apply ROM.lossless_o; apply Hs.
  qed.

  lemma log_stable x (RO <: Oracle{ARO}):
    islossless RO.o =>
    bd_hoare[ ARO(RO).o : x = ARO.log ==> x <= ARO.log] = 1%r.
  proof strict.
  intros=> Ho; fun; if; [call Ho | ];
     wp; skip=> //; progress; smt.
  qed.

  lemma RO_log_stable x:
     mu dsample cpTrue = 1%r => 
     bd_hoare[ ARO(ROM.RO).o: x = ARO.log ==> x <= ARO.log ] = 1%r.
  proof strict.
  by intros=> Hs; apply (log_stable x ROM.RO); apply ROM.lossless_o.
  qed.
end WRO_Int.

theory WRO_Set.
  require import FSet.
  module ARO(R:Oracle):Oracle = {
    var log:from set

    fun init():unit = {
      R.init();
      log = FSet.empty;
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

  lemma lossless_init (R <: Oracle):
    islossless R.init =>
    islossless ARO(R).init.
  proof strict.
  by intros=> HR; fun; wp; call HR; skip.
  qed.

  lemma lossless_o (R <: Oracle):
    islossless R.o =>
    islossless ARO(R).o.
  proof strict.
  by intros=> HR; fun; wp; if; [call HR | ]; wp; skip.
  qed.

  lemma RO_lossless_init: islossless ARO(ROM.RO).init.
  proof strict.
  by apply (lossless_init ROM.RO); apply ROM.lossless_init.
  qed.

  lemma RO_lossless_o:
    mu dsample cpTrue = 1%r =>
    islossless ARO(ROM.RO).o.
  proof strict.
  by intros=> Hs; apply (lossless_o ROM.RO); apply ROM.lossless_o; apply Hs.
  qed.

  lemma log_stable r (RO<:Oracle{ARO}):
    islossless RO.o =>
    bd_hoare[ ARO(RO).o : mem r ARO.log ==> mem r ARO.log ] = 1%r.
  proof strict.
  by intros=> Ho; fun; if; [call Ho | ];
     wp; skip=> //; progress; rewrite mem_add; left.
  qed.

  lemma RO_log_stable r:
     mu dsample cpTrue = 1%r => 
     bd_hoare[ ARO(ROM.RO).o: mem r ARO.log ==> mem r ARO.log ] = 1%r.
  proof strict.
  by intros=> Hs; apply (log_stable r ROM.RO); apply ROM.lossless_o.
  qed.

  lemma RO_upto_o r:
    equiv [ARO(ROM.RO).o ~ ARO(ROM.RO).o : 
      !mem r ARO.log{2} /\
      ={x, ARO.log} /\
      eq_except ROM.RO.m{1} ROM.RO.m{2} r ==>
      !mem r ARO.log{2} =>
        ={res, ARO.log} /\ eq_except ROM.RO.m{1} ROM.RO.m{2} r].
  proof strict.
  fun; if.
    by intros=> &1 &2 [r_nin_log] [[x_eq log_eq]] m_eq_exc;
       rewrite (fcongr card ARO.log{1} ARO.log{2}) //.
    by inline ROM.RO.o; wp; rnd; wp; skip; progress=> //; smt.
    by wp; skip; progress.
  qed.
end WRO_Set.

theory WRO_List.
  require import List.

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

  lemma lossless_init: forall (R <: Oracle),
    islossless R.init =>
    islossless ARO(R).init.
  proof strict.
  by intros=> R HR; fun; wp; call HR; skip.
  qed.

  lemma lossless_o: forall (R <: Oracle),
    islossless R.o =>
    islossless ARO(R).o.
  proof strict.
  by intros=> R HR; fun; wp; (if; first call HR); wp; skip.
  qed.

  lemma RO_lossless_init: islossless ARO(ROM.RO).init.
  proof strict.
  by apply (lossless_init ROM.RO); apply ROM.lossless_init.
  qed.

  lemma RO_lossless_o:
    mu dsample cpTrue = 1%r =>
    islossless ARO(ROM.RO).o.
  proof strict.
  by intros=> Hs; apply (lossless_o ROM.RO); apply ROM.lossless_o; apply Hs.
  qed.

  lemma log_stable: forall r (RO<:Oracle{ARO}), 
    islossless RO.o =>
    bd_hoare[ ARO(RO).o : mem r ARO.log ==> mem r ARO.log ] = 1%r.
  proof strict.
  intros=> r RO Ho; fun; if.
    by call Ho; wp; skip=> //; progress; rewrite mem_cons; right.
    by wp; skip=> //; progress.
  qed.

  lemma RO_log_stable: forall r,
     mu dsample cpTrue = 1%r => 
     bd_hoare[ ARO(ROM.RO).o: mem r ARO.log ==> mem r ARO.log ] = 1%r.
  proof strict.
  by intros=> r Hs; apply (log_stable r ROM.RO); apply ROM.lossless_o.
  qed.

  lemma RO_upto_o: forall r, 
    equiv [ARO(ROM.RO).o ~ ARO(ROM.RO).o : 
      !mem r ARO.log{2} /\
      ={x, ARO.log} /\
      eq_except ROM.RO.m{1} ROM.RO.m{2} r ==>
      !mem r ARO.log{2} =>
        ={res, ARO.log} /\ eq_except ROM.RO.m{1} ROM.RO.m{2} r].
  proof strict.
  intros=> r; fun; if.
    by intros=> &1 &2 [r_nin_log] [[x_eq log_eq]] m_eq_exc;
       rewrite (fcongr length ARO.log{1} ARO.log{2}) //.
    by inline ROM.RO.o; wp; rnd; wp; skip; progress=> //; smt.
    by wp; skip; progress.
  qed.
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