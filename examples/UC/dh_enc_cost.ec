require import AllCore SmtMap Distr RndO CHoareTactic.
require import Composition_cost.

import CoreMap Bigxint.

(* Parties have some sort of identifier *)
type party.

(* 2 party Protocols have roles *)
type role = [ | I | R ].

(* Most protocols will pack data in packages *)
type 'a pkg = party * party * 'a.

op snd (p : 'a pkg) = p.`1.
op rcv (p : 'a pkg) = p.`2.
op pld (p : 'a pkg) = p.`3.

lemma pkgid (p p' : unit pkg): p = (snd p',rcv p', ()) => p = p' by smt().

schema cost_rcv ['a] `{P} {p : 'a pkg} : cost [P : rcv p] = '1 + cost [P : p].
schema cost_snd ['a] `{P} {p : 'a pkg} : cost [P : snd p] = '1 + cost [P : p].
schema cost_pld ['a] `{P} {p:'a pkg} : cost[P:pld p] = '1 + cost [P:p].
schema cost_tt : cost [true : tt] = '0.

hint simplify cost_pld, cost_rcv, cost_snd, cost_tt.

schema cost_eqI `{P} {r:role} : cost [P : r = I] = '1 + cost [P : r].
schema cost_eqR `{P} {r:role} : cost [P : r = R] = '1 + cost [P : r].
hint simplify cost_eqI, cost_eqR.

schema cost_eqNone ['a] `{P} {x:'a option} : cost [P: x = None] = '1 + cost [P : x].
hint simplify cost_eqNone.

schema cost_eqLefttt `{P} {r: (unit,unit) sum} : cost [P : r = Left tt] = '1 + cost [P : r].
schema cost_eqRighttt `{P} {r: (unit,unit) sum} : cost [P : r = Right tt] = '1 + cost [P : r].
hint simplify cost_eqLefttt, cost_eqRighttt.


(****************************************************************)
(*                    CHANNEL FUNCTIONALITIES                   *)
(****************************************************************)

type 'a stlkg = [
   | Ch_Init
   | Ch_Blocked1 of 'a
   | Ch_Wait of 'a
   | Ch_Blocked2 of 'a
   | Ch_Available of 'a 
].

schema cost_eqSRI ['a] {r2: ('a stlkg, 'a stlkg) sum option} : cost[true : r2 = Some (Right Ch_Init)] = N 3 + cost [true : r2].
hint simplify cost_eqSRI.

theory FChan.

type msg.

type state = (msg pkg) stlkg.

op leakpkg (p : msg pkg) : unit pkg = (snd p, rcv p, ()).

op init_st : state = Ch_Init.

op get_msg (st : state) (r : role) (p' : unit pkg)  = 
    with st = Ch_Init => None
    with st = Ch_Blocked1 _ => None
    with st = Ch_Wait _ => None
    with st = Ch_Blocked2 _ => None
    with st = Ch_Available p => if leakpkg p = p' /\ r = R then Some (pld p) else None.
 
op unblock (st : state) =
    with st = Ch_Init => st
    with st = Ch_Blocked1 p => Ch_Wait p
    with st = Ch_Wait _ => st
    with st = Ch_Blocked2 p => Ch_Available p
    with st = Ch_Available _ => st.

theory FAuth.

op set_msg (st : state) (r : role) (p : msg pkg) = 
    with st = Ch_Init => if r = I then Ch_Blocked2 p else st
    with st = Ch_Blocked1 _ => st
    with st = Ch_Wait _ => st
    with st = Ch_Blocked2 _ => st
    with st = Ch_Available _ => st.

type leakage = (msg pkg) stlkg.

op leak (st : state) = Some st.

schema cost_witness_msgpkg : cost [true: witness <:msg pkg>] = '1.
hint simplify cost_witness_msgpkg.

schema cost_init_st : cost [true : init_st] = '1.
schema cost_set_msg {r : role, p : msg pkg, st: state } : 
  cost [true : set_msg st r p] = N 3 + cost[true : st] + cost [true : r] + cost [true : p].
schema cost_get_msg {r : role, p : unit pkg, st: state } :
   cost [true :  get_msg st r p] = N 9 + cost[true : st] + cost [true : r] + cost [true : p].
schema cost_unblock {st:state} : cost [true : unblock st] = N 2 + cost[true : st].
schema cost_leak    {st: state} : cost [true : leak st] = '1 + cost[true : st].
hint simplify cost_init_st, cost_set_msg, cost_get_msg, cost_unblock, cost_leak.

clone import REAL_IDEAL as FAuthWorlds with
    type REAL.inputs <- role * msg pkg,
    type REAL.ask_outputs <- role * unit pkg,
    type REAL.outputs <- msg,
    type IDEAL.step <- unit,
    type IDEAL.ask_backdoor <- unit,
    type IDEAL.backdoor <- leakage.

import IDEAL.

module FAuth : PROTOCOL = {
   var st : state

   proc init() : unit = { st <- init_st; }

   proc inputs(r : role, p : msg pkg) : unit = {
      st <- set_msg st r p;
   }

   proc outputs(r : role, p : unit pkg) : msg option = {
      return get_msg st r p;
   }

   proc step() : unit = {
      st <- unblock st;
   }

   proc backdoor() : leakage option = {
      return leak st;
   }

}.

end FAuth.

(* We need to replace this with general parallel composition of
   functionalitites *)
theory F2Auth.

clone FAuth as FAuthLR.

clone FAuth as FAuthRL.

clone import PARA with
    type Pi1.inputs        <- role * msg pkg,
    type Pi1.ask_outputs   <- role * unit pkg,
    type Pi1.outputs       <- msg,
    type Pi1.step          <- unit,
    type Pi1.ask_backdoor  <- unit,
    type Pi1.backdoor      <- (msg pkg) stlkg,
    type Pi2.inputs        <- role * msg pkg,
    type Pi2.ask_outputs   <- role * unit pkg,
    type Pi2.outputs       <- msg,
    type Pi2.step          <- unit,
    type Pi2.ask_backdoor  <- unit,
    type Pi2.backdoor      <- (msg pkg) stlkg.

module F2Auth = PPara(FAuthLR.FAuth,FAuthRL.FAuth).

end F2Auth.

theory FSC.

type leakage = (unit pkg) stlkg.

op set_msg (st : state) (r : role) (p : msg pkg) = 
    with st = Ch_Init => if r = I then Ch_Blocked1 p else st
    with st = Ch_Blocked1 _ => st
    with st = Ch_Wait p' => if r = R /\ snd p' = snd p /\ rcv p' = rcv p then Ch_Blocked2 p' else st
    with st = Ch_Blocked2 _ => st
    with st = Ch_Available _ => st.

op leak (st : state) = 
    with st = Ch_Init => Some Ch_Init
    with st = Ch_Blocked1 p => Some (Ch_Blocked1 (leakpkg p))
    with st = Ch_Wait p => Some (Ch_Wait (leakpkg p))
    with st = Ch_Blocked2 p => Some (Ch_Blocked2 (leakpkg p))
    with st = Ch_Available p => Some (Ch_Available (leakpkg p)).

clone import REAL_IDEAL as FSCWorlds with
    type REAL.inputs <- role * msg pkg,
    type REAL.ask_outputs <- role * unit pkg,
    type REAL.outputs <- msg,
    type IDEAL.step <- unit,
    type IDEAL.ask_backdoor <- unit,
    type IDEAL.backdoor <- leakage.

import IDEAL.

module FSC : PROTOCOL = {
   var st : state

   proc init() : unit = { st <- init_st; }

   proc inputs(r : role, p : msg pkg) : unit = {
      st <- set_msg st r p;
   }

   proc outputs(r : role, p : unit pkg) : msg option = {
      return get_msg st r p;
   }

   proc step() : unit = {
      st <- unblock st;
   }

   proc backdoor() : leakage option = {
      return leak st;
   }

}.

end FSC.

end FChan.

(****************************************************************)
(*                  KEY EXCHANGE FUNCTIONALITY                  *)
(****************************************************************)


theory FKE.

type key.

op gen : key distr.

type kestate = [
  | KE_Init
  | KE_Blocked1 of unit pkg
  | KE_Wait of unit pkg
  | KE_Blocked2 of unit pkg
  | KE_Available of unit pkg
].

type state = {
  key : key;
  kst : kestate;
}.

type leakage = kestate.

op init key = {| key = key; kst = KE_Init |}.

schema cost_init `{P} {k:key} : cost[P:init k] = N 2 + cost[P:k].
hint simplify cost_init.

(* This is a hack *)
op kstp st = st.`kst.

(* Both parties need to provide the same party ids and roles
   for the protocol to start *)
op party_start (st : state) (r : role)  (p' : unit pkg) = 
 match (kstp st) with
    |  KE_Init        => if r = I
                         then {| st with kst = KE_Blocked1 p' |} 
                         else st
    |  KE_Blocked1 p  => st
    |  KE_Wait p      => if r = R /\ p = p' 
                         then {| st with kst = KE_Blocked2 p |} 
                         else st
    |  KE_Blocked2 p  => st
    |  KE_Available p => st
    end.

op party_output (st : state) (r : role) = 
    match (kstp st) with
    |  KE_Init        => None
    |  KE_Blocked1 p  =>  None
    |  KE_Wait p      => None
    |  KE_Blocked2 p  => if r = R
                         then Some st.`key
                         else None
    |  KE_Available p => if r = I \/ r = R
                         then Some st.`key
                         else None
    end.

op unblock st = 
    match (kstp st) with
    |  KE_Init        => st
    |  KE_Blocked1 p  => {| st with kst = KE_Wait p |} 
    |  KE_Wait p      => st
    |  KE_Blocked2 p  => {| st with kst = KE_Available p |} 
    |  KE_Available p => st
    end.

op leak st = Some st.`kst.

schema cost_leak `{P} {st:state} : cost [P:leak st] = '1 + cost[P:st].
hint simplify cost_leak.

schema cost_unblock `{P} {s:state} : cost[P : unblock s] = N 2 + cost[P : s].
hint simplify cost_unblock.

clone import REAL_IDEAL as FKEWorlds with
    type REAL.inputs <- role * unit pkg,
    type REAL.ask_outputs <- role,
    type REAL.outputs <- key,
    type IDEAL.step <- unit,
    type IDEAL.ask_backdoor <- unit,
    type IDEAL.backdoor <- leakage.

import IDEAL.

module FKE : PROTOCOL = {
   var st : state

   proc init() : unit = {
      var k;
      k <$ gen;
      st <- init k;
   }

   proc inputs(r : role, p : unit pkg) : unit = {
      st <- party_start st r p;
   }

   proc outputs(r : role) : key option = {
      return party_output st r;
   }

   proc step() : unit = {
      st <- unblock st;
   }

   proc backdoor() : leakage option = {
      return leak st;
   }

}.

(* The following subtheory defines a joint
    ideal functionality that combines FKE with
    FAuth in parallel. *)

theory FKEAuth.

clone import FChan.

clone import PARA with
    type Pi1.inputs        <- role * msg pkg,
    type Pi1.ask_outputs   <- role * unit pkg,
    type Pi1.outputs       <- msg,
    type Pi1.step          <- unit,
    type Pi1.ask_backdoor  <- unit,
    type Pi1.backdoor      <- (msg pkg) stlkg,
    type Pi2.inputs        <- role * unit pkg,
    type Pi2.ask_outputs   <- role,
    type Pi2.outputs       <- key,
    type Pi2.step          <- unit,
    type Pi2.ask_backdoor  <- unit,
    type Pi2.backdoor      <- kestate.

module FKEAuth = PPara(FAuth.FAuth,FKE).

end FKEAuth.

end FKE.

(****************************************************************)
(*                  DIFFIE - HELLMAN PROTOCOL                   *)
(****************************************************************)


require import DiffieHellman.

schema cost_dapply : cost[true : dapply (fun (x : t) => g ^ x) FDistr.dt] = 
                          N (FDistr.cdt + cgpow).

op adv_ddh : int -> real.

axiom adv_ddh_max cddh : 
   forall (A <:DDH.Adversary [ guess : `{N cddh}]) &m, 
     `| Pr[DDH.DDH0(A).main() @&m : res] - Pr[DDH.DDH1(A).main() @&m : res] | <= adv_ddh cddh.

theory DHKE. 

import DDH.

clone import FChan as HybFChan with
     type msg <- group.

(* This allows us to define a hybrid protocol that uses F2Auth.
   We don't intend to instantiate this functionality.  *)
clone import COMPOSITION with
   type Pi.REAL.inputs = (role * group pkg, role * group pkg) sum,
   type Pi.REAL.ask_outputs = (role * unit pkg, role * unit pkg) sum,
   type Pi.REAL.outputs = (group, group) sum,
   type Pi.IDEAL.step =  (unit,unit) sum,
   type Pi.IDEAL.ask_backdoor =  (unit,unit) sum,
   type Pi.IDEAL.backdoor = (state,state) sum,
   type R.inputs = role * unit pkg,
   type R.ask_outputs = role,
   type R.outputs = group,
   type R.step = role,
   type R.ask_backdoor = role,
   type R.backdoor = unit.

import RPi.

type istate = [
   | IInit
   | ISent
   | IDone
].

type rstate = [
   | RWaiting
   | RDone
].

schema cost_eqIInit `{P} {i:istate} : cost[P : i = IInit] = '1 + cost[P: i].
schema cost_eqISent `{P} {i:istate} : cost[P : i = ISent] = '1 + cost[P: i].
schema cost_eqRWaiting `{P} {i:rstate} : cost[P : i = RWaiting] = '1 + cost[P: i].
hint simplify cost_eqIInit, cost_eqISent, cost_eqRWaiting.

schema cost_witness_UPKG `{P} : cost[P : witness <:unit pkg>] = '1.
hint simplify cost_witness_UPKG.

module (DHKE : RHO) (Auth: Pi.REAL.IO) = {

   module Initiator = {
     var p : unit pkg
     var st : istate
     var _X : group
     var _x : F.t
     var _K  : group option

     proc init() : unit = {
        p <- witness;
        st <- IInit;
        _x <$ FDistr.dt;
        _X <- g^_x;
        _K <- None;
     }
  
     proc inputs(_p : unit pkg) : unit = { 
        if (st = IInit) {
           p <- _p;
           Auth.inputs(Left (I, (snd p, rcv p, _X))); 
           st <- ISent;
        }
     }
  
     proc outputs() : group option = { 
        return _K;
     }

     proc step() : unit = { 
        var _Y;
        if (st = ISent) {
           _Y <@ Auth.outputs(Right (R, (rcv p, snd p, ())));
           if (_Y <> None) {
              _K <- Some (oget (getr (oget _Y)) ^ _x);
              st <- IDone;
           }
        }
     }
  
     proc backdoor() : unit option = { 
         return None;
     }
   }

   module Responder = {
     var p : unit pkg
     var st : rstate
     var _Y : group
     var _y : F.t
     var _K  : group option

     proc init() : unit = {
        p <- witness;
        st <- RWaiting;
        _y <$ FDistr.dt;
        _Y <- g^_y;
        _K <- None;
     }
  
     proc inputs(_p : unit pkg) : unit = { 
        var _X;
        if (st = RWaiting) {
           _X <@ Auth.outputs(Left (R,_p));
           if (_X <> None) {
              p <- _p;
              Auth.inputs(Right (I, (rcv p, snd p, _Y))); 
              _K <- Some (oget (getl (oget _X)) ^ _y);
              st <- RDone;
           }
        }
     }
  
     proc outputs() : group option = { 
        return _K;
     }
  
     proc step() : unit = { 
     }
  
     proc backdoor() : unit option = { 
         return None;
     }
   }

   (* Now the protocol *)

   proc init() : unit = {
     Initiator.init();
     Responder.init();
   }

   proc inputs(r : role, p : unit pkg) : unit = {
      if (r = I) {
            Initiator.inputs(p);
      } else {
            Responder.inputs(p);
      }  
   }

   proc outputs(r : role) : group option = {
      var rr;
      rr <- None;
      if (r = I) {
         rr <@ Initiator.outputs();
      } else {
         rr <@ Responder.outputs();
      }
      return rr;
   }

   proc step(r : role) : unit = {
      if (r = I) {
         Initiator.step();
      } else {
         Responder.step();
      }
   }

   proc backdoor(r : role) : unit option = {
      var rr;
      if (r = I) {
         rr <@ Initiator.backdoor();
      } else {
         rr <@ Responder.backdoor();
      }
      return rr;
   }

}.

(* To have the type of the simulator we need now to clone FKE. *)

clone import FKE with
  type key <- group,
  op gen <- dapply (fun x => g^x) FDistr.dt,
  type FKEWorlds.REAL.step <- IDEAL.step,
  type FKEWorlds.REAL.ask_backdoor <- IDEAL.ask_backdoor,
  type FKEWorlds.REAL.backdoor <- IDEAL.backdoor,
  type FKEAuth.FChan.msg <- group.

clone import F2Auth as SimAuth.

import FKEWorlds.

module (DHKE_SIM : SIMULATOR) (FB : IDEAL.BACKDOORS) = {
   var _Keager : group

   var _X : group
   var _Y : group

   proc init() : unit = {
     var x,y;

     x <$ FDistr.dt;
     y <$ FDistr.dt;

     _X <- g^x;
     _Y <- g^y;

     SimAuth.F2Auth.init();
   }

   proc step(s : RPi.IDEAL.step) : unit = {
      var lk ,__Y;
      match (s) with
      | Left r => { 
         (* Stepping Rho *)
         lk <@ FB.backdoor();
         if (lk <> None) {
            match (oget lk) with 
            | KE_Init => {
                 (* Nothing happened on the inputs side,
                    so nothing to do *)
              }
            | KE_Blocked1 i => {
                 (* Initiator was given first input, but
                    this was not yet delivered. We do
                    nothing *)
              } 
            | KE_Wait i => {
                 (* Nothing happened on the receiver 
                    side yet, we wait *)
              }
            | KE_Blocked2 i => {
                 (* We got an input on the receiver 
                    side for sure.
                    The sender may now be terminating in the
                    real world, easy to check because we will
                    have a message to read also on the initiator
                    end of things *)
                    if (r = I) {    
                         __Y <@ SimAuth.F2Auth.outputs(Right (R,(rcv i, snd i, ())));
                        if (__Y <> None) {
                           FB.step();
                        }
                    }
              }
            | KE_Available i => {
                 (* Nothing to do *)
              }
            end;
         }
        }
      | Right r => { 
         (* Stepping F2Auth *)
         lk <@ FB.backdoor();
         if (lk <> None) {
            match (oget lk) with 
            | KE_Init => {
                 (* Nothing happened on the inputs side,
                    so nothing to do *)
              }
            | KE_Blocked1 i => {
                    if (r = Left ()) {
                        (* Initiator was given first input, and
                           this is now being delivered. *)
                        SimAuth.F2Auth.inputs(Left (I, (snd i, rcv i, _X))); 
                        SimAuth.F2Auth.step(Left ()); 
                        FB.step();
                    }                 
              } 
            | KE_Wait i => {
                        (* Nothing to do *)
              }
            | KE_Blocked2 i => {
                    if (r = Right ()) {
                      (* We got an input on the receiver 
                      side for sure.
                      This step to the channel is
                      the moment in which the message 
                      the receiver sent gets delivered. *)
                       SimAuth.F2Auth.inputs(Right (I, (rcv i, snd i, _Y))); 
                       SimAuth.F2Auth.step(Right ()); 
                    }                 
              }
            | KE_Available i => {
                 (* Nothing to do *)
              }
            end;
         }
        }
      end;
   }

   proc backdoor(b : RPi.IDEAL.ask_backdoor) : RPi.IDEAL.backdoor option = {
    var r2 : Pi.IDEAL.backdoor option;
    var r : (R.backdoor, Pi.IDEAL.backdoor) sum option;
    var lk; 
    
    match (b) with
    | Left m1 => { 
         r <- None;
         }
    | Right m2 => {
         (* Since things are out of sync we may need to cheat *)
         r <- None;
         lk <@ FB.backdoor();
         if (lk <> None) {
            match (oget lk) with 
            | KE_Init => {
               (* All in sync *)
               r2 <@ SimAuth.F2Auth.backdoor(m2);              
               r <- omap Right r2;       
              }
            | KE_Blocked1 i => {
               if (m2 = Left ()) { 
                  (* Initiator channel *)          
                  r <- Some (Right (Left (Ch_Blocked2 (snd i, rcv i,_X)))); 
               }
               else {
                  (* Responder channel *)          
                  r <- Some (Right (Right Ch_Init)); 
               }
              } 
            | KE_Wait i => {
               (* All in sync *)
               r2 <@  SimAuth.F2Auth.backdoor(m2);              
               r <- omap Right r2;       
              }
            | KE_Blocked2 i => {
               if (m2 = Left ()) {  
                  (* Initiator channel *)         
                  r <- Some (Right (Left (Ch_Available (snd i, rcv i, _X)))); 
               }
               else {
                  (* Responder channel *)
                  r2 <@  SimAuth.F2Auth.backdoor(Right ()); 
                  if (r2 = Some (Right Ch_Init)) {
                     r <- Some (Right (Right (Ch_Blocked2 (rcv i, snd i, _Y)))); 
                  } else {
                     r <- Some (Right (Right (Ch_Available (rcv i, snd i, _Y)))); 
                  }
               }
              }
            | KE_Available i => {
               (* All in sync *)
               r2 <@  SimAuth.F2Auth.backdoor(m2);              
               r <- omap Right r2;       
              }
            end;
         }
    }
    end;
    return r;
   }

}.

(**************************)
(* We now write the proof *)
(**************************)

(* EAGER SAMPLE IN RHO *)

module type RHOEager (P : Pi.REAL.IO) = {
  proc init(__X : group ,__Y : group, __Z : group) : unit {}
  
  proc inputs(i : R.inputs) : unit {P.inputs, P.outputs}
  
  proc outputs(o : R.ask_outputs) : R.outputs option {P.inputs, P.outputs}
  
  proc step(m : R.step) : unit {P.inputs, P.outputs}
  
  proc backdoor(m : R.ask_backdoor) : R.backdoor option {P.inputs, P.outputs}
}.

module (DHKE_Eager : RHOEager) (Auth: Pi.REAL.IO) = {

   module Initiator = {

     proc init(__X : group) : unit = {
        DHKE.Initiator.p <- witness;
        DHKE.Initiator.st <- IInit;
        DHKE.Initiator._X <- __X;
        DHKE.Initiator._K <- None;
     }

     proc step() : unit = { 
        var _Y;
        if (DHKE.Initiator.st = ISent) {
           _Y <@ Auth.outputs(Right (R, (rcv DHKE.Initiator.p, snd DHKE.Initiator.p, ())));
           if (_Y <> None) {
              DHKE.Initiator._K <- Some DHKE_SIM._Keager;
              DHKE.Initiator.st <- IDone;
           }
        }
     }

     include DHKE(Auth).Initiator [ -init, step]
   }

   module Responder = {

     proc init(__Y) : unit = {
        DHKE.Responder.p <- witness;
        DHKE.Responder.st <- RWaiting;
        DHKE.Responder._K <- None;
        DHKE.Responder._Y <- __Y;
     }
  
     proc inputs(p : unit pkg) : unit = { 
        var _X;
        if (DHKE.Responder.st = RWaiting) {
           _X <@ Auth.outputs(Left (R, p));
           if (_X <> None) {
              DHKE.Responder.p <- p;
              Auth.inputs(Right (I, (rcv DHKE.Responder.p, snd DHKE.Responder.p, DHKE.Responder._Y))); 
              DHKE.Responder._K <- Some DHKE_SIM._Keager;
              DHKE.Responder.st <- RDone;
           }
        }
     }
     include DHKE(Auth).Responder [ -init, inputs]
   }

   (* Now the protocol with eager sampling *)

   proc init(__X, __Y, __K : group) : unit = {
     DHKE_SIM._Keager <- __K;
     Initiator.init(__X);
     Responder.init(__Y);    
   }

   include DHKE(Auth) [ -init, inputs, step]

   proc inputs(r : role, p : unit pkg) : unit = {
      if (r = I) {
           Initiator.inputs(p);
      } else {
           Responder.inputs(p); 
     }
   }

   proc step(r : role) : unit = {
      if (r = I) {
         Initiator.step();
      } else {
         Responder.step();
      }
   }

}.

(* Now composition with eager sampling *)

module CompRFEager (Rho : RHOEager, F : Pi.IDEAL.PROTOCOL) = {
  proc init(__X : group, __Y : group, __K : group) : unit = {
    F.init();
    Rho(F).init(__X, __Y, __K);
  }
  
  include Rho(F) [inputs, outputs]
  
  proc step(m : RPi.IDEAL.step) : unit = {
    match (m) with
    | Left m1 =>  Rho(F).step(m1);
    | Right m2 =>  F.step(m2);
    end;
  }
  
  proc backdoor(m : RPi.IDEAL.ask_backdoor) : RPi.IDEAL.backdoor option = {
    var r1 : R.backdoor option;
    var r2 : Pi.IDEAL.backdoor option;
    var r : (R.backdoor, Pi.IDEAL.backdoor) sum option;
    
    match (m) with
    | Left m1 => { 
         r1 <@ Rho(F).backdoor(m1);
         r <- omap Left r1;
         }
    | Right m2 => {
         r2 <@ F.backdoor(m2);
         r <- omap Right r2;
    }
    end;
    
    return r;
  }
}.

(* Finally the game with eager sampling and DDH attacker type *)

module type EagerPROTOCOL = {
   include REAL.PROTOCOL [-init]
   proc init(__X : group, __Y : group, __K : group) : unit
}.

module UC_emul_DDH(E : REAL.ENV, P : EagerPROTOCOL) : Adversary = {
  proc guess(__X : group, __Y : group, __K : group) : bool = {
    var b : bool;
    
    P.init(__X,__Y,__K);
    b <@ E(P).distinguish();
    
    return b;
  }
}.

section.

(* Security proof first uses DDH to replace the key with a random
   group element in the real-world. Then it shows that the simulator
   perfectly emulates this modified game *)

declare module Z : REAL.ENV {-DHKE_SIM, -FKE, 
                           -HybFChan.F2Auth.FAuthLR.FAuth,
                           -HybFChan.F2Auth.FAuthRL.FAuth,
                           -DHKE}.

lemma hop1 &m : 
   Pr[ REAL.UC_emul(Z,CompRF(DHKE,HybFChan.F2Auth.F2Auth)).main() @ &m : res] =
   Pr[ DDH0(UC_emul_DDH(Z,CompRFEager(DHKE_Eager,HybFChan.F2Auth.F2Auth))).main() @ &m : res].
proof.
byequiv => //.
proc.
inline *.
swap {1} 5 -4.
swap {1} 10 -8.
seq 2 2 : (={glob Z} /\ DHKE.Initiator._x{1} = x{2} /\ DHKE.Responder._y{1} = y{2}).
by sim />.
wp;call (_: ={glob HybFChan.F2Auth.F2Auth,
           DHKE.Initiator.p,DHKE.Initiator.st,DHKE.Initiator._X,
           DHKE.Initiator._K,
           DHKE.Responder.p,DHKE.Responder.st,DHKE.Responder._Y,
           DHKE.Responder._K} /\
           DHKE_SIM._Keager{2} = DHKE.Responder._Y{1}^DHKE.Initiator._x{1} /\
           DHKE_SIM._Keager{2} = DHKE.Initiator._X{1}^DHKE.Responder._y{1} /\

           (match DHKE.Initiator.st{1} with
            | IInit => 
                  HybFChan.F2Auth.FAuthLR.FAuth.st{1} = Ch_Init /\
                  HybFChan.F2Auth.FAuthRL.FAuth.st{1} = Ch_Init 
            | ISent => 
                 match (HybFChan.F2Auth.FAuthLR.FAuth.st{1}) with
                 | Ch_Init => true
                 | Ch_Blocked1 p => true
                 | Ch_Wait p => true
                 | Ch_Blocked2 p   => p = (snd DHKE.Initiator.p{1}, rcv DHKE.Initiator.p{1}, DHKE.Initiator._X{1})
                 | Ch_Available p => p = (snd DHKE.Initiator.p{1}, rcv DHKE.Initiator.p{1}, DHKE.Initiator._X{1})
                 end /\

                 match HybFChan.F2Auth.FAuthRL.FAuth.st{1} with
                 | Ch_Init => true
                 | Ch_Blocked1 p => true
                 | Ch_Wait p => true
                 | Ch_Blocked2 p   => p = (rcv DHKE.Responder.p{1}, snd DHKE.Responder.p{1}, DHKE.Responder._Y{1})
                 | Ch_Available p => p = (rcv DHKE.Responder.p{1}, snd DHKE.Responder.p{1}, DHKE.Responder._Y{1})
                 end
            | IDone =>  DHKE.Responder.st{1} = RDone /\
                        DHKE.Initiator._K{1} = Some (DHKE.Responder._Y{1}^DHKE.Initiator._x{1})
            end) /\
           (match DHKE.Responder.st{1} with
            | RWaiting => DHKE.Initiator.st{1} = IInit \/ 
                  (DHKE.Initiator.st{1} = ISent /\ HybFChan.F2Auth.FAuthRL.FAuth.st{1} = Ch_Init)
            | RDone => 
                 (DHKE.Initiator.st{1} = ISent \/ DHKE.Initiator.st{1} = IDone)  /\
                  DHKE.Responder._K{1} = Some (DHKE.Initiator._X{1}^DHKE.Responder._y{1})
               end)
); last first.

(* Init *)
auto => />; smt(@G).

(* Now the call *)
+ by proc;inline *; auto => /> /#.
+ by sim />.
+ proc; match; first 2 by auto.
  + move => m1 m1_0; inline *.
    sp 1 1; if => //=; if => //=.
    by sp 1 1; match; auto => /#.
  + move => m1 m1_0; inline *; auto => /#.
by proc; inline *; match; auto => /#.
qed.

(* we'll need a complex relation on states *)
op staterel (p1 : unit pkg) ist1 rst1 (kst2 : kestate) 
            (fLR1 fRL1 fLR2 fRL2 : HybFChan.state) _Xp _Yp _KI _KR (_K : group) =
    match kst2 with
    (* KE INITIAL STATE: NOTHING HAPPENED YET *)
    | KE_Init =>
        (ist1 = IInit)   /\ (rst1 = RWaiting) /\ 
        (fLR1 = Ch_Init) /\ (fRL1 = Ch_Init) /\ 
        (fLR2 = Ch_Init) /\ (fRL2 = Ch_Init) /\ 
        (_KI = None)     /\ (_KR = None)
    (* KE BLOCKED1 STATE: ENV PROVIDED INPUT TO INITIATOR BUT X NOT YET DELIVERED *)
    | KE_Blocked1 p => 
        p1 = p /\ 
        (ist1 = ISent)         /\ (rst1 = RWaiting) /\ 
        (fLR1 = Ch_Blocked2 _Xp) /\ (fRL1 = Ch_Init)  /\ 
        (fLR2 = Ch_Init)       /\ (fRL2 = Ch_Init)   /\ 
        (_KI = None)           /\ (_KR = None)
    (* KE WAITING STATE: ENV PROVIDED INPUT TO INITIATOR AND X DELIVERED. *)
    | KE_Wait p => 
        p1 = p /\ 
        (ist1 = ISent)           /\ (rst1 = RWaiting) /\ 
        (fLR1 = Ch_Available _Xp) /\ (fRL1 = Ch_Init) /\ 
        (fLR2 = Ch_Available _Xp) /\ (fRL2 = Ch_Init) /\ 
        (_KI = None)             /\ (_KR = None)
    (* KE BLOCKED2 STATE: ENV PROVIDED INPUT TO BOTH PARTIES AND Y YES/NO DELIVERED *)
    | KE_Blocked2 p => 
        p1 = p /\ 
        (ist1 = ISent) /\ (rst1 = RDone) /\ 
        (fLR1 = Ch_Available _Xp)         /\ 
        (fRL2 = Ch_Init \/ fRL2 = Ch_Available _Yp) /\
              (fRL2 = Ch_Init          => fRL1 = Ch_Blocked2 _Yp)   /\
              (fRL2 = Ch_Available _Yp => fRL1 = Ch_Available _Yp) /\
        (fLR2 = Ch_Available _Xp) /\ 
        (_KI = None) /\ (_KR = Some _K)
    (* KE AVAILABLE STATE: ALeft DONE *)
    | KE_Available p => 
        p1 = p /\ 
        (ist1 = IDone) /\ (rst1 = RDone) /\ 
        (fLR1 = Ch_Available _Xp) /\ (fRL1 = Ch_Available _Yp) /\ 
        (fLR2 = Ch_Available _Xp) /\ (fRL2 = Ch_Available _Yp) /\ 
        (_KI = Some _K)  /\ (_KR = Some _K)
    end.


lemma hop2 &m : 
   Pr[ DDH1(UC_emul_DDH(Z,CompRFEager(DHKE_Eager,HybFChan.F2Auth.F2Auth))).main() @ &m : res] =
   Pr[ REAL.UC_emul(Z,CompS(FKE, DHKE_SIM)).main() @ &m : res].
proof.
byequiv => //.
proc. 

(* Initializations *)
inline {1} UC_emul_DDH(Z, CompRFEager(DHKE_Eager, HybFChan.F2Auth.F2Auth)).guess.
inline {2} CompS(FKE, DHKE_SIM).init. 
seq 7 2 : (={glob Z} /\
           HybFChan.F2Auth.FAuthLR.FAuth.st{1} = SimAuth.FAuthLR.FAuth.st{2} /\
           HybFChan.F2Auth.FAuthRL.FAuth.st{1} = SimAuth.FAuthRL.FAuth.st{2} /\
           FAuthLR.FAuth.st{2} = Ch_Init /\
           FAuthRL.FAuth.st{2} = Ch_Init /\
           DHKE.Initiator._K{1} = None /\
           DHKE.Responder._K{1} = None /\
           DHKE.Initiator._X{1} = DHKE_SIM._X{2} /\
           DHKE.Responder._Y{1} = DHKE_SIM._Y{2}  /\
           DHKE_SIM._Keager{1} = FKE.st.`key{2} /\
           DHKE.Initiator.st{1} = IInit /\
           DHKE.Responder.st{1} = RWaiting /\
           FKE.st.`kst{2}  = KE_Init
           ).
+ inline *.
  wp; swap {1} 3 -2; rnd; rnd;  wp; rnd (fun x => g^x) (fun x => log x). 
  auto => />; progress; 1,4:algebra. 
  + rewrite dmapE /(\o) /pred1; congr; apply fun_ext => z; algebra.
  by rewrite supp_dmap; exists zL; trivial.

(* Calling the environment *)
wp; call (_: 
   DHKE.Initiator._X{1} = DHKE_SIM._X{2} /\
   DHKE.Responder._Y{1} = DHKE_SIM._Y{2} /\
   DHKE_SIM._Keager{1} = FKE.st{2}.`key /\
   staterel DHKE.Initiator.p{1}
            DHKE.Initiator.st{1} 
            DHKE.Responder.st{1} 
            FKE.st{2}.`kst 
            HybFChan.F2Auth.FAuthLR.FAuth.st{1}
            HybFChan.F2Auth.FAuthRL.FAuth.st{1}
            FAuthLR.FAuth.st{2}
            FAuthRL.FAuth.st{2}
            (snd DHKE.Initiator.p{1}, rcv DHKE.Initiator.p{1}, DHKE.Initiator._X{1})
            (rcv DHKE.Initiator.p{1}, snd DHKE.Initiator.p{1}, DHKE.Responder._Y{1})
            DHKE.Initiator._K{1}
            DHKE.Responder._K{1}
            DHKE_SIM._Keager{1}).

(* INPUTS *)
(* PY: SMT doesn't catch this without rewrite *)
+ by proc; inline *;wp;skip; rewrite /staterel; smt(pkgid). 

(* OUTPUTS *)
+ by proc;inline *;auto => />; rewrite /staterel => /#. 

(* STEP *)
+ proc.
  match; first 2 by smt().
  (* We step Rho *)
  + by move => m1 p; inline *;wp;skip; smt(). 
  (* We step F2Auth *)
  by move => m2 p;inline *; auto => /> &1 &2; rewrite /staterel /leak oget_some /unblock /kstp /#.

(* BACKDOOR *)
+ proc.
  match; first 2 by smt().
  (* Backdoor Rho *)
  + by move => *; inline *;auto => /#.   
  (* Backdoor F2Auth *)
  by move=> m2 p; inline *; auto => /> &1 &2; rewrite /staterel /leak oget_some /unblock /kstp /rcv /#.

(* WRAP-UP CALL *)
by auto => /#.
qed.

(* THIS IS THE MAIN DH UC SECURITY THEOREM *)

lemma KEAdv &m :
      `| Pr[ REAL.UC_emul(Z,CompRF(DHKE,HybFChan.F2Auth.F2Auth)).main() @ &m : res] - 
         Pr[ REAL.UC_emul(Z,CompS(FKE, DHKE_SIM)).main() @ &m : res] | = 
      `| Pr[ DDH0(UC_emul_DDH(Z,CompRFEager(DHKE_Eager,HybFChan.F2Auth.F2Auth))).main() @ &m : res] - 
         Pr[ DDH1(UC_emul_DDH(Z,CompRFEager(DHKE_Eager,HybFChan.F2Auth.F2Auth))).main() @ &m : res] |.
proof. by rewrite (hop1 &m) (hop2 &m). qed.

end section.

abstract theory C.

clone FKEWorlds.C as RC
  with op csi = {|
    cinit     = 2 * (1 + cgpow + FDistr.cdt);
    cstep     = 26; 
    cs_s      = 1; 
    cs_b      = 1;
    cbackdoor = 20;
    cb_s      = 0;
    cb_b      = 1; 
  |}
  proof csi_pos by smt (ge0_cg ge0_cf) .

op cddh =  8 + RC.c.`cd + RC.c.`ci * 29 + RC.c.`co * 2 + RC.c.`cs * 23 + RC.c.`cb * 5.

lemma KEAdv_ex &m :
    exists (S <: RC.CSIMULATOR {DHKE_SIM}), 
      forall (Z <: RC.CENV { -HybFChan.F2Auth.FAuthLR.FAuth, -HybFChan.F2Auth.FAuthRL.FAuth, -DHKE, -FKE, -DHKE_SIM}),
      `| Pr[ REAL.UC_emul(Z,CompRF(DHKE,HybFChan.F2Auth.F2Auth)).main() @ &m : res] - 
         Pr[ REAL.UC_emul(Z,CompS(FKE, S)).main() @ &m : res] | <= adv_ddh cddh.
proof. 
  exists DHKE_SIM; split.
  + split; [ | split] => kb ks FB hkb hks.
    + proc; inline *; wp; do !rnd; skip => />.
      rewrite FDistr.dt_ll /#.
    + proc; exlim s => -[]r.
      + match Left 1; [1: by auto; smt() | 2: done].
        seq 1 : true time [ N 25; FB.backdoor : 0; FB.step : 1 ]; 1: done.
        + by call (:true); auto => />. 
        if => //.
        + exlim (oget lk) => -[|i|i|i|i].
          + by match KE_Init 1 => //=; auto => /> /#.
          + by match KE_Blocked1 1 => //=; auto => /> /#. 
          + by match KE_Wait 1 => //=; auto => /> /#.
          + match KE_Blocked2 1 => //=; auto => />; 1: smt().
            if => //.
            + seq 1 : true time [N 2; FB.step : 1] => //.
              + by inline *; sp 1 => //=; match Right 1 => //=; auto => /> /#.
              by if => //; 1: call (:true); auto => />.
            by auto => /> /#.          
          by match KE_Available 1 => //=; auto => /> /#.
        by auto=> /> /#.
      match Right 1; [1: by auto; smt() | 2: done].
      seq 1 : true time [ N 20; FB.backdoor : 0; FB.step : 1 ]; 1: done.
      + by call (:true); auto => />. 
      if => //.
      + exlim (oget lk) => -[|i|i|i|i].
        + by match KE_Init 1 => //=; auto => /> /#. 
        + match KE_Blocked1 1 => //=; auto => />; 1: smt().
          if => //.
          + call(:true); inline *; sp 1 => //=.
            by match Left 1 => //=; auto => /> /#. 
          by auto => /> /#.
        + by match KE_Wait 1 => //=; auto => /> /#. 
        + match KE_Blocked2 1 => //=; auto => />; 1: smt().
          if => //.
          + inline *; sp 1 => //=.
            by match Right 1 => //=; auto => /> /#. 
          by auto => /> /#. 
        match KE_Available 1 => //=; auto => /> /#.
      by auto=> /> /#. 
    proc.
    exlim b => -[] mi. 
    + match Left 1; [1: by auto; smt() | 2: done].
      by auto => /> /#.
    match Right 1; [1: by auto; smt() | 2: done].
    seq 2 : true time [N 18] => //.
    + by call (:true); auto => />.
    by inline *; auto => /> /#.     

  move=> Z. have ->:= KEAdv Z &m.
  apply (adv_ddh_max cddh (UC_emul_DDH(Z, CompRFEager(DHKE_Eager, HybFChan.F2Auth.PARA.PPara(HybFChan.F2Auth.FAuthLR.FAuth, HybFChan.F2Auth.FAuthRL.FAuth))))).
  proc; inline *.
  call (:true; time [
     (CompRFEager(DHKE_Eager, HybFChan.F2Auth.PARA.PPara(HybFChan.F2Auth.FAuthLR.FAuth, HybFChan.F2Auth.FAuthRL.FAuth)).inputs : [N 29]),
     (CompRFEager(DHKE_Eager, HybFChan.F2Auth.PARA.PPara(HybFChan.F2Auth.FAuthLR.FAuth, HybFChan.F2Auth.FAuthRL.FAuth)).outputs : [N 2]),
     (CompRFEager(DHKE_Eager, HybFChan.F2Auth.PARA.PPara(HybFChan.F2Auth.FAuthLR.FAuth, HybFChan.F2Auth.FAuthRL.FAuth)).step : [N 23]),
     (CompRFEager(DHKE_Eager, HybFChan.F2Auth.PARA.PPara(HybFChan.F2Auth.FAuthLR.FAuth, HybFChan.F2Auth.FAuthRL.FAuth)).backdoor : [N 5]) ]) => /= *.
  + by proc; inline *; auto => />.
  + by proc; inline *; auto => />.
  + by proc; inline *; auto => /> /#.
  + by proc; inline *; auto => /> /#.
  auto => />.
  rewrite !bigi_constz; smt (RC.c_pos).
qed.

end C.

end DHKE.

(****************************************************************)
(*                  SECURE CHANNEL BASED ON OTP                 *)
(****************************************************************)

theory OTP.

type msg = group.
type key = group.
type cph = group.

op gen = dapply (fun x => g^x) FDistr.dt.

op enc(m : msg, k : key) = m * k.
op dec(c : cph, k : key) = c / k.

lemma correctness m k :
   dec (enc m k) k = m.
proof. rewrite /dec /enc -div_def log_mul -{2}(gpow_log m); congr; ring. qed.

schema cost_dec `{P} {c : cph, k : key} : cost [P: dec c k] = N cgdiv + cost[P:c] + cost[P:k].
schema cost_enc `{P} {c : cph, k : key} : cost [P: enc c k] = N cgmul + cost[P:c] + cost[P:k].
hint simplify cost_dec, cost_enc.

import DHKE.FKE.

(* To have the type of the simulator we need now to clone ideal
   secure channel functionality FSC. *)

clone import FChan with
  type msg <- group,
  type FSC.FSCWorlds.REAL.step <- (role, (unit, unit) sum) sum,
  type FSC.FSCWorlds.REAL.ask_backdoor <- (role, (unit, unit) sum) sum,
  type FSC.FSCWorlds.REAL.backdoor <- (unit,  (FKEAuth.FChan.state, kestate) sum) sum.

(* This allows us to define a hybrid protocol that uses FKEAuth. *)
clone import COMPOSITION as C_OTP with
   type Pi.REAL.inputs = (role * group pkg,role * unit pkg) sum,
   type Pi.REAL.ask_outputs = (role * unit pkg, role) sum,
   type Pi.REAL.outputs = (group,group) sum,
   (**************************************************)
   (* We look ahead to an instantiation based on DHKE *)
   type Pi.REAL.step = (unit, (role, (unit, unit) sum) sum) sum,
   type Pi.REAL.ask_backdoor = (unit, (role, (unit, unit) sum) sum) sum,
   type Pi.REAL.backdoor = (FKEAuth.FChan.state, (unit, (DHKE.HybFChan.state,
DHKE.HybFChan.state) sum) sum) sum,
   (**************************************************)
   type Pi.IDEAL.step = (unit,unit) sum,
   type Pi.IDEAL.ask_backdoor = (unit, unit) sum,
   type Pi.IDEAL.backdoor = (FKEAuth.FChan.state,kestate) sum,
   type R.inputs = role * msg pkg,
   type R.ask_outputs = role * unit pkg,
   type R.outputs = msg,
   type R.step = role,
   type R.ask_backdoor = role,
   type R.backdoor = unit,
   (* We also set the stage for transitivity *)
   type TRANS.H2.IDEAL.step = unit,
   type TRANS.H2.IDEAL.ask_backdoor = unit,
   type TRANS.H2.IDEAL.backdoor = FChan.FSC.leakage.

import RPi.

type iscstate = [
   | ISCInit
   | ISCSentKE
   | ISCDone
].

schema cost_eqISCInit   `{P} {i:iscstate} : cost [P : i = ISCInit] = '1 + cost [P : i].
schema cost_eqISCSentKE `{P} {i:iscstate} : cost [P : i = ISCSentKE] = '1 + cost [P : i].
schema cost_eqISCDone   `{P} {i:iscstate} : cost [P : i = ISCDone] = '1 + cost [P : i].
hint simplify cost_eqISCInit, cost_eqISCSentKE, cost_eqISCDone.

module (OTP : RHO) (KEAuth: Pi.REAL.IO) = {

   module Initiator = {
     var p : msg pkg
     var st : iscstate

     proc init() : unit = {
        p <- witness;
        st <- ISCInit;
     }
  
     (* To avoid confusion we only accept one input on initiator side *)
     proc inputs(_p : msg pkg) : unit = { 
        if (st = ISCInit) {
           p <- _p;
           KEAuth.inputs(Right (I, (snd p, rcv p, ()))); 
           st <- ISCSentKE;
        }
     }
  
     proc outputs() : group option = { return None; }

     (* Initiator needs to be stepped to be aware of KE completion *)
     proc step() : unit = { 
        var _K;
        if (st = ISCSentKE) {
           _K <@ KEAuth.outputs(Right I);
           if (_K <> None) {
              KEAuth.inputs(Left (I, (snd p, rcv p, enc (pld p) (oget (getr (oget _K))))));
              st <- ISCDone;
           }
        }
     }
  
     proc backdoor() : unit option = { return None; }
   }

   module Responder = {

     proc init() : unit = { }
  
     (* We let KE functionality manage inputs, only one will
        be accepted, and it must mach the one previously given
        by initiator *)
     proc inputs(_p : msg pkg) : unit = { 
        KEAuth.inputs(Right (R, (snd _p, rcv _p, ())));
     }

     (* Output becomes available whenever the authentication
        channel is unblocked *)  
     proc outputs(_p : unit pkg) : group option = {
        var rr,m,_K;
        rr <- None; 
        m <@ KEAuth.outputs(Left (R,  (snd _p, rcv _p, ())));
        if (m <> None) {
           _K <@ KEAuth.outputs(Right R);
           rr <- Some (dec (oget (getl (oget m))) (oget (getr (oget _K))));
        }
        return rr;
     }
  
     proc step() : unit = { }
  
     proc backdoor() : unit option = { return None; }
   }

   (* Now the protocol *)

   proc init() : unit = {
     Initiator.init();
     Responder.init();
   }

   proc inputs(r : role, p : msg pkg) : unit = {
      if (r = I) {
            Initiator.inputs(p);
      } else {
            Responder.inputs(p);
      }  
   }

   proc outputs(r : role, p : unit pkg) : group option = {
      var rr;
      rr <- None;
      if (r = I) {
         rr <@ Initiator.outputs();
      } else {
         rr <@ Responder.outputs(p);
      }
      return rr;
   }

   proc step(r : role) : unit = {
      if (r = I) {
         Initiator.step();
      } else {
         Responder.step();
      }
   }

   proc backdoor(r : role) : unit option = {
      var rr;
      if (r = I) {
         rr <@ Initiator.backdoor();
      } else {
         rr <@ Responder.backdoor();
      }
      return rr;
   }
}.


(* The simulator uses it's own copy of the low level
   ideal functionalities, which it uses in the simulation *)
clone import FKEAuth as SimKEAuth.

import FSC.
import FSCWorlds.

module (OTP_SIM : SIMULATOR) (FB : IDEAL.BACKDOORS) = {

   proc init() : unit = {
     SimKEAuth.FKEAuth.init();
   }

   proc step(s : RPi.IDEAL.step) : unit = {
     var lsc ,lke, lfa,fresh;
     match s with
     | Left m1 => {
           (* Stepping rho *)
           lsc <@ FB.backdoor();
           match (oget lsc) with
           | Ch_Init => { (* Nothing happended yet *) }
           | Ch_Blocked1 p => { (* Initiator has provided input, but responder still did not *) }
           | Ch_Wait p => { (* Initiator has provided input, but responder still did not *) }
           | Ch_Blocked2 p => {
               if (m1 = I) {
                   (* Stepping initiator when both already provided input.
                      Step causes initiator to progress if KE just finished *)
                   lfa <@ SimKEAuth.FKEAuth.backdoor(Left ());
                   match (oget (getl (oget lfa))) with
                   | Ch_Init => {
                     lke <@ SimKEAuth.FKEAuth.backdoor(Right ());
                      match  (oget (getr (oget lke))) with
                      | KE_Init => {}
                      | KE_Blocked1 p => {}
                      | KE_Wait p => {}
                      | KE_Blocked2 p => {}
                      | KE_Available p => {
                            fresh <$ dapply (fun x => g^x) FDistr.dt;
                            SimKEAuth.FKEAuth.inputs(Left (I, (snd p, rcv p, enc  (g^F.zero) fresh)));
                        }
                      end; 
                     }
                   | Ch_Blocked1 p' => { }
                   | Ch_Wait p' => { }
                   | Ch_Blocked2 p' => { }
                   | Ch_Available p' => { }
                   end;
               } else {
                   (* Stepping responder has no effect *)
               }
             }
           | Ch_Available p => { }
           end;
             
       }
     | Right m2 => {
           match m2 with
           | Left m21 => {
              (* Stepping FAuth: pass it along but check if receiver done. *)
                 SimKEAuth.FKEAuth.step(Left ());
                 lfa <@ SimKEAuth.FKEAuth.backdoor(Left ());
                 match (oget (getl (oget lfa))) with
                 | Ch_Init => { }
                 | Ch_Blocked1 p' => { }
                 | Ch_Wait p' => { }
                 | Ch_Blocked2 p' => { }
                 | Ch_Available p' => { FB.step(); }
                 end;
             }
           | Right m22 => {
              (* Stepping FKE: Just pass it along, but check if inputs
                 needs to be given first. *)
                 lsc <@ FB.backdoor();
                 match (oget lsc) with
                 | Ch_Init => { }
                 | Ch_Blocked1 p' => { 
                    lke <@ SimKEAuth.FKEAuth.backdoor(Right ());
                     match  (oget (getr (oget lke))) with
                     | KE_Init => {  SimKEAuth.FKEAuth.inputs(Right (I,(snd p', rcv p', ()))); FB.step(); }
                     | KE_Blocked1 p => {}
                     | KE_Wait p => { }
                     | KE_Blocked2 p => {}
                     | KE_Available p => { }
                     end; 
                   }
                 | Ch_Wait p' => { }
                 | Ch_Blocked2 p' => {
                    lke <@ SimKEAuth.FKEAuth.backdoor(Right ());
                     match  (oget (getr (oget lke))) with
                     | KE_Init => {}
                     | KE_Blocked1 p => {}
                     | KE_Wait p => { SimKEAuth.FKEAuth.inputs(Right (R,p));  }
                     | KE_Blocked2 p => {}
                     | KE_Available p => { }
                     end; 
                    }
                 | Ch_Available p' => { }
                 end;
                 SimKEAuth.FKEAuth.step(Right ());
             }
           end;
       }
     end;
   }

   proc backdoor(b : RPi.IDEAL.ask_backdoor) : RPi.IDEAL.backdoor option = {
       var rr,lsc,lfa,lke;
       rr <- None;
       match b with 
       | Left b1 => {
             (* Rho has no leakage *)
         } 
       | Right b2 => {
            match b2 with
            | Left c1 => {
               (* Auth backdoor: just type conversions *)
                 lfa <@ SimKEAuth.FKEAuth.backdoor(Left ());
                 match (oget (getl (oget lfa))) with
                 | Ch_Init => { 
                     rr <- Some (Right (Left (Ch_Init))); 
                   }
                 | Ch_Blocked1 p' => { 
                     rr <- Some (Right (Left (Ch_Blocked1 p'))); 
                   }
                 | Ch_Wait p' => {  
                     rr <- Some (Right (Left (Ch_Wait p')));  
                   }
                 | Ch_Blocked2 p' => { 
                     rr <- Some (Right (Left (Ch_Blocked2 p')));  
                   }
                 | Ch_Available p' => {  
                     rr <- Some (Right (Left (Ch_Available p')));  
                   }
                 end;
          }
          | Right c2 => {
               (* Key exchange leakage: sim sometimes lags behind, but we don't 
                  step FKE here. *)
               lsc <@ FB.backdoor();
               match (oget lsc) with
               | Ch_Init => { rr <- Some (Right (Right KE_Init)); }
               | Ch_Blocked1 p => { rr <- Some (Right (Right (KE_Blocked1 p))); }
               | Ch_Wait p => { rr <- Some (Right (Right (KE_Wait p))); }
               | Ch_Blocked2 p => {
                  lfa <@ SimKEAuth.FKEAuth.backdoor(Left ());
                  match (oget (getl (oget lfa))) with
                  | Ch_Init => {
                    lke <@ SimKEAuth.FKEAuth.backdoor(Right ());
                     match  (oget (getr (oget lke))) with
                     | KE_Init => { rr <- Some (Right (Right (KE_Blocked2 p))); }
                     | KE_Blocked1 p' => { rr <- Some (Right (Right (KE_Blocked2 p))); }
                     | KE_Wait p' => { rr <- Some (Right (Right (KE_Blocked2 p))); }
                     | KE_Blocked2 p' => { rr <- Some (Right (Right (KE_Blocked2 p))); }
                     | KE_Available p' => { rr <- Some (Right (Right (KE_Available p))); }
                     end; 
                    }
                  | Ch_Blocked1 p' => { }
                  | Ch_Wait p' => { }
                  | Ch_Blocked2 p' => { 
                       rr <- Some (Right (Right (KE_Available p))); 
                    }
                  | Ch_Available p' => { 
                       rr <- Some (Right (Right (KE_Available p))); 
                    }
                  end;
                }
             | Ch_Available p => { rr <- Some (Right (Right (KE_Available p))); }
             end;
             }
          end;
         } 
       end;
       return rr;
   }

}.

section.

(* AS A PROOF INSTRUMENT WE NEED TO MOVE THE SAMPLING OF THE AGREED KEY TO WHERE THE 
   SIMULATOR DOES IT *)
module (OTPLazy : RHO) (KEAuth: Pi.REAL.IO) = {
   module Initiator = {
     include OTP(KEAuth).Initiator [- step]

     proc step() : unit = { 
        var _K,fresh;
        if (OTP.Initiator.st = ISCSentKE) {
           _K <@ DHKE.FKE.FKEAuth.FKEAuth.outputs(Right I);
           if (_K <> None) {
              fresh <$  dapply (fun x => g^x) FDistr.dt;
              (* WE PUNCH THROUGH THE INTERFACE TO HARDWIRE A FRESH KEY *)
              DHKE.FKE.FKE.st <- {| DHKE.FKE.FKE.st with key = fresh |};
              DHKE.FKE.FKEAuth.FKEAuth.inputs(Left (I, 
                 (snd OTP.Initiator.p, rcv OTP.Initiator.p, enc (pld OTP.Initiator.p) fresh)));
              OTP.Initiator.st <- ISCDone;
           }
        }
     }
   }


   (* Now the protocol *)

   include OTP(KEAuth) [- init,step]

   proc init() : unit = {
     Initiator.init();
     OTP(KEAuth).Responder.init();
   }

   proc step(r : role) : unit = {
      if (r = I) {
         Initiator.step();
      } else {
         OTP(KEAuth).Responder.step();
      }
   }
}.

declare module Z : REAL.ENV {-FKE, -FSC, -FChan.FAuth.FAuth, -OTP_SIM, 
                             -OTP, -DHKE.FKE.FKEAuth.FChan.FAuth.FAuth, -OTPLazy}.

(* To prove that our change of sampling in OTP is sound we use a generic
   eager sampling module *)
local clone import GenEager with
  type from <- unit, 
  type to   <- group, 
  op sampleto <- fun (x:unit) => dapply (fun (x : t) => g ^ x) FDistr.dt
  proof *.
realize sampleto_ll.
proof. by move => _; rewrite /= weight_dmap FDistr.dt_ll. qed.

(* We rewrite our new version of OTP using this module *)
local module OTP_AUX (O:RO) (KEAuth: Pi.REAL.IO) = {
   module Initiator = {
     include OTP(KEAuth).Initiator [- step]

     proc step() : unit = { 
        var _K,fresh;
        if (OTP.Initiator.st = ISCSentKE) {
           _K <@ DHKE.FKE.FKEAuth.FKEAuth.outputs(Right I);
           if (_K <> None) {
              fresh <@ O.get();
              (* WE PUNCH THROUGH THE INTERFACE TO HARDWIRE A FRESH KEY *)
              DHKE.FKE.FKE.st <- {| DHKE.FKE.FKE.st with key = fresh |};
              DHKE.FKE.FKEAuth.FKEAuth.inputs(Left (I, 
                 (snd OTP.Initiator.p, rcv OTP.Initiator.p, enc (pld OTP.Initiator.p) fresh)));
              OTP.Initiator.st <- ISCDone;
           }
        }
     }
  }


   (* Now the protocol *)

   include OTP(KEAuth) [- init,step]

   proc init() : unit = {
     O.init();
     O.sample();
     Initiator.init();
     OTP(KEAuth).Responder.init();
   }

   proc step(r : role) : unit = {
      if (r = I) {
         Initiator.step();
      } else {
         OTP(KEAuth).Responder.step();
      }
   }
}.

local module D (O:RO) = {
   proc distinguish = REAL.UC_emul(Z,CompRF(OTP_AUX(O),DHKE.FKE.FKEAuth.FKEAuth)).main
}.

lemma OTPAdv1 &m :
      Pr[ REAL.UC_emul(Z,CompRF(OTP,DHKE.FKE.FKEAuth.FKEAuth)).main() @ &m : res] =
      Pr[ REAL.UC_emul(Z,CompRF(OTPLazy,DHKE.FKE.FKEAuth.FKEAuth)).main() @ &m : res].
proof.
  have -> : 
    Pr[ REAL.UC_emul(Z,CompRF(OTP,DHKE.FKE.FKEAuth.FKEAuth)).main() @ &m : res] =
    Pr[ D(RO).distinguish() @ &m : res].
  + byequiv (_: ={glob Z} ==> ={res}) => //.
    proc.
    call (_: ={glob DHKE.FKE.FKEAuth.FChan.FAuth.FAuth, glob OTP} /\ 
            FKE.st{1}.`kst = FKE.st{2}.`kst /\
            () \in RO.m{2} /\
            FKE.st{1}.`key = oget RO.m{2}.[()] /\
            (DHKE.FKE.FKEAuth.FChan.FAuth.FAuth.st{2} <> Ch_Init => 
                   FKE.st{2}.`key = oget RO.m{2}.[()])
             ); conseq />.
    + proc => /=; inline *; wp; skip => /> &1 &2; rewrite /party_start /kstp /= /#.
    + proc => /=; inline *; wp; skip => /> &1 &2; rewrite /party_output /kstp /= /#.    
    + proc; match; 1,2 : smt().
      + move=> m1 m2.      
        inline OTP(DHKE.FKE.FKEAuth.FKEAuth).step OTP_AUX(RO, DHKE.FKE.FKEAuth.FKEAuth).step.
        sp 1 1; if => //; conseq />; last by sim.
        inline *.
        if => //.
        match Right {1} 2; 1: by auto => /#.
        match Right {2} 2; 1: by auto => /#.
        sp; if; last done.
        + move => /> &1 &2.
          rewrite /get_as_Right /= /party_output /kstp => <-.
          by case: (FKE.st{1}.`kst) => />.
        rcondf{2} 3; 1: by auto.
        match Left {1} 2; 1: auto => /#.
        match Left {2} 6; 1: auto => /#.
        auto => /> &1 &2 ?? heq.
        rewrite /party_output /kstp /get_as_Left /get_as_Right /= heq.
        case : (FKE.st{1}.`kst) => />; rewrite //=. 
        rewrite /= dmap_ll //=.
        by apply  FDistr.dt_ll.
      move => m1 m2. 
      inline DHKE.FKE.FKEAuth.FKEAuth.step.
      sp 1 1; match; 1,2: smt().
      + by move=> *; inline *; auto => /#.
      move=> tt1 tt2; inline *; auto => /> &1 &2 heq ??.
      by rewrite /unblock /kstp heq; case: (FKE.st{2}.`kst) => />.
    + proc.
      match; 1,2 : smt().
      + by move=> m1 m2; inline *; sim; auto.
      by move=> m1 m2; inline *; auto => /> /#.
    inline *; auto => />; rewrite /is_lossless weight_dmap FDistr.dt_ll /= => *.
    by rewrite get_setE /init /= mem_empty /= mem_set.
  have -> : Pr[D(RO).distinguish() @ &m : res] = Pr[D(LRO).distinguish() @ &m : res].
  + byequiv (RO_LRO_D(D)) => //.
  byequiv (_: ={glob Z} ==> ={res}) => //.
  proc.
  call (_: ={glob DHKE.FKE.FKEAuth.FChan.FAuth.FAuth, glob OTP, glob FKE} /\ 
            () \in RO.m{1} = (OTP.Initiator.st{1} = ISCDone)); conseq />; 2,4: by sim.
  + proc; if => //; conseq />; 2: by sim.
    by inline *; auto => />.
  + proc; match; 1,2 : smt().
    + move=> m1 m2; inline *; sp 1 1; if => //.
      if => //.
      match Right {1} 2; 1: by auto => /#.
      match Right {2} 2; 1: by auto => /#.
      sp; if => //; auto => /> &1 &2 -> /= ??.
      by rewrite get_setE /= mem_set.
    by move=> m1 m2;conseq />; inline *; sim; auto.
  by inline *; auto => /> ?; rewrite mem_empty.
qed.

(* THE INVARIANT RELATES THE STATES OF THE REAL AND SIMULATED
   FUNCTIONALITIES *)

op invotp ip1 kst1 kst2 (cst2 : group pkg stlkg) ast2 ast1 ist1 =
   match cst2 with
   | Ch_Init => (* We just started, no inputs, all funcs in init *)
                kst1.`kst = kst2.`kst /\
                kst2.`kst = KE_Init /\
                ast2 = FChan.init_st /\
                ast1 = DHKE.FKE.FKEAuth.FChan.init_st /\ 
                ist1 = ISCInit
   | Ch_Blocked1 p => 
                (* There has been a initiator input, but nothing else,
                   so things only moved in the real world key exchance *)
                ip1 = p /\ 
                kst1.`kst = KE_Blocked1 (snd p,rcv p, ()) /\
                kst2.`kst = KE_Init /\
                ast2 = FChan.init_st /\ 
                ast1 = Ch_Init /\ 
                ist1 = ISCSentKE 
   | Ch_Wait p => 
                (* KE has been stepped to wait in the real world and simulator
                   picks it up to make everything match again at waiting state *)
                ip1 = p /\ 
                kst1.`kst = kst2.`kst /\
                kst1.`kst = KE_Wait (snd p,rcv p, ()) /\
                ast2 = FChan.init_st /\ 
                ast1 = Ch_Init /\ 
                ist1 = ISCSentKE
   | Ch_Blocked2 p => 
                ip1 = p  /\
                (* We create a disjunction in the invariant based on the state of various 
                    functionalities *)

                (
                (* We may have just come from wait state *)
                   (kst1.`kst = KE_Blocked2 (snd p,rcv p, ()) /\ 
                     kst2.`kst = KE_Wait (snd p,rcv p, ()) /\ 
                      ast1 = Ch_Init /\
                       ist1 = ISCSentKE /\ ast2 = Ch_Init) \/
                (* Key Exchange finished but nobody knows: we get here through steps to ke *)
                   (kst1.`kst = KE_Available (snd p,rcv p, ()) /\ 
                     kst2.`kst = KE_Available (snd p,rcv p, ()) /\ 
                      ast1 = Ch_Init /\
                       ist1 = ISCSentKE /\ ast2 = Ch_Init) \/
                (* Key Exchange finished and initiator did its part but still undelivered *)
                   (kst1.`kst = KE_Available (snd p,rcv p, ()) /\ 
                     kst2.`kst = KE_Available (snd p,rcv p, ()) /\
                      ast1 = Ch_Blocked2 
                                     (snd p, rcv p, enc (pld p) kst1.`key) /\
                      ast2 = Ch_Blocked2 (snd p, rcv p, enc (pld p) kst1.`key) /\
                       ist1 = ISCDone)
                 ) 
   | Ch_Available p => 
                ip1 = p /\ 
                kst1.`kst = KE_Available (snd p,rcv p, ()) /\
                kst2.`kst = KE_Available (snd p,rcv p, ()) /\
                ast1 = Ch_Available 
                                    (snd p, rcv p, enc (pld p) kst1.`key) /\
                ist1 = ISCDone /\ 
                ast2 = Ch_Available (snd p, rcv p, enc (pld p) kst1.`key)
   end.

lemma alg_lem1 (a b c : group):
   a = a * inv b * c * b * inv c.
proof. rewrite log_bij !(Ring.rw_algebra, inv_def); ring. qed.

lemma alg_lem2 (a b c : group):
   a = a * b * inv c * inv b * c.
proof. rewrite log_bij !(Ring.rw_algebra, inv_def); ring. qed.

lemma sup_lem1 (a b c : group):
   a \in gen =>
     mu1 gen a = mu1 gen (a * inv b * c).
have genu : (is_uniform gen); first by apply dmap_uni;smt(@DiffieHellman).
have genl : (is_lossless gen); first by apply dmap_ll;smt(@DiffieHellman).
rewrite !(mu1_uni_ll _ _ genu genl). 
move => agen; rewrite agen //=.
have -> // : (a * inv b * c \in gen).
rewrite /gen supp_dmap.
by exists ((log a) - (log b) + (log c));smt(@DiffieHellman).
qed.

lemma sup_lem2 (a b c : group):
    a \in gen =>
      a * b * inv c \in gen.
proof.
rewrite /gen //=  => *; rewrite supp_dmap. 
by exists (log a + log b + (log (inv c)));smt(@DiffieHellman).
qed.

lemma enc_lem (a b c : group):
    enc b a = enc c (a * b * inv c).
proof.
rewrite /enc; rewrite log_bij !(Ring.rw_algebra, inv_def); ring. 
qed.

lemma OTPAdv2 &m :
      Pr[ REAL.UC_emul(Z,CompRF(OTPLazy,DHKE.FKE.FKEAuth.FKEAuth)).main() @ &m : res] =
         Pr[ REAL.UC_emul(Z,CompS(FSC, OTP_SIM)).main() @ &m : res].
byequiv => //.
proc.
inline *.
swap {1} [2..3] -1.
swap {2} [3..4] -2.
seq 2 2 : (={glob Z,glob FKE} /\ FKE.st.`kst{2} = KE_Init); first by auto => /#.
call (_: invotp OTP.Initiator.p{1}
                FKE.st{1}
                FKE.st{2} 
                FSC.st{2}
                FChan.FAuth.FAuth.st{2} 
                DHKE.FKE.FKEAuth.FChan.FAuth.FAuth.st{1} 
                OTP.Initiator.st{1}); last by auto => />.

(* INPUTS *)
+ by proc;inline *;wp;skip;rewrite /invotp; smt().

(* OUTPUTS *)
+ proc;inline *.
  by wp; skip => /> &1 &2; rewrite /rcv /= /party_output /invotp /kstp /=; smt (correctness). 

(* Step *)
+ proc;inline *.
  match; first 2 by smt().
  (* STEP RHO *)
  + move => m1 m1_0.
    sp 1 0; if{1}.
    (* STEP INITIATOR *)
    + sp 0 1; match{2}.
      + by rcondf {1} 1; move => *; wp;skip;smt().
      + move => p. 
        rcondt {1} 1; first by move => *; wp;skip;smt().
        by sp 1 0; match{1};  by move => *;rcondf {1} 5; move => *;wp;skip;smt().
      + move => p.
        rcondt {1} 1; first by move => *; wp;skip;smt().
        by sp 1 0; match{1};  by move => *;rcondf {1} 5; move => *;wp;skip;smt().
      + move => p.
        rcondt {2} 1; first by move => *; wp;skip;smt().
        if{1}.
        + seq 0 3 : (#pre /\  (oget (getl (oget lfa{2}))) = Ch_Init); 
            first by wp;skip;smt().
          match {2}; last 4 by move => p'; exfalso; smt().
          seq 3 3 : (#pre /\ 
              (_K{1} <> None => 
                 FKE.st{1}.`kst = KE_Available (snd OTP.Initiator.p{1}, 
                                                rcv OTP.Initiator.p{1},()) /\
                (oget (getr (oget lke{2}))) = FKE.st{1}.`kst) /\
              (_K{1} = None => 
                FKE.st{1}.`kst <> KE_Available (snd OTP.Initiator.p{1}, 
                                                rcv OTP.Initiator.p{1},()) /\
                (oget (getr (oget lke{2}))) = KE_Wait (snd OTP.Initiator.p{1}, 
                                                        rcv OTP.Initiator.p{1},()))); 
            first by wp;skip;rewrite /invotp /#.
          case (_K{1} = None).
          + rcondf {1} 1; first by auto => /#.
            by match {2}; auto => /#.
          rcondt {1} 1; first by auto => />.
          match {2}; first 4 by auto => /#.
          move => p0.
          swap {1} 2 1.
          seq 2 2 : (#pre /\ ={i} /\ 
                    i{1} = Left (I,  (snd OTP.Initiator.p{1},  
                                        rcv OTP.Initiator.p{1}, 
                                        enc (pld OTP.Initiator.p{1}) fresh{1}))).
          + wp; rnd (fun (fresh1 : group) => 
                       fresh1 * (pld OTP.Initiator.p{1}) * (inv (g ^ F.zero))) 
                    (fun (fresh2 : group) => 
                       fresh2 * (inv (pld OTP.Initiator.p{1})) * (g ^ F.zero)).
            by wp;skip;smt(alg_lem1 sup_lem1 sup_lem2 alg_lem2 enc_lem).
          by wp;skip;rewrite /invotp;smt().
        seq 0 3 : (#pre /\ (oget (getl (oget lfa{2}))) <> Ch_Init); 
          first by wp;skip;smt().
        by match {2}; 1: (by exfalso => /#); auto => /#.
      by move => p; rcondf{1} 1; [ by move => *;auto => /#| by auto=> />].
    (* STEP RESPONDER *)
    sp 0 1; match{2}; first 3 by auto;rewrite /invotp /#.
    + by move => p;rcondf{2} 1; auto; rewrite /invotp /#.
    by auto; rewrite /invotp /#.

  (* STEP HYBRID FUNC *)
  move => m2 m2_0.
  sp 1 0;match; 1,2: (by smt()). 
  (* FAuth *)
  + auto; rewrite /invotp /#.
  (* KE *)
  move => *;wp;skip;rewrite /invotp => /> &1 &2.
  by case: (FSC.st{2}) => /> /#. 

(* BACKDOOR *)
proc.
sp 0 1; match; first 2 by smt().

(* Backdooring the protocol *)
+ by move => m1 b1; inline *; wp;skip;rewrite /invotp; smt().

(* Backdooring the hybrid functionalities *)
move => m2 b2; inline *.
by sp 1 0; match; 1,2: (by smt()); auto; rewrite /invotp /#.
qed.

(* Main theorem for secure channel based on OTP using ideal functionalities
   for key exchange and authenticated message transfer. Simulation is perfect. *)
lemma OTPAdv &m :
      Pr[ REAL.UC_emul(Z,CompRF(OTP,DHKE.FKE.FKEAuth.FKEAuth)).main() @ &m : res] =
         Pr[ REAL.UC_emul(Z,CompS(FSC, OTP_SIM)).main() @ &m : res].
proof. by rewrite (OTPAdv1 &m) -(OTPAdv2 &m). qed.

end section.

(* NOW WE MOVE TO INSTANTIATING FKE WITH DHKE *)

clone import PARA_IR with
    type Pi1.inputs        <- role * group pkg,
    type Pi1.ask_outputs   <- role * unit pkg,
    type Pi1.outputs       <- group,
    type Pi1.step          <- unit,
    type Pi1.ask_backdoor  <- unit,
    type Pi1.backdoor      <- DHKE.FKE.FKEAuth.FChan.state,
    type Pi2.REAL.inputs        <- role * unit pkg,
    type Pi2.REAL.ask_outputs   <- role,
    type Pi2.REAL.outputs       <- group,
    type Pi2.REAL.step          <- (role,(unit,unit) sum) sum,
    type Pi2.REAL.ask_backdoor  <- (role,(unit,unit) sum) sum,
    type Pi2.REAL.backdoor      <- (unit, (DHKE.HybFChan.state, DHKE.HybFChan.state) sum) sum,
    type Pi2.IDEAL.step          <- unit,
    type Pi2.IDEAL.ask_backdoor  <- unit,
    type Pi2.IDEAL.backdoor      <- DHKE.FKE.kestate. 


(* We re-express OTP as an instance of PARA_IR. *)
module I_PARA = I.PPara(DHKE.FKE.FKEAuth.FChan.FAuth.FAuth, DHKE.FKE.FKE).
module I_OTP = C_OTP.CompRF(OTP,I_PARA).

(* This also allows us to express an instantiated KE *)
module DHKE_ = DHKE.COMPOSITION.CompRF(DHKE.DHKE,DHKE.HybFChan.F2Auth.F2Auth).
module R_PARA = R.PPara(DHKE.FKE.FKEAuth.FChan.FAuth.FAuth, DHKE_).
(* And also to express parametrizing OTP with this *)
module R_OTP = C_OTP.CompRP(OTP,R_PARA).

op cz : cenv.
axiom cz_pos : cenv_pos cz.

clone PARA_IR.C as PIC with
  op cz = {|
    cd = 2 + cz.`cd + 9 * cz.`ci + (22 + cgdiv) * cz.`co + (19 + cgmul) * cz.`cs + 5 * cz.`cb;
    ci = cz.`cs + cz.`ci;
    co = cz.`cs + 2 * cz.`co;
    cs = cz.`cs;
    cb = cz.`cb;
  |},
  op cf1 = {|
    cpinit     = 1;
    cpinputs   = 3;
    cpoutputs  = 9;
    cpstep     = 2;
    cpbackdoor = 1;
  |},
  op cs2 = {|
    cinit     = 2 * (1 + cgpow + FDistr.cdt);
    cstep     = 26; 
    cs_s      = 1; 
    cs_b      = 1;
    cbackdoor = 20;
    cb_s      = 0;
    cb_b      = 1; 
  |}
  proof cz_pos by smt (cz_pos ge0_cg)
  proof cf1_pos by done
  proof cs2_pos by smt (ge0_cg ge0_cf).

clone DHKE.C as DHKEC with
  op RC.c <- PIC.CPi2.c
  proof RC.c_pos by apply PIC.CPi2.c_pos. 

(* THIS PROOF IS ALL BOILER PLATE: WE APPLY THE REFINEMENT OF UC THEOREM FOR INSTANTIATING
   ONE OF THE FUNCTIONALITIES IN A PARALLEL COMPOSITION OF FUNCTIONALITIES, AND THEN PROVE THAT
   EVERYTHING MATCHES SYNTACTICALLY. THE THEOREM STATES THAT THE DHKE SIMULATOR CAN BE USED TO
   CONSTRUCT A SIMULATOR FOR THE INSTANTIATED PROTOCOL, WHICH UC REALIZES THE PROTOCOL WITH
   AN IDEAL FKE. BELOW WE APPLY TRANSITIVITY TO DERIVE THE MAIN THEOREM. *)

op csi = {|
   cinit = PIC.CRI.csi.`cinit;
   cstep = max 2 (1 + PIC.CRI.csi.`cstep + PIC.CRI.csi.`cs_s + PIC.CRI.csi.`cs_b * 4);
   cs_s  = max 1 PIC.CRI.csi.`cs_s;
   cs_b  = PIC.CRI.csi.`cs_s;
   cbackdoor = max 7 (3 + PIC.CRI.csi.`cbackdoor + PIC.CRI.csi.`cb_s + PIC.CRI.csi.`cb_b * 4);
   cb_s      = PIC.CRI.csi.`cb_s;
   cb_b      = max 1 PIC.CRI.csi.`cb_b;
|}.

lemma InstOTPAdv &m :    
  exists (S <: RPi.SIMULATOR {+DHKE.DHKE_SIM}
               [init : {} `{N csi.`cinit},
                step : `{N csi.`cstep, #FB.step : csi.`cs_s, #FB.backdoor : csi.`cs_b},
                backdoor : `{N csi.`cbackdoor, #FB.step : csi.`cb_s, #FB.backdoor : csi.`cb_b}]) , 
      forall (Z <:  C_OTP.RPi.REAL.ENV {-OTP, -FKE, -DHKE.FKE.FKEAuth.FChan.FAuth.FAuth,
                              -DHKE.DHKE_SIM, -DHKE_, -FSC, -FChan.FAuth.FAuth}
                  [distinguish : {#I.inputs, #I.outputs, #I.step, #I.backdoor}
                               `{N cz.`cd,
                                 #I.inputs : cz.`ci,
                                 #I.outputs : cz.`co,
                                 #I.step : cz.`cs,
                                 #I.backdoor : cz.`cb}
              ]), 
      `| Pr[ C_OTP.RPi.REAL.UC_emul(Z,R_OTP).main() @ &m : res] -
         Pr[ C_OTP.RPi.REAL.UC_emul(Z,C_OTP.RPi.CompS(I_OTP, S)) .main() @ &m : res] | <= adv_ddh DHKEC.cddh.
proof.
have [S h] := DHKEC.KEAdv_ex &m.
have := PIC.ex_compose DHKE.FKE.FKEAuth.FChan.FAuth.FAuth _ _ _ _ _ DHKE_ DHKE.FKE.FKE S &m (adv_ddh DHKEC.cddh) _;
  1..5: by proc; auto => />.
move=> /= Z; have := h Z.
have -> : 
    Pr[FKEWorlds.REAL.UC_emul(Z, DHKE.COMPOSITION.CompRF(DHKE.DHKE, DHKE.HybFChan.F2Auth.PARA.PPara(DHKE.HybFChan.F2Auth.FAuthLR.FAuth, DHKE.HybFChan.F2Auth.FAuthRL.FAuth))).main
     () @ &m : res] =
   Pr[Pi2.REAL.UC_emul(Z, DHKE.COMPOSITION.CompRF(DHKE.DHKE, DHKE.HybFChan.F2Auth.PARA.PPara(DHKE.HybFChan.F2Auth.FAuthLR.FAuth, DHKE.HybFChan.F2Auth.FAuthRL.FAuth))).main () @ &m : res].
+ by byequiv => //; sim.
have -> //: Pr[FKEWorlds.REAL.UC_emul(Z, FKEWorlds.CompS(FKE, S)).main() @ &m : res] = Pr[Pi2.REAL.UC_emul(Z, Pi2.CompS(FKE, S)).main() @ &m : res].
+ by byequiv => //; sim.
move=> [S1 hS1].
exists (C_OTP.Sid(S1)); split.
+ split; [|split] => kb ks FB *.
  + by proc true : time []. 
  + proc; exlim m => -[] mi.
    + match Left 1; [auto; smt() | done |].
      by call (:true); auto => /> /#. 
    match Right 1;[auto; smt() | done |].
    call (:true; time [(C_OTP.Sid(S1, FB).FBPi.step : [N 1; FB.step : 1]), 
                       (C_OTP.Sid(S1, FB).FBPi.backdoor : [N 4; FB.backdoor : 1])]).
    + by move=> *; proc; call(:true); auto.
    + by move=> *; proc; call(:true); auto.
    auto => />.
    rewrite !bigi_constz; 1..2 : smt (PIC.CRI.csi_pos).
    by rewrite /= !StdBigop.Bigint.bigi_constz; smt (PIC.CRI.csi_pos).
  proc; exlim m => -[] mi.
  + match Left 1; [auto; smt() | done |].
    by wp; call (:true); auto => />. 
  match Right 1;[auto; smt() | done |].
  wp;call (:true; time [(C_OTP.Sid(S1, FB).FBPi.step : [N 1; FB.step : 1]), 
                        (C_OTP.Sid(S1, FB).FBPi.backdoor : [N 4; FB.backdoor : 1])]).
  + by move=> *; proc; call(:true); auto.
  + by move=> *; proc; call(:true); auto.
  auto => />.
  rewrite !bigi_constz; 1..2 : smt (PIC.CRI.csi_pos).
  by rewrite /= !StdBigop.Bigint.bigi_constz; smt (PIC.CRI.csi_pos).
move => Z.
have -> : Pr[ C_OTP.RPi.REAL.UC_emul(Z,R_OTP).main() @ &m : res] = 
          Pr[ RI.REAL.UC_emul(C_OTP.CompZR(Z, OTP), R.PPara(DHKE.FKE.FKEAuth.FChan.FAuth.FAuth, DHKE_)).main () 
               @ &m : res].
+ byequiv => //.
  proc;inline *.
  wp;call(_: ={glob OTP, glob DHKE.DHKE, glob DHKE.HybFChan.F2Auth.F2Auth, 
               glob DHKE.FKE.FKEAuth.FChan.FAuth.FAuth}); first 4 by sim.
  by auto.
have -> : Pr[RPi.REAL.UC_emul(Z, RPi.CompS(I_OTP, C_OTP.Sid(S1))).main() @ &m : res] = 
          Pr[RI.REAL.UC_emul(C_OTP.CompZR(Z, OTP), RI.CompS(I.PPara(DHKE.FKE.FKEAuth.FChan.FAuth.FAuth, FKE), S1)).main() @ &m : res]. 
+ byequiv => //. 
  proc;inline *.
  wp;call(_: ={glob S1, glob OTP, glob DHKE.FKE.FKEAuth.FChan.FAuth.FAuth, glob FKE}); 
     first 2 by sim.
  + proc; match; [1,2: by smt()]; move=> *;inline *; auto.
    call (: ={glob S1, glob OTP, glob DHKE.FKE.FKEAuth.FChan.FAuth.FAuth, glob FKE}).
    + by proc; inline *; match Right {1} 2; auto => /#.
    + by proc; inline *; match Right {1} 2; auto => /#.
    by auto => />.
  + proc; match; 1,2: by smt().
    + by move => *; inline *;auto => /> /#.
    move => *; inline *.
    wp; call (: ={glob S1, glob OTP, glob DHKE.FKE.FKEAuth.FChan.FAuth.FAuth, glob FKE}).
    + by proc; inline *; match Right {1} 2; auto => /#.
    + by proc; inline *; match Right {1} 2; auto => /#.
    by auto => />.
  wp; call (:true); auto => />.
apply (hS1 (C_OTP.CompZR(Z, OTP))). 
move=> kb ks ko ki I0 * {S h S1 hS1}.
proc.
call (:true; time [ (CompR_I(OTP, I0).inputs  : [N 9; I0.inputs : 1]), 
                    (CompR_I(OTP, I0).outputs : [N (22 + cgdiv); I0.outputs : 2]), 
                    (CompR_I(OTP, I0).step    : [N (19 + cgmul); I0.inputs : 1; I0.outputs : 1; I0.step : 1]), 
                    (CompR_I(OTP, I0).backdoor : [N 5; I0.backdoor : 1])]) => /= *.
+ proc; inline *;if => //.
  + sp => //; if => //; auto; last by smt().
    by call (:true); auto => />.
  by call(:true);auto => />. 
+ proc; inline *; sp => //; if => //; auto => />; 1: smt(ge0_cg).
  seq 3 : true time [N (13 + cgdiv); I0.outputs : 1] => //.
  + by call (:true); auto => /> /#.
  if => //=; auto => />; last smt(ge0_cg).
  by call(:true); auto => /> /#.
+ proc; exlim m => -[] mi.
  + match Left 1; [auto; smt() | done |].
    inline *; sp => //; if => //; last by auto; smt (ge0_cg).
    if => //; last by auto; smt (ge0_cg).
    seq 1 : true time [N (14 + cgmul); I0.inputs : 1] => //.
    + by call(:true); auto => /> /#.
    if => //; auto; 2: smt(ge0_cg).
    call (:true); auto => /> /#.
  match Right 1; [auto; smt() | done |].
  call(:true); auto => />; smt (ge0_cg).
+ proc. exlim m => -[] mi.
  + match Left 1; [auto; smt() | done |].
    by inline *; auto => /#.
  match Right 1; [auto; smt() | done |].
  by wp; call (:true); auto.  
inline *; auto => />.
rewrite !bigi_constz 1..4:[smt(cz_pos)] /=.
rewrite !StdBigop.Bigint.bigi_constz; smt (cz_pos).
qed.

import DHKE.
(* import COMPOSITION. *)
import FKE.
import FKEAuth. 

(****************************************************************)
(*  MAIN THEOREM: ASSUMING 3 AUTHENTICATED COMMUNICATIONS       *)
(*  DHKE + OTP UC REALIZES A ONE-SHOT SECURE CHANNEL.           *)
(****************************************************************)

(* Again, the steps in this proof are all boiler plate; we just apply transitivity.
   We could have equality here, but we need to have a strengthened transitivity lemma for perfect simulators. *)

clone C_OTP.TRANS.C as COTPTC with
  op cz   <- cz,
  op cs12 <- csi,
  op cs23 <- {|
    cinit     = 3 + FDistr.cdt + cgpow;
    cstep     = 34 + cgmul + 2 * cgpow + FDistr.cdt;
    cs_s      = 1;
    cs_b      = 1;
    cbackdoor = 25;
    cb_s      = 0;
    cb_b      = 1;
    |}
  proof cz_pos by apply cz_pos
  proof cs12_pos by smt (PIC.CRI.csi_pos)
  proof cs23_pos by smt (ge0_cf ge0_cg).
 
(* add proof *)

(* hint simplify cost_dapply. *)


schema cost_party_start `{P} {s:state, r:role, p : unit pkg}: cost[P: party_start s r p] = N 5 + cost[P:s] + cost[P:r] + cost[P:p].
hint simplify cost_party_start.

lemma MainTheorem &m : 
  exists (S <: TRANS.GOAL.SIMULATOR),
    forall (Z <: RPi.REAL.ENV {-S, -FSC, -CompRP(OTP,R.PPara(FChan.FAuth.FAuth, COMPOSITION.CompRF(DHKE,HybFChan.F2Auth.F2Auth)))}
      [distinguish : 
        `{N cz.`cd,
          #I.inputs : cz.`ci,
          #I.outputs : cz.`co,
          #I.step : cz.`cs,
          #I.backdoor : cz.`cb}]
    ),   
      `| Pr[ RPi.REAL.UC_emul(Z,CompRP(OTP,R.PPara(FChan.FAuth.FAuth, COMPOSITION.CompRF(DHKE,HybFChan.F2Auth.F2Auth)))).main() @ &m : res] -
         Pr[ RPi.REAL.UC_emul(Z,TRANS.GOAL.CompS(FSC, S)).main() @ &m : res] | <=
       adv_ddh (11 + cz.`cd + 42 * cz.`ci + (52 + cgdiv) * cz.`co + (93 + cgmul) * cz.`cs + 15 * cz.`cb).
proof.
have -> : 11 + cz.`cd + 42 * cz.`ci + (52 + cgdiv) * cz.`co + (93 + cgmul) * cz.`cs + 15 * cz.`cb = DHKEC.cddh by smt().
have [S hS]:= InstOTPAdv &m.
have [S1 hS1]:= COTPTC.ex_uc_transitivity
      (CompRP(OTP, R.PPara(FChan.FAuth.FAuth, COMPOSITION.CompRF(DHKE, HybFChan.F2Auth.F2Auth)))) 
      (CompRF(OTP,FKEAuth)) FSC S OTP_SIM _ _ _ &m (adv_ddh DHKEC.cddh) 0%r _ _.
+ move=> kb ks FB *.
  instantiate h := (cost_dapply {k : group}).
  proc; inline *; wp; rnd; 1: by rewrite h.
  by auto => />; rewrite h dmap_ll 1:FDistr.dt_ll /= /#.
+ move=> kb ks FB *.                  
  proc. 
  exlim (s) => -[]mi.
  + match Left 1;[auto; smt() | done |].
    seq 1 : true time [N (33 + cgmul + 2 * cgpow + FDistr.cdt)] => //.
    + by call (:true); auto => /> /#. 
    inline *; wp.
    exlim (oget lsc) => -[|p|p|p|p].
    + match Ch_Init 1; [auto; smt() | done |].
      by auto => />; smt(ge0_cf ge0_cg).
    + match Ch_Blocked1 1; [auto; smt() | done |].
      by auto => />; smt(ge0_cf ge0_cg).
    + match Ch_Wait 1; [auto; smt() | done |].
      auto => />; smt(ge0_cf ge0_cg).
    + match Ch_Blocked2 1; [auto; smt() | done |].
      if => //.
      + sp => //.
        match Left 1; [auto; smt() | done |].
        sp => //.
        exlim (oget (getl (oget lfa))) => -[|p'|p'|p'|p'].
        + match Ch_Init 1; [auto; smt() | done |].
          sp => //.
          match Right 1; [auto; smt() | done |].
          sp => //.
          exlim (oget (getr (oget lke))) => -[|p1|p1|p1|p1].
          + match KE_Init 1; [auto; smt() | done |].
            auto; smt(ge0_cf ge0_cg).
          + match KE_Blocked1 1; [auto; smt() | done |].
            auto => />; smt(ge0_cf ge0_cg).
          + match KE_Wait 1; [auto; smt() | done |].
            auto => />; smt(ge0_cf ge0_cg).
          + match KE_Blocked2 1; [auto; smt() | done |].
            auto => />; smt(ge0_cf ge0_cg).
          match KE_Available 1; [auto; smt() | done |].
          seq 2 : (i =  Left (I, (snd p2, rcv p2, enc (g ^ F.zero) fresh))) time [N 4] => //.
          + instantiate h := (cost_dapply {m2, m3 : unit, r3, r4 : role, p0, p1, p2 : unit pkg, fresh : group, 
                                           p : group pkg, r1, r10 : group pkg stlkg option, r2, r20 : kestate option,
                                           r, r0 : (group pkg stlkg, kestate) sum option, lsc : Top.OTP.FChan.FSC.leakage option, 
                                           m1 : C_OTP.R.step, s : RPi.IDEAL.step, i : SimKEAuth.PARA.Pi12.inputs,
                                           m, m0 : SimKEAuth.PARA.Pi12.ask_backdoor, lke, lfa : SimKEAuth.PARA.Pi12.backdoor option}).
             wp; rnd => />; 1: by rewrite h.
             auto => /> *; rewrite h dmap_ll 1:FDistr.dt_ll /=; smt(ge0_cf ge0_cg).
          by match Left 1; [auto; smt() | done | auto => />].
        + match Ch_Blocked1 1; [auto; smt() | done |].
          auto; smt(ge0_cf ge0_cg).
        + match Ch_Wait 1; [auto; smt() | done |].
          auto; smt(ge0_cf ge0_cg).
        + match Ch_Blocked2 1; [auto; smt() | done |].
          auto; smt(ge0_cf ge0_cg).
        match Ch_Available 1; [auto; smt() | done |].
        auto; smt(ge0_cf ge0_cg).
      auto; smt(ge0_cf ge0_cg).
    match Ch_Available 1; [auto; smt() | done |].
    auto; smt(ge0_cf ge0_cg).
  match Right 1;[auto; smt() | done |].
  inline *.
  exlim m2 => -[] m2i.
  + match Left 1; [auto; smt() | done |].
    sp 1 => //.
    match Left 1; [auto; smt() | done |].
    sp 3 => //.
    match Left 1; [auto; smt() | done|].
    sp => //.
    exlim (oget (getl (oget lfa))) => -[|p'|p'|p'|p'].
    + match Ch_Init 1; [auto; smt() | done |].
      by auto => /=; smt(ge0_cf ge0_cg).
    + by match Ch_Blocked1 1; auto; smt(ge0_cf ge0_cg).
    + by match Ch_Wait 1; auto; smt(ge0_cf ge0_cg).
    + by match Ch_Blocked2 1; auto; smt(ge0_cf ge0_cg).
    match Ch_Available 1; [auto; smt() | done |].
    by call (:true); auto; smt(ge0_cf ge0_cg).
  match Right 1; [auto; smt() | done |].
  seq 1 : true time [N 28; FB.step : 1] => //.
  + by call(:true); auto => />; smt(ge0_cf ge0_cg).
  seq 1 : true time [N 4] => //; last by sp 1 => //; match Right 1; auto.
  exlim (oget lsc) => -[|p'|p'|p'|p'].
  + match Ch_Init 1; auto; smt(ge0_cf ge0_cg).
  + match Ch_Blocked1 1;[auto; smt() | done |].
    sp 1 => //; match Right 1; [auto; smt() | done |].
    sp 4 => //.
    exlim  (oget (getr (oget lke))) =>  -[|p|p|p|p].
    + match KE_Init 1; [auto; smt() | done |].
      sp 1 => //; match Right 1; [auto; smt() | done |].
      by call (:true); auto => />. 
    + by match KE_Blocked1 1; auto; smt(ge0_cf ge0_cg).
    + by match KE_Wait 1; auto; smt(ge0_cf ge0_cg).
    + by match KE_Blocked2 1; auto; smt(ge0_cf ge0_cg).
    by match KE_Available 1; auto; smt(ge0_cf ge0_cg).
  + by match Ch_Wait 1; auto; smt(ge0_cf ge0_cg).
  + match Ch_Blocked2 1; [auto; smt() | done |].
    by sp 1 => //; match Right 1; auto; smt(ge0_cf ge0_cg).
  by match Ch_Available 1; auto; smt(ge0_cf ge0_cg).
+ move=> kb ks FB *.                  
  proc.
  inline *.
  exlim (b) => -[bl|br].     
  + by match Left 2; auto; smt().
  match Right 2; [1: by auto; smt() | 2: done].
  exlim (b2) => -[b2l|b2r].     
  + by match Left 2; auto; smt().
  match Right 2; [1: by auto; smt() | 2: done].
  sp => //.
  seq 1 : true time [ N 22]; 1: done.
  call (:true); auto => * /=; by smt (). 
  by auto => /> /#.
+ move=> Z.
  have -> : 
    Pr[TRANS.H1.REAL.UC_emul(Z, CompRP(OTP, R.PPara(FChan.FAuth.FAuth, COMPOSITION.CompRF(DHKE, HybFChan.F2Auth.F2Auth)))).main() @ &m : res] = 
     Pr[RPi.REAL.UC_emul(Z, CompRP(OTP, R.PPara(FChan.FAuth.FAuth, COMPOSITION.CompRF(DHKE,HybFChan.F2Auth.PARA.PPara(HybFChan.F2Auth.FAuthLR.FAuth, HybFChan.F2Auth.FAuthRL.FAuth))))).main() @ &m : res].
  + by byequiv => //;sim.
  have -> : 
    Pr[TRANS.H1.REAL.UC_emul(Z, TRANS.H1.CompS(CompRF(OTP, FKEAuth), S)).main() @ &m : res] = 
    Pr[RPi.REAL.UC_emul(Z, RPi.CompS(CompRF(OTP, I.PPara(FChan.FAuth.FAuth, FKE)), S)).main() @ &m : res].
  + by byequiv => //; sim.
  by apply (hS Z).
+ move=> Z.
  have -> :
    Pr[TRANS.H2.REAL.UC_emul(Z, CompRF(OTP, FKEAuth)).main() @ &m : res] = 
    Pr[REAL.UC_emul(Z, CompRF(OTP, PARA.PPara(FChan.FAuth.FAuth, FKE))).main() @ &m : res].
  + by byequiv => //; sim.
  have -> : 
    Pr[TRANS.H2.REAL.UC_emul(Z, TRANS.H2.CompS(FSC, OTP_SIM)).main() @ &m : res] = 
    Pr[REAL.UC_emul(Z, CompS(FSC, OTP_SIM)).main() @ &m : res].
  + by byequiv => //; sim.
  by rewrite  -(OTPAdv Z &m).
exists S1 => Z.
have <- : 
  Pr[TRANS.GOAL.REAL.UC_emul(Z, CompRP(OTP, R.PPara(FChan.FAuth.FAuth, COMPOSITION.CompRF(DHKE, HybFChan.F2Auth.F2Auth)))).main() @ &m : res] = 
  Pr[RPi.REAL.UC_emul(Z, CompRP(OTP, R.PPara(FChan.FAuth.FAuth, COMPOSITION.CompRF(DHKE, HybFChan.F2Auth.F2Auth)))).main() @ &m : res].
+ by byequiv=> //; sim.
have <- :
  Pr[TRANS.GOAL.REAL.UC_emul(Z, TRANS.GOAL.CompS(FSC, S1)).main() @ &m : res] =
  Pr[RPi.REAL.UC_emul(Z, TRANS.GOAL.CompS(FSC, S1)).main () @ &m : res].
+ by byequiv => //;sim.
apply (hS1 Z).
qed.

end OTP.
