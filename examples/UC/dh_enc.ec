require import AllCore FMap Distr RndO.
require import Composition.

(* Parties have some sort of identifier *)
type party.

(* 2 party Protocols have roles *)
type role = [ | I | R ].

(* Most protocols will pack data in packages *)
type 'a pkg = party * party * 'a.

op snd (p : 'a pkg) = p.`1.
op rcv (p : 'a pkg) = p.`2.
op pld (p : 'a pkg) = p.`3.

lemma pkgid (p p' : unit pkg): p = (snd p', rcv p', ()) => p = p'
  by elim p; elim p'.


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


require DiffieHellman.
clone DiffieHellman as DH.
import DH.DDH DH.G DH.GP DH.FD DH.GP.ZModE.

clone DH.GP.ZModE.ZModpField as ZPF.

(*  Such statements make no sense when we don't restrict to a
    complexity class 
op adv_ddh : int -> real.

axiom adv_ddh_max cddh :
   forall (A <:DH.DDH.Adversary [ guess : `{N cddh}]) &m,
     `| Pr[DH.DDH.DDH0(A).main() @&m : res] - Pr[DH.DDH.DDH1(A).main() @&m : res] | <= adv_ddh cddh.
*)

theory DHKE.

import DH.DDH.

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

module (DHKE : RHO) (Auth: Pi.REAL.IO) = {

   module Initiator = {
     var p : unit pkg
     var st : istate
     var _X : group
     var _x : exp
     var _K  : group option

     proc init() : unit = {
        p <- witness;
        st <- IInit;
        _x <$ dt;
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
     var _y : exp
     var _K  : group option

     proc init() : unit = {
        p <- witness;
        st <- RWaiting;
        _y <$ dt;
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
  op gen <- dapply (fun x : exp => g^x) dt,
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

     x <$ dt;
     y <$ dt;

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

declare module Z <: REAL.ENV {-DHKE_SIM, -FKE,
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
by auto => /> &2; rewrite expM /= -expM ZPF.mulrC expM.
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
  wp; swap {1} 3 -2; rnd; rnd;  wp; rnd (fun x : exp => g^x) (fun x => loge x).
  auto => />; progress; 1, 4:algebra.
  + by rewrite dmapE /(\o) /pred1; congr; apply fun_ext => z; algebra.
  + by rewrite supp_dmap; exists zL; trivial.
  + by rewrite /init.
  + by rewrite /init.
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

    move => m2 p;inline *; auto => /> &1 &2.
    rewrite /staterel /leak oget_some /unblock /kstp.
    by case (FKE.st{2}.`kst) => /> /#.

(* BACKDOOR *)
+ proc.
  match; first 2 by smt().
  (* Backdoor Rho *)
  + by move => *; inline *;auto => /#.
  (* Backdoor F2Auth *)
  move=> m2 p; inline *; auto => /> &1 &2.
  rewrite /staterel /leak oget_some /unblock /kstp /rcv.
  by case (FKE.st{2}.`kst) => /> /#.

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

end DHKE.

(****************************************************************)
(*                  SECURE CHANNEL BASED ON OTP                 *)
(****************************************************************)

theory OTP.

type msg = group.
type key = group.
type cph = group.

op gen = dapply (fun x : exp => g^x) dt.

op enc(m : msg, k : key) = m * k.
op dec(c : cph, k : key) = c / k.

lemma correctness m k :
   dec (enc m k) k = m.
proof. rewrite /dec /enc -div_def logDr -{2}(expgK m); congr; ring. qed.

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
                            fresh <$ dapply (fun x : exp => g^x) dt;
                            SimKEAuth.FKEAuth.inputs(Left (I, (snd p, rcv p, enc  (g^zero) fresh)));
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
              fresh <$  dapply (fun x : exp => g^x) dt;
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

declare module Z <: REAL.ENV {-FKE, -FSC, -FChan.FAuth.FAuth, -OTP_SIM,
                             -OTP, -DHKE.FKE.FKEAuth.FChan.FAuth.FAuth, -OTPLazy}.

(* To prove that our change of sampling in OTP is sound we use a generic
   eager sampling module *)
local clone import GenEager with
  type from <- unit,
  type to   <- group,
  op sampleto <- fun (x:unit) => dapply (fun (x : exp) => g ^ x) dt
  proof *.
realize sampleto_ll.
proof. by move => _; rewrite /= weight_dmap dt_ll. qed.

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
    + proc => /=; inline *; wp; skip => /> &1 &2; rewrite /party_start /kstp /=.
      progress; smt ().

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
        by apply  dt_ll.
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
    inline *; auto => />; rewrite /is_lossless weight_dmap dt_ll /= => *.
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
have genu : (is_uniform gen); 1: by apply dmap_uni; smt(dt_funi pow_bij).
have genl : (is_lossless gen); 1: by apply dmap_ll; smt(dt_ll).
rewrite !(mu1_uni_ll _ _ genu genl).
move => agen; rewrite agen //=.
have -> // : (a * inv b * c \in gen).
rewrite /gen supp_dmap.
exists ((loge a) - (loge b) + (loge c)); split; 1: by smt(dt_fu).
by rewrite log_bij /= loggK logDr logDrN.
qed.

lemma sup_lem2 (a b c : group):
    a \in gen =>
      a * b * inv c \in gen.
proof.
rewrite /gen //=  => *; rewrite supp_dmap.
exists (loge a + loge b + (loge (inv c))); split; 1: by smt(dt_fu).
by smt(log_bij loggK logDr logDrN).
qed.

lemma enc_lem (a b c : group):
    enc b a = enc c (a * b * inv c).
proof.
rewrite /enc; rewrite log_bij !(Ring.rw_algebra, inv_def); ring.
qed.

lemma aux ['a] (b : bool) (u v : 'a) :
  b => (if b then u else v) = u
by case b.
lemma aux2 ['a] (b : bool) (u v : 'a) :
  !b => (if b then u else v) = v
by case b.

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
  wp; skip => /> &1 &2; rewrite /rcv /= /party_output /invotp /kstp /=;smt (correctness). 

(* Step *)
+ proc;inline *.
  match; first 2 by smt().
  (* STEP RHO *)
  + move => m1 m1_0.
    sp 1 0; if{1}.
    (* STEP INITIATOR *)
    + sp 0 1; match{2}.
      + by rcondf {1} 1; auto => /> &1;rewrite /invotp /kstp; smt().
      + rcondt {1} 1; first by auto => /> &1;rewrite /invotp /kstp; smt().
        by sp 1 0; match{1}; by move => *;rcondf {1} 5; auto => /> &1;rewrite /invotp /kstp;smt().
      + rcondt {1} 1; first by auto => /> &1;rewrite /invotp /kstp;smt().
        by sp 1 0; match{1};  by move => *;rcondf {1} 5; auto => /> &1;rewrite /invotp /kstp;smt().
      + rcondt {2} 1; first by move => *; wp;skip;smt().
        if{1}.
        + seq 0 3 : (#pre /\  (oget (getl (oget lfa{2}))) = Ch_Init);
            first by wp;skip;smt().
          match {2}; last 4 by exfalso; smt().
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

          swap {1} 2 1.
          seq 2 2 : (#pre /\ ={i} /\
                    i{1} = Left (I,  (snd OTP.Initiator.p{1},
                                        rcv OTP.Initiator.p{1},
                                        enc (pld OTP.Initiator.p{1}) fresh{1}))).
          + wp; rnd (fun (fresh1 : group) =>
                       fresh1 * (pld OTP.Initiator.p{1}) * (inv (g ^ zero)))
                    (fun (fresh2 : group) =>
                       fresh2 * (inv (pld OTP.Initiator.p{1})) * (g ^ zero)).

            (* MERGE-COST: old proof *)
            (* by wp;skip;smt(alg_lem1 sup_lem1 sup_lem2 alg_lem2 enc_lem). *)

            (* MERGE-COST: new proof *)
            wp;skip.
            move => />.
            progress.
            smt(alg_lem1 alg_lem2 enc_lem).
            by apply sup_lem1.
            by apply sup_lem2.
            smt(alg_lem1 alg_lem2 enc_lem).
            smt(alg_lem1 alg_lem2 enc_lem).
            smt(alg_lem1 alg_lem2 enc_lem).
            smt(alg_lem1 alg_lem2 enc_lem).
            (* MERGE-COST: end *)

          by wp;skip;rewrite /invotp;smt().
        seq 0 3 : (#pre /\ (oget (getl (oget lfa{2}))) <> Ch_Init);
          first by wp;skip;smt().
        by match {2}; 1: (by exfalso => /#); auto => /#.
      by rcondf{1} 1; [ by auto => /> &1;rewrite /invotp /kstp;smt()| by auto=> />].
    (* STEP RESPONDER *)
    sp 0 1; match{2}; first 3 by auto;rewrite /invotp /#.
    + by rcondf{2} 1; auto; rewrite /invotp /#.
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
by sp 1 0; match; 1,2: (by smt()); auto => />; rewrite /invotp /#.
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

section.

declare module Z <:  C_OTP.RPi.REAL.ENV {-OTP, -FKE, -DHKE.FKE.FKEAuth.FChan.FAuth.FAuth,
                              -DHKE.DHKE_SIM, -DHKE_, -FSC, -FChan.FAuth.FAuth}.

module ZP = CompZR(C_OTP.CompZR(Z, OTP), DHKE.FKE.FKEAuth.FChan.FAuth.FAuth).
module SP = C_OTP.Sid(Sid(DHKE.DHKE_SIM)).

lemma InstOTPAdv &m  (epsilon : real):
   `|Pr[DDH0(DHKE.UC_emul_DDH(ZP, DHKE.CompRFEager(DHKE.DHKE_Eager, DHKE.HybFChan.F2Auth.F2Auth))).main() @ &m : res] -
       Pr[DDH1(DHKE.UC_emul_DDH(ZP, DHKE.CompRFEager(DHKE.DHKE_Eager, DHKE.HybFChan.F2Auth.F2Auth))).main() @ &m : res]| <= epsilon => 
      `| Pr[ C_OTP.RPi.REAL.UC_emul(Z,R_OTP).main() @ &m : res] -
         Pr[ C_OTP.RPi.REAL.UC_emul(Z,C_OTP.RPi.CompS(I_OTP, SP)) .main() @ &m : res] | <= epsilon.
proof.
move => Heps.
have  := compose DHKE.FKE.FKEAuth.FChan.FAuth.FAuth DHKE_ DHKE.FKE.FKE DHKE.DHKE_SIM (C_OTP.CompZR(Z, OTP)) &m.
have  := DHKE.KEAdv ZP &m. 
have -> :
    Pr[FKEWorlds.REAL.UC_emul(ZP, DHKE.COMPOSITION.CompRF(DHKE.DHKE, DHKE.HybFChan.F2Auth.PARA.PPara(DHKE.HybFChan.F2Auth.FAuthLR.FAuth, DHKE.HybFChan.F2Auth.FAuthRL.FAuth))).main
     () @ &m : res] =
   Pr[Pi2.REAL.UC_emul(ZP, DHKE.COMPOSITION.CompRF(DHKE.DHKE, DHKE.HybFChan.F2Auth.PARA.PPara(DHKE.HybFChan.F2Auth.FAuthLR.FAuth, DHKE.HybFChan.F2Auth.FAuthRL.FAuth))).main () @ &m : res].
+ by byequiv => //; sim.
have -> //: Pr[FKEWorlds.REAL.UC_emul(ZP, FKEWorlds.CompS(FKE, DHKE.DHKE_SIM)).main() @ &m : res] = Pr[Pi2.REAL.UC_emul(ZP, Pi2.CompS(FKE, DHKE.DHKE_SIM)).main() @ &m : res].
+ by byequiv => //; sim.
move=> hS1.
have -> : Pr[ C_OTP.RPi.REAL.UC_emul(Z,R_OTP).main() @ &m : res] =
          Pr[ RI.REAL.UC_emul(C_OTP.CompZR(Z, OTP), R.PPara(DHKE.FKE.FKEAuth.FChan.FAuth.FAuth, DHKE_)).main ()
               @ &m : res].
+ byequiv => //.
  proc;inline *.
  wp;call(_: ={glob OTP, glob DHKE.DHKE, glob DHKE.HybFChan.F2Auth.F2Auth,
               glob DHKE.FKE.FKEAuth.FChan.FAuth.FAuth}); first 4 by sim.
  by auto.
have -> : Pr[RPi.REAL.UC_emul(Z, RPi.CompS(I_OTP, C_OTP.Sid(Sid(DHKE.DHKE_SIM)))).main() @ &m : res] =
          Pr[RI.REAL.UC_emul(C_OTP.CompZR(Z, OTP), RI.CompS(I.PPara(DHKE.FKE.FKEAuth.FChan.FAuth.FAuth, FKE), Sid(DHKE.DHKE_SIM))).main() @ &m : res]; last by smt().
          
byequiv => //.
proc;inline *.  
  wp;call(_: ={ DHKE.DHKE_SIM._X, DHKE.DHKE_SIM._Y, glob DHKE.SimAuth.FAuthLR.FAuth, glob DHKE.SimAuth.FAuthRL.FAuth, glob OTP, glob DHKE.FKE.FKEAuth.FChan.FAuth.FAuth, glob FKE});
     first 2 by sim.
  + proc; match; [1,2: by smt()]; move => *;inline *; auto => /> /#.  
  + proc; match; [1,2: by smt()]; move=>  m1 m2;inline *;auto => />.
    move => &2;case m2 => x; smt(). 
    
 by  auto => />.
qed.

end section.

import DHKE.
import FKE.
import FKEAuth.

(****************************************************************)
(*  MAIN THEOREM: ASSUMING 3 AUTHENTICATED COMMUNICATIONS       *)
(*  DHKE + OTP UC REALIZES A ONE-SHOT SECURE CHANNEL.           *)
(****************************************************************)

(* Again, the steps in this proof are all boiler plate; we just apply transitivity.
   We could have equality here, but we need to have a strengthened transitivity lemma for perfect simulators. *)

section.

declare module Z <: RPi.REAL.ENV { -SP, -OTP_SIM, -FKE, -FChan.FAuth.FAuth,-DHKE_SIM, -FSC, -CompRP(OTP,R.PPara(FChan.FAuth.FAuth, COMPOSITION.CompRF(DHKE,HybFChan.F2Auth.F2Auth)))}.

lemma MainTheorem &m eps:
   `|Pr[DDH0(
           UC_emul_DDH(CompZR(C_OTP.CompZR(Z, OTP), FChan.FAuth.FAuth),
             CompRFEager(DHKE_Eager, HybFChan.F2Auth.F2Auth))).main() @ &m :
         res] -
      Pr[DDH1(
           UC_emul_DDH(CompZR(C_OTP.CompZR(Z, OTP), FChan.FAuth.FAuth),
             CompRFEager(DHKE_Eager, HybFChan.F2Auth.F2Auth))).main() @ &m :
         res]| <=
    eps =>
      `| Pr[ RPi.REAL.UC_emul(Z,CompRP(OTP,R.PPara(FChan.FAuth.FAuth, COMPOSITION.CompRF(DHKE,HybFChan.F2Auth.F2Auth)))).main() @ &m : res] -
         Pr[ RPi.REAL.UC_emul(Z,TRANS.GOAL.CompS(FSC, TRANS.SeqS(OTP_SIM, SP))).main() @ &m : res] | <= eps.
proof.
move => Heps.
have hS:= InstOTPAdv Z &m eps Heps.  
have := C_OTP.TRANS.uc_transitivity
      (CompRP(OTP, R.PPara(FChan.FAuth.FAuth, COMPOSITION.CompRF(DHKE, HybFChan.F2Auth.F2Auth))))
      (CompRF(OTP,FKEAuth)) FSC SP OTP_SIM Z &m.
+ have -> :
    Pr[TRANS.H1.REAL.UC_emul(Z, CompRP(OTP, R.PPara(FChan.FAuth.FAuth, COMPOSITION.CompRF(DHKE, HybFChan.F2Auth.F2Auth)))).main() @ &m : res] =
     Pr[RPi.REAL.UC_emul(Z, CompRP(OTP, R.PPara(FChan.FAuth.FAuth, COMPOSITION.CompRF(DHKE,HybFChan.F2Auth.PARA.PPara(HybFChan.F2Auth.FAuthLR.FAuth, HybFChan.F2Auth.FAuthRL.FAuth))))).main() @ &m : res].
  + by byequiv => //;sim.
  have -> :
    Pr[TRANS.H1.REAL.UC_emul(Z, TRANS.H1.CompS(CompRF(OTP, FKEAuth), SP)).main() @ &m : res] =
    Pr[RPi.REAL.UC_emul(Z, RPi.CompS(CompRF(OTP, I.PPara(FChan.FAuth.FAuth, FKE)), SP)).main() @ &m : res].
  + by byequiv => //; sim.
+ have -> :
    Pr[TRANS.H2.REAL.UC_emul(TRANS.CompZS(Z, SP), CompRF(OTP, FKEAuth)).main() @ &m : res] =
    Pr[REAL.UC_emul(TRANS.CompZS(Z, SP), CompRF(OTP, PARA.PPara(FChan.FAuth.FAuth, FKE))).main() @ &m : res].
  + by byequiv => //; sim.
  have -> :
    Pr[TRANS.H2.REAL.UC_emul(TRANS.CompZS(Z, SP), TRANS.H2.CompS(FSC, OTP_SIM)).main() @ &m : res] =
    Pr[REAL.UC_emul(TRANS.CompZS(Z, SP), CompS(FSC, OTP_SIM)).main() @ &m : res].
  by byequiv => //;sim.
have <- :
  Pr[TRANS.GOAL.REAL.UC_emul(Z, CompRP(OTP, R.PPara(FChan.FAuth.FAuth, COMPOSITION.CompRF(DHKE, HybFChan.F2Auth.F2Auth)))).main() @ &m : res] =
  Pr[RPi.REAL.UC_emul(Z, CompRP(OTP, R.PPara(FChan.FAuth.FAuth, COMPOSITION.CompRF(DHKE, HybFChan.F2Auth.F2Auth)))).main() @ &m : res].
+ by byequiv=> //; sim.
have <- :
  Pr[TRANS.GOAL.REAL.UC_emul(Z, TRANS.GOAL.CompS(FSC, TRANS.SeqS(OTP_SIM, SP))).main() @ &m : res] =
  Pr[RPi.REAL.UC_emul(Z, TRANS.GOAL.CompS(FSC, TRANS.SeqS(OTP_SIM, SP))).main () @ &m : res].
+ by byequiv => //;sim.
move : hS.
rewrite  -(OTPAdv (TRANS.CompZS(Z, SP)) &m).
have -> : Pr[RPi.REAL.UC_emul(Z, R_OTP).main() @ &m : res] =
 Pr[TRANS.GOAL.REAL.UC_emul(Z, CompRP(OTP, R.PPara(FChan.FAuth.FAuth, COMPOSITION.CompRF(DHKE, HybFChan.F2Auth.F2Auth)))).main
     () @ &m : res].
+ by byequiv => //;sim.
by smt().
qed.
end section.
end OTP.
