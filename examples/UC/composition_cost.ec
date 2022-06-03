require import AllCore Real Distr.
require import CHoareTactic.
import StdBigop Bigint BIA.

type ('a, 'b) sum = [
  | Left of 'a
  | Right of 'b
].

op getl (s:('a, 'b) sum) = 
  with s = Left a  => Some a
  with s = Right _ => None.

op getr (s:('a, 'b) sum) = 
  with s = Left a  => None
  with s = Right b => Some b.

schema cost_getl ['a 'b] `{P} {s:('a, 'b) sum} : cost[P:getl s] = N 2 + cost[P:s].
schema cost_getr ['a 'b] `{P} {s:('a, 'b) sum} : cost[P:getr s] = N 2 + cost[P:s].
hint simplify cost_getl, cost_getr.

op smap (fa:'a -> 'c) (fb:'b -> 'd) (s: ('a, 'b) sum) = 
  with s = Left a  => Left (fa a)
  with s = Right b => Right (fb b).

schema cost_obind_getr ['a 'b] `{P} {e : ('a,'b)sum option}: 
  cost[P : obind getr e] = cost[P : e] + N 3.
hint simplify cost_obind_getr.

schema cost_obind_getl ['a 'b] `{P} {e : ('a,'b)sum option}: 
  cost[P : obind getl e] = cost[P : e] + N 3.
hint simplify cost_obind_getl.

schema cost_omap_Left ['a 'b] `{P} {e : 'a option}:
  cost[P : omap (Left<:'a,'b>) e] = cost[P:e] + N 2.
hint simplify cost_omap_Left.

schema cost_omap_Right ['a 'b] `{P} {e : 'b option}:
  cost[P : omap (Right<:'a,'b>) e] = cost[P:e] + N 2.
hint simplify cost_omap_Right.

schema cost_Left ['a 'b] `{P} {e:'a}:
  cost[P: Left<:'a, 'b> e] = cost [P: e] + N 1.

schema cost_Right ['a 'b] `{P} {e:'b}:
  cost[P: Right<:'a, 'b> e] = cost [P: e] + N 1.
hint simplify cost_Left.
hint simplify cost_Right.

type cenv = {
  cd    : int; (* self complexity of the distinguisher *)
  ci    : int; (* number of call to inputs             *)
  co    : int; (* number of call to outputs            *)
  cs    : int; (* number of call to step               *)
  cb    : int; (* number of call to backdoor           *)
}.
  
op cenv_pos (c:cenv) = 
   0 <= c.`cd /\
   0 <= c.`ci /\
   0 <= c.`co /\
   0 <= c.`cs /\
   0 <= c.`cb.

type cprot = {
  cpinit     : int;
  cpinputs   : int;
  cpoutputs  : int;
  cpstep     : int;
  cpbackdoor : int;
}.

op cprot_pos (cp:cprot) = 
  0 <= cp.`cpinit     /\
  0 <= cp.`cpinputs   /\
  0 <= cp.`cpoutputs  /\
  0 <= cp.`cpstep     /\
  0 <= cp.`cpbackdoor.

abstract theory ProtocolType.

(*
     
exists S, forall Z

We take the formalisation using dummy adversary 
      ------------------------      ------------------------
      |       Z              |      |       Z              |
      ------------------|    |      ------------------|    |
            : I/O       |    |            : I/O       |    |
      |-------------|   |    |      |-------------|   |    |
      |     P       |   |    |      |     P'      |   |    |
      |             |   |    |      |   |---------|   |    |
      |             | - |    |      |   |     : L     |    |
      |             | M |    |      |   | |-------|   |    |
      |             |   |    |      |   | |   S   | - |    |
      |-------------|   |----|      |-- | |-------| M |----|

Z communicates with P/P' and S 
P' (can also be a functionality F) communicates with S

*)
      
type inputs.         (* Z can send inputs to P/F *)
type ask_outputs.    (* Z can ask outputs to P/F *)
type outputs.        

type step.           (* Z can ask to do step *)
type ask_backdoor.   (* Z can ask backdoors to P/S, S can ask backdoors to F*)
type backdoor.

end ProtocolType.

abstract theory EXEC_MODEL.

clone include ProtocolType.

module type IO = {
  proc inputs (i:inputs) : unit
  proc outputs(o:ask_outputs) : outputs option
}.

module type BACKDOORS = {
  proc step (m:step) : unit
  proc backdoor (m:ask_backdoor) : backdoor option
}.

module type E_INTERFACE = {
  include IO
  include BACKDOORS
}.

module type PROTOCOL = {
  proc init() : unit
  include E_INTERFACE
}.

module type ENV (I:E_INTERFACE) = {
  proc distinguish () : bool
}.

module UC_emul (E:ENV) (P:PROTOCOL) = {
  proc main() = {
    var b;
    P.init();
    b <@ E(P).distinguish();
    return b;
  }
}.

abstract theory C.

  op c : cenv.

  axiom c_pos : cenv_pos c.

  module type CENV (I : E_INTERFACE) = {
    proc distinguish() : bool `{N c.`cd, I.inputs:c.`ci, I.outputs:c.`co, I.step:c.`cs, I.backdoor:c.`cb}
  }.

end C.

abstract theory CP.

  op cp : cprot.

  axiom cp_pos : cprot_pos cp.

  module type CPROTOCOL  = {
    proc init() : unit `{N cp.`cpinit}
    
    proc inputs(i : inputs) : unit `{N cp.`cpinputs}
    
    proc outputs(o : ask_outputs) : outputs option `{N cp.`cpoutputs}
    
    proc step(m : step) : unit `{N cp.`cpstep}
    
    proc backdoor(m : ask_backdoor) : backdoor option `{N cp.`cpbackdoor}
  }.

end CP.

end EXEC_MODEL.

type csim = {
  cinit : int;
  cstep : int;
  cs_s  : int;
  cs_b  : int;
  cbackdoor : int;
  cb_s  : int;
  cb_b  : int;
}.

op csim_pos (c:csim) = 
  0 <= c.`cinit /\
  0 <= c.`cstep /\
  0 <= c.`cs_s  /\ 
  0 <= c.`cs_b  /\ 
  0 <= c.`cbackdoor /\ 
  0 <= c.`cb_s  /\
  0 <= c.`cb_b.

abstract theory REAL_IDEAL.

  clone EXEC_MODEL as REAL.
  clone EXEC_MODEL as IDEAL with
    type inputs      <- REAL.inputs,
    type ask_outputs <- REAL.ask_outputs,
    type outputs     <- REAL.outputs.        

  module type SIMULATOR (FB:IDEAL.BACKDOORS) = {
    proc init() : unit {}
    include REAL.BACKDOORS
  }.

  (* Compose a functionality with a simulator --> protocol *)

  module CompS(F:IDEAL.PROTOCOL, S:SIMULATOR) : REAL.PROTOCOL = {
    proc init() = {
      F.init();
      S(F).init();
    }
    include F [ inputs, outputs]
    include S(F) [step, backdoor]
  }.

  abstract theory C.
    clone include REAL.C.

    op csi : csim.
    axiom csi_pos : csim_pos csi.

    module type CSIMULATOR (FB:IDEAL.BACKDOORS) = {
      proc init() : unit {} `{N csi.`cinit}
      proc step(m : REAL.step) : unit `{N csi.`cstep, FB.step:csi.`cs_s, FB.backdoor:csi.`cs_b}
      proc backdoor(m : REAL.ask_backdoor) : REAL.backdoor option `{N csi.`cbackdoor, FB.step:csi.`cb_s, FB.backdoor:csi.`cb_b}
    }.

  end C.

end REAL_IDEAL.

abstract theory NON_DUMMY.

  clone REAL_IDEAL as RI.

  (* We put the non-dummy adversary inside the protocol. *)

  type step_A.
  type ask_A.
  type get_A.

  clone REAL_IDEAL as NONDUMMY_RI with
    type REAL.inputs        <- RI.REAL.inputs,
    type REAL.ask_outputs   <- RI.REAL.ask_outputs,
    type REAL.outputs       <- RI.REAL.outputs,
    type REAL.step          <- step_A,
    type REAL.ask_backdoor  <- ask_A, 
    type REAL.backdoor      <- get_A,
    type IDEAL.step         <- RI.IDEAL.step,
    type IDEAL.ask_backdoor <- RI.IDEAL.ask_backdoor,
    type IDEAL.backdoor     <- RI.IDEAL.backdoor.

  (* A Can't have an init, which seems fine *)
  module type ADV(B : RI.REAL.BACKDOORS) = { 
     include NONDUMMY_RI.REAL.BACKDOORS
  }.

  module A_PROTOCOL(A : ADV, P : RI.REAL.PROTOCOL) : NONDUMMY_RI.REAL.PROTOCOL = {
     proc init() : unit = {
         P.init();
     }
     include P [inputs, outputs]
     include A(P) [step,backdoor]
  }.

(*  
  module P : DUMMY_RI.REAL.PROTOCOL.
  module F : DUMMY_RI.IDEAL.PROTOCOL.

  op eps : real.

  axiom security : 
    exists (S<: NONDUMMY_RI.SIMULATOR),
       forall (Z<: NONDUMMY_RI.REAL.ENV),
         `| Pr[NONDUMMY_RI.REAL.UC_emul(Z,A_PROTOCOL(A,P)).main() @ &m : res] -
            Pr[NONDUMMY_RI.REAL.UC_emul(Z,NONDUMMY_RI.CompS(F,S)).main() @ &m : res] | <= eps.
*)

end NON_DUMMY.

theory NONDUMMY_EQUIV_DUMMY.

  clone import NON_DUMMY as NON_DUMMY.
  
  type cadv = {
    cas   : int;
    cas_s : int;
    cas_b : int;
    cab   : int;
    cab_s : int;
    cab_b : int
  }.

  op cadv_pos cA = 
    0 <= cA.`cas   /\
    0 <= cA.`cas_s /\
    0 <= cA.`cas_b /\
    0 <= cA.`cab   /\
    0 <= cA.`cab_s /\
    0 <= cA.`cab_b.
  
   module (SeqSA(A:ADV, S:RI.SIMULATOR): NONDUMMY_RI.SIMULATOR) (B:NONDUMMY_RI.IDEAL.BACKDOORS) = {
     proc init () = {
       S(B).init();
     }

     include A(S(B))
  }.

  module SeqZA(Z:NONDUMMY_RI.REAL.ENV) (A:ADV) (I: RI.REAL.E_INTERFACE) = { 
    module IA = {
      proc inputs  = I.inputs
      proc outputs = I.outputs
      proc step    = A(I).step
      proc backdoor = A(I).backdoor
    }
    proc distinguish = Z(IA).distinguish
  }.

  op csa (cA:cadv) (cS:csim) = {|
    cinit = cS.`cinit;
    cstep = cA.`cas + cS.`cstep * cA.`cas_s + cS.`cbackdoor * cA.`cas_b;
    cs_s  = cS.`cs_s * cA.`cas_s + cS.`cb_s * cA.`cas_b;
    cs_b  = cS.`cs_b * cA.`cas_s + cS.`cb_b * cA.`cas_b;
    cbackdoor =  cA.`cab + cS.`cstep * cA.`cab_s + cS.`cbackdoor * cA.`cab_b;
    cb_s  = cS.`cs_s * cA.`cab_s + cS.`cb_s * cA.`cab_b;
    cb_b  = cS.`cs_b * cA.`cab_s + cS.`cb_b * cA.`cab_b;
  |}.

  lemma dummy_nondummy (P<:RI.REAL.PROTOCOL) (F<:RI.IDEAL.PROTOCOL) &m eps (cS: csim) :
    csim_pos cS => 
    forall (S<: RI.SIMULATOR
                 [init : `{N cS.`cinit} {},
                  step : `{N cS.`cstep, #FB.step : cS.`cs_s, #FB.backdoor : cS.`cs_b},
                  backdoor : `{N cS.`cbackdoor, #FB.step: cS.`cb_s, #FB.backdoor : cS.`cb_b}]
                 {-F}),
      (forall (Z<: RI.REAL.ENV {-P,-F,-S}),
        `| Pr[RI.REAL.UC_emul(Z,P).main() @ &m : res] -
           Pr[RI.REAL.UC_emul(Z,RI.CompS(F,S)).main() @ &m : res] | <= eps) =>

    forall (cA:cadv) (A<:ADV [step : `{N cA.`cas, #B.step: cA.`cas_s, #B.backdoor: cA.`cas_b},
                              backdoor : `{N cA.`cab, #B.step: cA.`cab_s, #B.backdoor: cA.`cab_b}]
                              {-F, -P, -S}),
     cadv_pos cA =>                       
     let csa = csa cA cS in
     exists (S1<: NONDUMMY_RI.SIMULATOR 
                  [init : `{N csa.`cinit} {},
                   step : `{N csa.`cstep, #FB.step : csa.`cs_s, #FB.backdoor : csa.`cs_b},
                   backdoor : `{N csa.`cbackdoor, #FB.step: csa.`cb_s, #FB.backdoor : csa.`cb_b}]
                  {+S, + A, -F}), (* Remark the -F, is redoundant since S and A cannot use it *)
      forall (Z<: NONDUMMY_RI.REAL.ENV {-A, -P, -F, -S1}),
        `| Pr[NONDUMMY_RI.REAL.UC_emul(Z,A_PROTOCOL(A,P)).main() @ &m : res] -
           Pr[NONDUMMY_RI.REAL.UC_emul(Z,NONDUMMY_RI.CompS(F,S1)).main() @ &m : res] | <= eps.
  proof.
    move=> hcS S hS cA A hcA csa.
    exists (SeqSA(A,S)); split.
    + (split; last split) => kb ks FB hkb hks.
      + by proc; call (:true; time []); skip => /= /#. 
      + move=> /=; proc true : time 
              [S(FB).step : [N (cS.`cstep + ks * cS.`cs_s + kb * cS.`cs_b)],
               S(FB).backdoor : [N (cS.`cbackdoor + ks * cS.`cb_s + kb * cS.`cb_b)]] => //=.
        + by rewrite !bigi_constz /#. 
        + move=> ???.
          proc true : time [FB.step : [N ks],
                            FB.backdoor : [N kb]] => //=.
          + by rewrite !bigi_constz /#.
          + by move=> ???;proc true : time [].
          by move=> ???;proc true : time [].
        move=> ???.
        proc true : time [FB.step : [N ks],
                          FB.backdoor : [N kb]] => //=.
        + by rewrite !bigi_constz /#.
        + by move=> ???;proc true : time [].
        by move=> ???;proc true : time [].
      move=> /=; proc true : time 
              [S(FB).step : [N (cS.`cstep + ks * cS.`cs_s + kb * cS.`cs_b)],
               S(FB).backdoor : [N (cS.`cbackdoor + ks * cS.`cb_s + kb * cS.`cb_b)]] => //=.
      + by rewrite !bigi_constz /#. 
      + move=> ???.
        proc true : time [FB.step : [N ks],
                          FB.backdoor : [N kb]] => //=.
        + by rewrite !bigi_constz /#.
        + by move=> ???;proc true : time [].
        by move=> ???;proc true : time [].
      move=> ???.
      proc true : time [FB.step : [N ks],
                        FB.backdoor : [N kb]] => //=.
      + by rewrite !bigi_constz /#.
      + by move=> ???;proc true : time [].
      by move=> ???;proc true : time [].
    move=> Z.
    have := hS (SeqZA(Z,A)).
    have -> : Pr[RI.REAL.UC_emul(SeqZA(Z, A), P).main() @ &m : res] = 
              Pr[NONDUMMY_RI.REAL.UC_emul(Z, A_PROTOCOL(A, P)).main() @ &m : res].
    + by byequiv => //; proc; inline *; sim.
    have -> // : Pr[RI.REAL.UC_emul(SeqZA(Z, A), RI.CompS(F, S)).main() @ &m : res] = 
                 Pr[NONDUMMY_RI.REAL.UC_emul(Z, NONDUMMY_RI.CompS(F, SeqSA(A, S))).main() @ &m : res].
    by byequiv => //; proc; inline *; sim.
  qed.

  theory NONDUMMY_DUMMY.

  clone import NON_DUMMY as ASSUMPTION1 with
      type step_A = RI.REAL.step,
      type ask_A  = RI.REAL.ask_backdoor,
      type get_A  = RI.REAL.backdoor.

  module (DUMMY_A : ADV) (B :RI.REAL.BACKDOORS)  = {
     proc step(s : RI.REAL.step) : unit = {
        B.step(s);
     }

     proc backdoor(b : RI.REAL.ask_backdoor) : RI.REAL.backdoor option = {
        var l;
        l <@ B.backdoor(b);
        return l;
     }
  }.

  (* A module with no exported procedure, this is used to encode any set of variable *)
  module type MEM = { }.

  lemma nondummy_dummy (P<:RI.REAL.PROTOCOL) (F<:RI.IDEAL.PROTOCOL) &m eps (cS: cadv -> csim) (Mem <: MEM):
    (forall cA, cadv_pos cA => csim_pos (cS cA)) => 
    (forall (cA:cadv) (A<:ADV [step : `{N cA.`cas, #B.step: cA.`cas_s, #B.backdoor: cA.`cas_b},
                     backdoor : `{N cA.`cab, #B.step: cA.`cab_s, #B.backdoor: cA.`cab_b} ]),
     let csa = cS cA in
     exists (S<: NONDUMMY_RI.SIMULATOR 
                  [init : `{N csa.`cinit} {},
                   step : `{N csa.`cstep, #FB.step : csa.`cs_s, #FB.backdoor : csa.`cs_b},
                   backdoor : `{N csa.`cbackdoor, #FB.step: csa.`cb_s, #FB.backdoor : csa.`cb_b}]
                  {+Mem, -F}),
      forall (Z<: NONDUMMY_RI.REAL.ENV {-A, -P, -F, -S}),
        `| Pr[NONDUMMY_RI.REAL.UC_emul(Z,A_PROTOCOL(A,P)).main() @ &m : res] -
           Pr[NONDUMMY_RI.REAL.UC_emul(Z,NONDUMMY_RI.CompS(F,S)).main() @ &m : res] | <= eps) =>
    let cdA = {| cas = 0; cas_s = 1; cas_b = 0; cab = 0; cab_s = 0; cab_b = 1 |} in
    let csd = cS cdA in
    (exists (S<: RI.SIMULATOR
                 [init : `{N csd.`cinit} {},
                  step : `{N csd.`cstep, #FB.step : csd.`cs_s, #FB.backdoor : csd.`cs_b},
                  backdoor : `{N csd.`cbackdoor, #FB.step: csd.`cb_s, #FB.backdoor : csd.`cb_b}]
                 {+Mem, -F}),
      forall (Z<: RI.REAL.ENV {-P,-F,-S}),
        `| Pr[RI.REAL.UC_emul(Z,P).main() @ &m : res] -
           Pr[RI.REAL.UC_emul(Z,RI.CompS(F,S)).main() @ &m : res] | <= eps).
  proof.
    move=> hcS hA cdA csd.  
    have /= [S hS]:= hA cdA (<:DUMMY_A) _ _.     
    + by move=> kBb kBs B ??; proc; call(:true; time []); auto.
    + by move=> kBb kBs B ??; proc; call(:true; time []); auto.
    exists S; split.
    + (split; last split) => kBb kBs FB ??.
      + by proc true : time []. 
      + proc true : time [FB.step : [N kBs],FB.backdoor :[N kBb]] => //=.
        + have cS_pos := hcS cdA _; 1: done.
          by rewrite !bigi_constz /#. 
        + by move=> *; proc true : time [].
        by move=> *; proc true : time [].
      proc true : time [FB.step : [N kBs],FB.backdoor :[N kBb]] => //=.
      + have cS_pos := hcS cdA _; 1: done.
        by rewrite !bigi_constz /#. 
      + by move=> *; proc true : time [].
      by move=> *; proc true : time [].                 
    move=> Z; have := hS Z. 
    have -> : Pr[NONDUMMY_RI.REAL.UC_emul(Z, A_PROTOCOL(DUMMY_A, P)).main() @ &m : res] = 
              Pr[RI.REAL.UC_emul(Z, P).main() @ &m : res].
    + byequiv => //; last by move=> ?? ->.
      proc; call (_: ={glob P}).
      + by proc *; inline *; call (:true).
      + by proc *; inline *; call (:true).
      + by proc *; inline *; call (:true); auto.
      + by proc *; inline *; wp; call (:true); auto.
      by inline *; call(:true); auto => /> ?? 4!->.
    have -> // : Pr[NONDUMMY_RI.REAL.UC_emul(Z, NONDUMMY_RI.CompS(F, S)).main() @ &m : res] =
              Pr[RI.REAL.UC_emul(Z, RI.CompS(F, S)).main() @ &m : res].
    byequiv => //; last by move=> ?? ->.
    proc; call (_: ={glob F, glob S}).
    + by proc *; inline *; call (:true).
    + by proc *; inline *; call (:true).
    + by proc *; inline *; call (: ={glob F}); auto; proc true.
    + by proc *; inline *; call (: ={glob F}); auto; proc true.
    by inline *; call(: ={glob F}); call(: true); auto => /> ?? 6!->.
  qed.

  end NONDUMMY_DUMMY.

end NONDUMMY_EQUIV_DUMMY.

abstract theory TRANSITIVITY.

  (* H1 := P2 realizes P1 /\ H2 := P3 realizes P2 => P3 realizes P1 *)

  clone REAL_IDEAL as H1.

  clone REAL_IDEAL as H2 with
    type REAL.inputs       <- H1.REAL.inputs,
    type REAL.ask_outputs  <- H1.REAL.ask_outputs,
    type REAL.outputs      <- H1.REAL.outputs,
    type REAL.step         <- H1.IDEAL.step,
    type REAL.ask_backdoor <- H1.IDEAL.ask_backdoor, 
    type REAL.backdoor     <- H1.IDEAL.backdoor.

  clone REAL_IDEAL as GOAL with
    type REAL.inputs       <- H1.REAL.inputs,
    type REAL.ask_outputs  <- H1.REAL.ask_outputs,
    type REAL.outputs      <- H1.REAL.outputs,
    type REAL.step         <- H1.REAL.step,
    type REAL.ask_backdoor <- H1.REAL.ask_backdoor, 
    type REAL.backdoor     <- H1.REAL.backdoor,
    type IDEAL.step         <- H2.IDEAL.step,
    type IDEAL.ask_backdoor <- H2.IDEAL.ask_backdoor, 
    type IDEAL.backdoor     <- H2.IDEAL.backdoor.

   module (SeqS(S1:H2.SIMULATOR, S2:H1.SIMULATOR): GOAL.SIMULATOR) (FB:GOAL.IDEAL.BACKDOORS) = {
     proc init () = {
       S1(FB).init();
       S2(S1(FB)).init();
     }

     include S2(S1(FB)) [-init] 
   }.

  module (CompZS(Z:GOAL.REAL.ENV)(S:H1.SIMULATOR) : H2.REAL.ENV) (I:H2.REAL.E_INTERFACE) = {
    module IZ = {
      include I [inputs, outputs]
      include S(I) 
    }

    proc distinguish() = {
      var b;
      IZ.init();
      b <@ Z(IZ).distinguish();
      return b;
    }
    
  }.

  section TRANS.
     declare module P1 <: GOAL.REAL.PROTOCOL.
     declare module P2 <: H1.IDEAL.PROTOCOL.
     declare module P3 <: H2.IDEAL.PROTOCOL.
     declare module S12 <: H1.SIMULATOR {-P2, -P3}.
     declare module S23 <: H2.SIMULATOR {-P3, -S12}.
  
     declare module Z <: GOAL.REAL.ENV { -P1, -P2, -P3, -S12, -S23}.
 
     lemma uc_transitivity &m : 
       `| Pr[GOAL.REAL.UC_emul(Z, P1).main() @ &m : res] - 
          Pr[GOAL.REAL.UC_emul(Z, GOAL.CompS(P3, SeqS(S23, S12))).main() @ &m : res] | <= 
       `| Pr[  H1.REAL.UC_emul(Z, P1).main() @ &m : res] - 
          Pr[  H1.REAL.UC_emul(Z, H1.CompS(P2, S12)).main() @ &m : res] | + 
       `| Pr[  H2.REAL.UC_emul(CompZS(Z,S12),P2).main() @ &m : res] - 
          Pr[  H2.REAL.UC_emul(CompZS(Z,S12),H2.CompS(P3, S23)).main() @ &m : res] |.
     proof.
      have -> : Pr[GOAL.REAL.UC_emul(Z,P1).main() @ &m : res] = Pr[H1.REAL.UC_emul(Z,P1).main() @ &m : res].
      + by byequiv => //; sim.
      have -> : 
        Pr[H1.REAL.UC_emul(Z, H1.CompS(P2, S12)).main() @ &m : res] = 
        Pr[H2.REAL.UC_emul(CompZS(Z,S12),P2).main() @ &m : res].
      + by byequiv => //; proc; inline *; wp; sim.
      have -> /#: 
        Pr[GOAL.REAL.UC_emul(Z, GOAL.CompS(P3, SeqS(S23, S12))).main() @ &m : res] = 
        Pr[H2.REAL.UC_emul(CompZS(Z, S12), H2.CompS(P3, S23)).main() @ &m : res].
      by byequiv => //; proc; inline *; wp; sim. 
    qed.

   end section TRANS.

   abstract theory C.

   op cz   : cenv.
   op cs12 : csim.
   op cs23 : csim.

   axiom cz_pos   : cenv_pos cz.
   axiom cs12_pos : csim_pos cs12.
   axiom cs23_pos : csim_pos cs23.

   op cz23 = {|
     cd = cz.`cd + cs12.`cinit + cz.`cs * cs12.`cstep + cz.`cb * cs12.`cbackdoor; 
     ci = cz.`ci;
     co = cz.`co;
     cs = cz.`cs * cs12.`cs_s + cz.`cb * cs12.`cb_s;
     cb = cz.`cs * cs12.`cs_b + cz.`cb * cs12.`cb_b;
   |}.

   op cs13 = {| 
       cinit = cs12.`cinit + cs23.`cinit;
       cstep = cs12.`cstep + cs23.`cstep * cs12.`cs_s + cs23.`cbackdoor * cs12.`cs_b;
       cs_s  = cs12.`cs_s * cs23.`cs_s + cs12.`cs_b * cs23.`cb_s;
       cs_b  = cs12.`cs_s * cs23.`cs_b + cs12.`cs_b * cs23.`cb_b;
       cbackdoor = cs12.`cbackdoor + cs23.`cstep * cs12.`cb_s + cs23.`cbackdoor * cs12.`cb_b;
       cb_s  = cs12.`cb_s * cs23.`cs_s + cs12.`cb_b * cs23.`cb_s;
       cb_b  = cs12.`cb_s * cs23.`cs_b + cs12.`cb_b * cs23.`cb_b;
     |}.

   clone H1.C as CH1 with
     op c <- cz,
     op csi <- cs12
     proof * by smt(cz_pos cs12_pos cs23_pos).
   
   clone H2.C as CH2 with 
     op c <- cz23,
     op csi <- cs23
     proof * by smt(cz_pos cs12_pos cs23_pos).

   clone GOAL.C as CGOAL with
     op c <- cz,
     op csi <- cs13 
     proof * by smt (cz_pos cs12_pos cs23_pos).

   section.

   declare module P1  <: GOAL.REAL.PROTOCOL.
   declare module P2  <: H1.IDEAL.PROTOCOL.
   declare module P3  <: H2.IDEAL.PROTOCOL.
   declare module S12 <: CH1.CSIMULATOR {-P2, -P3}.
   declare module S23 <: CH2.CSIMULATOR {-P3, -S12}.

   lemma cost_S23_step (kbackdoor kstep : int) (FB <: GOAL.IDEAL.BACKDOORS[backdoor : `{N kbackdoor} , step : `{N kstep} ]) :
     choare[S23(FB).step] time [N cs23.`cstep; FB.step : cs23.`cs_s; FB.backdoor : cs23.`cs_b].
   proof.
     proc true : time [FB.step : [N kstep], FB.backdoor : [N kbackdoor]] => //=.
     + by rewrite !bigi_constz; smt(cs23_pos). 
     + by move=> /= *; proc true : time [].
     by move=> /= *; proc true : time [].
   qed.

   lemma cost_S23_backdoor (kbackdoor kstep : int) (FB <: GOAL.IDEAL.BACKDOORS[backdoor : `{N kbackdoor} , step : `{N kstep} ]) :
       choare[S23(FB).backdoor] time [N cs23.`cbackdoor; FB.step : cs23.`cb_s; FB.backdoor : cs23.`cb_b].
   proof.
     proc true : time [FB.step : [N kstep], FB.backdoor : [N kbackdoor]] => //=.
     + by rewrite !bigi_constz; smt(cs23_pos). 
     + by move=> /= *; proc true : time [].
     by move=> /= *; proc true : time [].
   qed.

   lemma cost_SeqS_init (FB <: GOAL.IDEAL.BACKDOORS):
      choare[SeqS(S23, S12, FB).init] time [N cs13.`cinit].
   proof. proc; call(:true);call(:true);skip => /#. qed.
  
   lemma cost_SeqS_step (kbackdoor kstep : int) (FB <: GOAL.IDEAL.BACKDOORS[backdoor : `{N kbackdoor} , step : `{N kstep} ]): 
      choare[S12(S23(FB)).step] time [N cs13.`cstep; FB.step : cs13.`cs_s; FB.backdoor : cs13.`cs_b].
   proof.
     proc true: time [S23(FB).step: [N cs23.`cstep; FB.step: cs23.`cs_s; FB.backdoor: cs23.`cs_b],
                      S23(FB).backdoor: [N cs23.`cbackdoor; FB.step: cs23.`cb_s; FB.backdoor: cs23.`cb_b]] => //=.
     + by rewrite !bigi_constz; smt(cs12_pos).
     + by move=> ???; apply (cost_S23_step kbackdoor kstep FB).
     by move=> ???; apply (cost_S23_backdoor kbackdoor kstep FB).
   qed.

   lemma cost_SeqS_backdoor (kbackdoor kstep : int) (FB <: GOAL.IDEAL.BACKDOORS[backdoor : `{N kbackdoor} , step : `{N kstep} ]): 
      choare[S12(S23(FB)).backdoor] time [N cs13.`cbackdoor; FB.step : cs13.`cb_s; FB.backdoor : cs13.`cb_b].
   proof.
     proc true: time [S23(FB).step: [N cs23.`cstep; FB.step: cs23.`cs_s; FB.backdoor: cs23.`cs_b],
                      S23(FB).backdoor: [N cs23.`cbackdoor; FB.step: cs23.`cb_s; FB.backdoor: cs23.`cb_b]] => //=.
     + by rewrite !bigi_constz; smt(cs12_pos). 
     + move=> *; apply (cost_S23_step kbackdoor kstep FB).
     by move=> *; apply (cost_S23_backdoor kbackdoor kstep FB).
   qed. 

   lemma ex_uc_transitivity &m (e1 e2:real):
      (forall (Z<:CH1.CENV{-P1, -P2, -S12, -P3, -S23}),
          `| Pr[H1.REAL.UC_emul(Z,P1).main() @ &m : res] - 
             Pr[H1.REAL.UC_emul(Z,H1.CompS(P2, S12)).main() @ &m : res] | <= e1) =>
      (forall (Z<:CH2.CENV{-P2,-P3,-S23, -P1}),
          `| Pr[H2.REAL.UC_emul(Z,P2).main() @ &m : res] - 
             Pr[H2.REAL.UC_emul(Z,H2.CompS(P3, S23)).main() @ &m : res] | <= e2) =>
      (exists (S13<:CGOAL.CSIMULATOR {+S12,+S23, -P3}),
        forall (Z<:CGOAL.CENV{-P1,-P2,-P3,-S12,-S23}),
          `| Pr[GOAL.REAL.UC_emul(Z,P1).main() @ &m : res] - 
             Pr[GOAL.REAL.UC_emul(Z,GOAL.CompS(P3, S13)).main() @ &m : res] | <= e1 + e2).
   proof.
     move=> hS12 hS23. 
     exists (SeqS(S23, S12)) => /=. 
     split.
     + split.
       + by move=> k1 k2 FB *; apply (cost_SeqS_init FB). 
       split.
       + by move=> k1 k2 FB *; apply (cost_SeqS_step k1 k2 FB).
       by move=> k1 k2 FB *; apply (cost_SeqS_backdoor k1 k2 FB).
     move=> Z.
     have := uc_transitivity P1 P2 P3 S12 S23 Z &m.
     have := hS12 Z. 
     have /# := hS23 (CompZS(Z,S12)) _.
     move=> kb ks ko ki I ????.
     proc; inline *.
     call (_:true; time [CompZS(Z, S12, I).IZ.inputs:['0; I.inputs: 1],
                         CompZS(Z, S12, I).IZ.outputs:['0; I.outputs: 1],
                         CompZS(Z, S12, I).IZ.step:
                                 [             N cs12.`cstep; 
                                  I.step     : cs12.`cs_s; 
                                  I.backdoor : cs12.`cs_b],
                         CompZS(Z, S12, I).IZ.backdoor:
                                 [             N cs12.`cbackdoor; 
                                  I.step     : cs12.`cb_s; 
                                  I.backdoor : cs12.`cb_b]]).
     + by move=> /= *; proc true : time []. 
     + by move=> /= *; proc true : time [].
     + move=> * /=.
       proc true: time [I.step :[N ks], I.backdoor : [N kb]] => //.
       + by rewrite !bigi_constz; smt(cs12_pos).
       + by move=> /= *; proc true : time [].
       by move=> /= *; proc true : time []. 
     + move=> * /=.
       proc true: time [I.step :[N ks], I.backdoor : [N kb]] => //.
       + by rewrite !bigi_constz; smt(cs12_pos).
       + by move=> /= *; proc true : time [].
       by move=> /= *; proc true : time []. 
     call (:true); skip => /=.
     by rewrite !big1_eq /= !bigi_constz /=;smt(cz_pos).
   qed.

  end section.

  end C.

end TRANSITIVITY.

theory COMPOSITION.

  (* Pi realizes f => R^Pi realizes R^f 
      
  ____IO___
  |    ____|    
  | R  |_f_| - backdoor
  |________| - backdoor *)

  clone REAL_IDEAL as Pi.

  clone EXEC_MODEL as R.

  clone REAL_IDEAL as RPi with
    type REAL.inputs       <- R.inputs,
    type REAL.ask_outputs  <- R.ask_outputs,
    type REAL.outputs      <- R.outputs,  
    type REAL.step         = (R.step, Pi.REAL.step) sum,
    type REAL.ask_backdoor = (R.ask_backdoor, Pi.REAL.ask_backdoor) sum,
    type REAL.backdoor     = (R.backdoor, Pi.REAL.backdoor) sum,
    type IDEAL.step         = (R.step, Pi.IDEAL.step) sum,
    type IDEAL.ask_backdoor = (R.ask_backdoor, Pi.IDEAL.ask_backdoor) sum,
    type IDEAL.backdoor     = (R.backdoor, Pi.IDEAL.backdoor) sum.

  module type RHO (P:Pi.REAL.IO) = {
    proc init() : unit {}
    include R.PROTOCOL [-init]
  }.

  module CompR_I(Rho:RHO) (P:Pi.REAL.E_INTERFACE) : RPi.REAL.E_INTERFACE = {

    include Rho(P) [inputs, outputs]

    proc step (m:RPi.REAL.step) : unit = {
      match (m) with
      | Left  m1 => { Rho(P).step(m1); }
      | Right m2 => { P.step(m2); }
      end;
    }

    proc backdoor (m:RPi.REAL.ask_backdoor) : RPi.REAL.backdoor option = {
      var r1, r2, r;
      match (m) with
      | Left m1  => { r1 <@ Rho(P).backdoor(m1); r <- omap Left r1; }
      | Right m2 => { r2 <@ P.backdoor(m2);      r <- omap Right r2; }
      end;
      return r;
    }
  }.

  module CompRP(Rho:RHO) (P:Pi.REAL.PROTOCOL) : RPi.REAL.PROTOCOL = {
    
    proc init () = {
      P.init();
      Rho(P).init();
    }
    include CompR_I(Rho,P) 
  }.

  module CompRF(Rho:RHO) (F:Pi.IDEAL.PROTOCOL) : RPi.IDEAL.PROTOCOL = {
    
    proc init () = {
      F.init();
      Rho(F).init();
    }
    
    include Rho(F) [inputs, outputs]

    proc step (m:RPi.IDEAL.step) : unit = {
      match (m) with
      | Left  m1 => { Rho(F).step(m1); }
      | Right m2 => { F.step(m2); }
      end;
    }

    proc backdoor (m:RPi.IDEAL.ask_backdoor) : RPi.IDEAL.backdoor option = {
      var r1, r2, r;
      match (m) with
      | Left m1  => { r1 <@ Rho(F).backdoor(m1); r <- omap Left r1; }
      | Right m2 => { r2 <@ F.backdoor(m2); r <- omap Right r2; }
      end;
      return r;
    }

  }.

  module (Sid(Sf:Pi.SIMULATOR) : RPi.SIMULATOR) (FB : RPi.IDEAL.BACKDOORS) = {
  
    module FBPi = {
      proc step(m:Pi.IDEAL.step) : unit = {
        FB.step(Right m);
      }
      
      proc backdoor(m:Pi.IDEAL.ask_backdoor) : Pi.IDEAL.backdoor option = {
        var r;
        r <@ FB.backdoor (Right m);
        return obind getr r;
      }
    }
    
    proc init = Sf(FBPi).init 

    proc step(m:RPi.REAL.step) : unit = {
      match (m) with
      | Left m1  => { FB.step(Left m1); }
      | Right m2 => { Sf(FBPi).step(m2); }
      end;
    }
    
    proc backdoor(m:RPi.REAL.ask_backdoor) : RPi.REAL.backdoor option = {
      var r1, r2;
      var r :RPi.REAL.backdoor option;
      match (m) with
      | Left  m1 => { r1 <@ FB.backdoor(Left m1); r <- omap Left (obind getl r1); } 
      | Right m2 => { r2 <@ Sf(FBPi).backdoor(m2); r <- omap Right r2; }
      end;
      return r;
    }
  }.

  module (CompZR(Z:RPi.REAL.ENV, Rho:RHO):Pi.REAL.ENV) (I : Pi.REAL.E_INTERFACE) = {
    proc distinguish() : bool = {
      var b;
      Rho(I).init();
      b <@ Z(CompR_I(Rho,I)).distinguish();
      return b;
    }
  }.
      
  section COMP.
 
    declare module P  <: Pi.REAL.PROTOCOL.
    declare module Ff <: Pi.IDEAL.PROTOCOL.
    declare module Sf <: Pi.SIMULATOR {-Ff}.

    declare module Rho<: RHO {-P, -Ff, -Sf}.
 
    declare module Z<: RPi.REAL.ENV {-Rho, -P, -Ff, -Sf}.

    lemma compose &m : 
      Pr[RPi.REAL.UC_emul(Z,CompRP(Rho,P)).main() @ &m : res] - 
        Pr[RPi.REAL.UC_emul(Z,RPi.CompS(CompRF(Rho,Ff), Sid(Sf))).main() @ &m : res] = 
      Pr[Pi.REAL.UC_emul(CompZR(Z,Rho), P).main() @ &m : res] - 
        Pr[Pi.REAL.UC_emul(CompZR(Z,Rho), Pi.CompS(Ff,Sf)).main() @ &m : res].
    proof.
      have -> :  
        Pr[RPi.REAL.UC_emul(Z,CompRP(Rho,P)).main() @ &m : res] =
        Pr[Pi.REAL.UC_emul(CompZR(Z,Rho), P).main() @ &m : res].
      + by byequiv => //; proc; inline *; wp; sim.
      have -> // : 
        Pr[RPi.REAL.UC_emul(Z,RPi.CompS(CompRF(Rho,Ff), Sid(Sf))).main() @ &m : res] =
        Pr[Pi.REAL.UC_emul(CompZR(Z,Rho), Pi.CompS(Ff,Sf)).main() @ &m : res]. 
      byequiv => //; proc; inline *; wp.
      call (_ : = {glob Rho, glob Ff, glob Sf}); 1,2:sim. 
      + proc; match; 1,2: smt().
        + move => m1 m2; inline *; match Left {1} 2.  
          + by auto => /#.
          call (_: ={glob Ff}); 1,2:sim.
          by auto => /> /#.
        move => m1 m2; call (_: ={glob Rho, glob Ff}); last by auto => />.
        + proc *; inline *; match Right {1} 3; 1: by auto => /#.
          by call (_: true); auto => /> /#.
        proc *; inline *;match Right {1} 3; 1: by auto => /#.
        by wp; call (_: true); auto => /> /#.
      + proc; match; 1,2: smt().
        + move=> m1 m2; wp; inline *; match Left {1} 2; 1: by auto => /#.
          by wp; call (_: ={glob Ff}); 1,2:sim; auto => /> /#.
        move=> m1 m2; wp; inline *; call (_: ={glob Rho, glob Ff}). 
        + proc *; inline *; match Right {1} 3; 1: by auto => /#.
          by call (_: true); auto => /> /#.
        + proc *; inline *; match Right {1} 3; 1: by auto => /#.
          by wp; call (_: true); auto => /> /#.       
        by auto => />.
      by swap{1} 2 1; sim />. 
    qed.
 
  end section COMP.

  abstract theory C.

  type crho = {
    cr_init : int;
    cr_in   : int;
    cr_in_i : int;
    cr_in_o : int;
    cr_out  : int;
    cr_out_i : int;
    cr_out_o : int;
    cr_st    : int;
    cr_st_i  : int;
    cr_st_o  : int;
    cr_bk    : int;
    cr_bk_i  : int;
    cr_bk_o  : int;
  }.

  op crho_pos (cr: crho) = 
    0 <= cr.`cr_init  /\
    0 <= cr.`cr_in    /\
    0 <= cr.`cr_in_i  /\
    0 <= cr.`cr_in_o  /\
    0 <= cr.`cr_out   /\
    0 <= cr.`cr_out_i /\
    0 <= cr.`cr_out_o /\
    0 <= cr.`cr_st    /\
    0 <= cr.`cr_st_i  /\
    0 <= cr.`cr_st_o  /\
    0 <= cr.`cr_bk    /\
    0 <= cr.`cr_bk_i  /\
    0 <= cr.`cr_bk_o.
  
  op cr : crho.
  axiom cr_pos : crho_pos cr.

  module type CRHO(P : Pi.REAL.IO)  = {
    proc init() : unit {} `{ N cr.`cr_init}
  
    proc inputs(i : R.inputs) : unit `{N cr.`cr_in, P.inputs : cr.`cr_in_i, P.outputs : cr.`cr_in_o} 
  
    proc outputs(o : R.ask_outputs) : R.outputs option `{N cr.`cr_out, P.inputs : cr.`cr_out_i, P.outputs : cr.`cr_out_o} 
  
    proc step(m : R.step) : unit `{N cr.`cr_st, P.inputs : cr.`cr_st_i, P.outputs : cr.`cr_st_o} 
  
    proc backdoor(m : R.ask_backdoor) : R.backdoor option `{N cr.`cr_bk, P.inputs : cr.`cr_bk_i, P.outputs : cr.`cr_bk_o} 
  }.

  op csi : csim.
  axiom csi_pos : csim_pos csi.

  op rcsi = {|
    cinit = csi.`cinit;
    cstep = max 2 (1 + csi.`cs_s + csi.`cs_b * 4 + csi.`cstep) ;
    cs_s  = max 1 csi.`cs_s;
    cs_b  = csi.`cs_b;
    cbackdoor = max 7 (3 + csi.`cb_s + csi.`cb_b * 4 + csi.`cbackdoor + csi.`cstep);
    cb_s = csi.`cb_s;
    cb_b = max 1 csi.`cb_b; 
  |}.

  lemma rcsi_pos : csim_pos rcsi by smt(csi_pos).

  (* complexity or the environement for the reduction CompRP(Rho,P) *)
  op rc : cenv.
  axiom rc_pos : cenv_pos rc.

  (* complexity or the environement of the reduction *)
  op c = {|
    cd = cr.`cr_init + rc.`cd + rc.`ci * cr.`cr_in + rc.`co * cr.`cr_out + rc.`cs * (1 + cr.`cr_st) + rc.`cb * (3 + cr.`cr_bk);
    ci = cr.`cr_in_i * rc.`ci + cr.`cr_out_i * rc.`co + cr.`cr_st_i * rc.`cs + cr.`cr_bk_i * rc.`cb;
    co = cr.`cr_in_o * rc.`ci + cr.`cr_out_o * rc.`co + cr.`cr_st_o * rc.`cs + cr.`cr_bk_o * rc.`cb;
    cs = rc.`cs;
    cb = rc.`cb;
  |}.  

  lemma c_pos : cenv_pos c by smt (rc_pos cr_pos). 

  clone Pi.C as CPi with
    op csi <- csi,
    op c   <- c
    proof csi_pos by apply csi_pos
    proof c_pos by apply c_pos.

  clone RPi.C as CRPi with
    op csi <- rcsi,
    op c <- rc
    proof csi_pos by apply rcsi_pos
    proof c_pos by apply rc_pos.

  section.

   declare module P  <: Pi.REAL.PROTOCOL.
   declare module Ff <: Pi.IDEAL.PROTOCOL.
   declare module Sf <: CPi.CSIMULATOR {-Ff}.

   declare module Rho<: CRHO {-P, -Ff, -Sf}.

   lemma ex_compose e &m : 
     (forall (Z <: CPi.CENV {-P, -Ff, -Sf}),
       `|Pr[Pi.REAL.UC_emul(Z, P).main() @ &m : res] - 
          Pr[Pi.REAL.UC_emul(Z, Pi.CompS(Ff,Sf)).main() @ &m : res]| <= e) =>
     exists (S<:CRPi.CSIMULATOR{+Sf}),
     (forall (Z <: CRPi.CENV {-Rho,-P,-Ff,-Sf}),
       `|Pr[RPi.REAL.UC_emul(Z,CompRP(Rho,P)).main() @ &m : res] - 
          Pr[RPi.REAL.UC_emul(Z,RPi.CompS(CompRF(Rho,Ff), S)).main() @ &m : res]| <= e).
   proof.
     move=> h; exists (Sid(Sf)); split.
     (* Complexity of the simulator *)
     + split.
       + by move=> kb ks FB hkb hks; proc true : time [].
       split.
       + move=> kb ks FB hkb hks; proc.
         exlim m => -[] mi. 
         + match Left 1; [1: by auto; smt() | 2: done].
           call(:true; time []); auto => />; smt(csi_pos).  
         match Right 1; [1: by auto; smt() | 2: done].
         call (:true; time [Sid(Sf, FB).FBPi.step : ['1; FB.step : 1], Sid(Sf, FB).FBPi.backdoor : [N 4; FB.backdoor : 1]]).
         + by move=> *; proc; call (:true; time []); skip => />.
         + by move=> *; proc; call (:true; time []); skip => />.
         by skip => &hr />; rewrite !bigi_constz /=; smt(csi_pos).
       move=> kb ks FB hkb hks; proc.
       exlim m => -[] mi.  
       + match Left 1; [1: by auto; smt() | 2: done].
         wp; call(:true; time []); auto => />; smt(csi_pos).
       match Right 1; [1: by auto; smt() | 2: done].
       wp;call (:true; time [Sid(Sf, FB).FBPi.step : ['1; FB.step : 1], Sid(Sf, FB).FBPi.backdoor : [N 4; FB.backdoor : 1]]).
       + by move=> *; proc; call (:true; time []); skip => />.
       + by move=> *; proc; call (:true; time []); skip => />.
       skip => &hr />; rewrite !bigi_constz /=; smt(csi_pos).
     move=> Z; rewrite (compose P Ff Sf Rho Z &m).
     (* Complexity of the environment *)
     apply (h (CompZR(Z,Rho))).
     move=> kb ks ko ki I hkb hks hko hki; proc.
     call(:true;time[CompR_I(Rho, I).inputs   : [N cr.`cr_in; I.inputs : cr.`cr_in_i; I.outputs : cr.`cr_in_o],
                     CompR_I(Rho, I).outputs  : [N cr.`cr_out; I.inputs : cr.`cr_out_i; I.outputs : cr.`cr_out_o],
                     CompR_I(Rho, I).step     : [N (1 + cr.`cr_st); I.inputs : cr.`cr_st_i; I.outputs : cr.`cr_st_o; I.step : 1],
                     CompR_I(Rho, I).backdoor : [N (3 + cr.`cr_bk); I.inputs : cr.`cr_bk_i; I.outputs : cr.`cr_bk_o; I.backdoor : 1]]).
     + move=> *; proc true : time [I.inputs: [N ki], I.outputs: [N ko]] => />.
       + by rewrite !bigi_constz /=; smt (cr_pos).
       + by move=> *; proc true : time [].
       by move=> *; proc true : time [].
     + move=> *; proc true : time [I.inputs : [N ki], I.outputs : [N ko]] => />.
       + rewrite !bigi_constz /=; smt (cr_pos). 
       + by move=> *; proc true : time [].
       by move=> *; proc true : time [].
     + move=> *; proc.
       exlim m => -[] mi. 
       + match Left 1; [1: by auto; smt() | 2: done].
         call(:true; time [I.inputs : [N ki], I.outputs : [N ko]]).
         + by move=> *; proc true : time [].
         + by move=> *; proc true : time [].
         skip => />; rewrite !bigi_constz /=; smt(cr_pos). 
       match Right 1; [1: by auto; smt() | 2: done].
       by call (:true); skip => />; smt (cr_pos).
     + move=> *; proc.
       exlim m => -[] mi. 
       + match Left 1; [1: by auto; smt() | 2: done].
         wp; call(:true; time [I.inputs : [N ki], I.outputs : [N ko]]).
         + by move=> *; proc true : time [].
         + by move=> *; proc true : time [].
         skip => />; rewrite !bigi_constz /=; smt(cr_pos).
       match Right 1; [1: by auto; smt() | 2: done].
       by wp; call (:true); skip => />; smt (cr_pos). 
     call (:true); skip => />.
     rewrite !bigi_constz /=; smt(rc_pos).
   qed.
  
  end section.
  
  end C.

  clone import TRANSITIVITY as TRANS with 
    type H1.REAL.inputs       <- R.inputs,
    type H1.REAL.ask_outputs  <- R.ask_outputs,
    type H1.REAL.outputs      <- R.outputs,
    type H1.REAL.step         <- RPi.REAL.step,
    type H1.REAL.ask_backdoor <- RPi.REAL.ask_backdoor, 
    type H1.REAL.backdoor     <- RPi.REAL.backdoor,
    type H1.IDEAL.step         <- RPi.IDEAL.step,
    type H1.IDEAL.ask_backdoor <- RPi.IDEAL.ask_backdoor, 
    type H1.IDEAL.backdoor     <- RPi.IDEAL.backdoor.

  section StrongCOMP.

    declare module P  <: Pi.REAL.PROTOCOL.
    declare module Ff <: Pi.IDEAL.PROTOCOL.
    declare module Sf <: Pi.SIMULATOR {-Ff}.

    declare module Rho<: RHO {-P, -Ff, -Sf}.
    declare module F <: H2.IDEAL.PROTOCOL {-Sf}.
    declare module S <: H2.SIMULATOR {-F, -Sf}.

    declare module Z<: RPi.REAL.ENV {-Rho, -P, -Ff, -Sf, -F, -S}.

    lemma strong_compose &m : 
      `| Pr[GOAL.REAL.UC_emul(Z,CompRP(Rho,P)).main() @ &m : res] - 
         Pr[GOAL.REAL.UC_emul(Z,GOAL.CompS(F, SeqS(S, Sid(Sf)))).main() @ &m : res] |
       <= 
      `| Pr[Pi.REAL.UC_emul(CompZR(Z,Rho), P).main() @ &m : res] - 
         Pr[Pi.REAL.UC_emul(CompZR(Z,Rho), Pi.CompS(Ff,Sf)).main() @ &m : res] | + 
      `| Pr[H2.REAL.UC_emul(CompZS(Z, Sid(Sf)), CompRF(Rho,Ff)).main() @ &m : res] - 
         Pr[H2.REAL.UC_emul(CompZS(Z, Sid(Sf)), H2.CompS(F,S)).main() @ &m : res] |.
    proof.
      have h1 := uc_transitivity (CompRP(Rho,P)) (CompRF(Rho,Ff)) F (Sid(Sf)) S Z &m.
      have h2 := compose P Ff Sf Rho Z &m.
      apply (StdOrder.RealOrder.ler_trans _ _ _ h1) => {h1}.
      have -> : Pr[H1.REAL.UC_emul(Z, CompRP(Rho, P)).main() @ &m : res] = 
                Pr[Pi.REAL.UC_emul(CompZR(Z, Rho), P).main() @ &m : res].
      + by byequiv=> //; proc; inline *; wp; sim.
      have -> // : Pr[H1.REAL.UC_emul(Z, H1.CompS(CompRF(Rho, Ff), Sid(Sf))).main() @ &m : res] =
                   Pr[Pi.REAL.UC_emul(CompZR(Z, Rho), Pi.CompS(Ff, Sf)).main() @ &m : res].
      byequiv=> //; proc; inline *; wp. swap{1} 2 1.
      call (_: ={glob Rho, glob Ff,glob Sf}); 1,2:sim.
      + proc; match; 1,2: smt().
        + move=> m1 m2; inline *; match Left {1} 2; 1: by auto => /> /#.
          call (_: ={glob Ff} ); 1,2:sim.
          by auto => /#.
        move=> m1 m2; inline *; call (_: ={glob Rho, glob Ff}). 
        + proc *; inline *; match Right {1} 3; 1: by auto => /> /#.
          by call (_: true); auto => /> /#.
        + proc *; inline *; match Right {1} 3; 1: by auto => /> /#.
          auto; call (_: true);auto => /> /#.
        by auto => />.
      + proc; match;1,2: smt().
        + move=> m1 m2; inline *; match Left {1} 2; 1: by auto => /> /#.
          wp;call (_: ={glob Ff} ); 1,2:sim.
          by auto => /#.
        move=> m1 m2; inline *; wp; call (_: ={glob Rho, glob Ff}). 
        + proc *; inline *; match Right {1} 3; 1: by auto => /> /#.
          by call (_: true); auto => /> /#.
        + proc *; inline *; match Right {1} 3; 1: by auto => /> /#.
          auto; call (_: true);auto => /> /#.
        by auto => />.
      sim />.
     qed.

  end section StrongCOMP.

  abstract theory SC.

  op csi : csim.

  axiom csi_pos : csim_pos csi.

  op rcsi : csim =
    {| cinit = csi.`cinit; cstep = max 2 (1 + csi.`cs_s + csi.`cs_b * 4 + csi.`cstep); cs_s =
      max 1 csi.`cs_s; cs_b = csi.`cs_b; cbackdoor =
      max 7 (3 + csi.`cb_s + csi.`cb_b * 4 + csi.`cbackdoor + csi.`cstep); cb_s = csi.`cb_s; cb_b =
      max 1 csi.`cb_b; |}.
  
  lemma rcsi_pos : csim_pos rcsi by smt (csi_pos).

  clone TRANS.C as CT
    with op cs12 <- rcsi
    proof cs12_pos by apply rcsi_pos.

  clone COMPOSITION.C as C0 with 
    op rc <- CT.cz,
    op csi <- csi
    proof rc_pos by apply CT.cz_pos
    proof csi_pos by apply csi_pos.

  section.  
    declare module P  <: Pi.REAL.PROTOCOL.
    declare module Ff <: Pi.IDEAL.PROTOCOL.
    declare module Sf <: C0.CPi.CSIMULATOR {-Ff}.

    declare module Rho<: C0.CRHO {-P, -Ff, -Sf}.
    declare module F <: H2.IDEAL.PROTOCOL {-Sf}.
    declare module S <: CT.CH2.CSIMULATOR {-F, -Sf}.

    lemma ex_strong_compose &m e1 e2 : 
      (forall (Z <: C0.CPi.CENV {-P, -Ff, -Sf}),
        `| Pr[Pi.REAL.UC_emul(Z, P).main() @ &m : res] - 
         Pr[Pi.REAL.UC_emul(Z, Pi.CompS(Ff,Sf)).main() @ &m : res] | <= e1) =>
      (forall (Z <: CT.CH2.CENV {-CompRF(Rho,Ff), -F, -S}),
        `| Pr[H2.REAL.UC_emul(Z, CompRF(Rho,Ff)).main() @ &m : res] - 
           Pr[H2.REAL.UC_emul(Z, H2.CompS(F,S)).main() @ &m : res] | <= e2) =>
      exists (S' <: CT.CGOAL.CSIMULATOR {+S, +Sf, -F}), 
      (forall (Z <: CT.CGOAL.CENV {-Rho, -P, -Ff, -Sf, -F, -S}),
        `| Pr[GOAL.REAL.UC_emul(Z,CompRP(Rho,P)).main() @ &m : res] - 
           Pr[GOAL.REAL.UC_emul(Z,GOAL.CompS(F, S')).main() @ &m : res] | <= e1 + e2).
    proof.
      move=> hP HR.
      have [Srho HSrho]:= C0.ex_compose P Ff Sf Rho e1 &m _; 1: by move=> Z0; apply (hP Z0).
      have := CT.ex_uc_transitivity (CompRP(Rho,P)) (CompRF(Rho,Ff)) F Srho S &m e1 e2 _ _.
      + move=> Z1; have := HSrho Z1.
        + have -> : Pr[RPi.REAL.UC_emul(Z1, CompRP(Rho, P)).main() @ &m : res] = 
                    Pr[H1.REAL.UC_emul(Z1, CompRP(Rho, P)).main() @ &m : res].
          + by byequiv => //; sim.
          have -> // : Pr[RPi.REAL.UC_emul(Z1, RPi.CompS(CompRF(Rho, Ff), Srho)).main() @ &m : res] = 
                    Pr[H1.REAL.UC_emul(Z1, H1.CompS(CompRF(Rho, Ff), Srho)).main() @ &m : res].
          + by byequiv => //; sim.
      + by move=> Z1; apply (HR Z1).
      by move=> [S' hS']; exists S' => Z; apply (hS' Z).
    qed.

  end section.

  end SC.

end COMPOSITION.

abstract theory PARA.
  
  clone EXEC_MODEL as Pi1.
  clone EXEC_MODEL as Pi2.

  clone EXEC_MODEL as Pi12 with
    type inputs         = (Pi1.inputs, Pi2.inputs) sum,
    type ask_outputs    = (Pi1.ask_outputs, Pi2.ask_outputs) sum,
    type outputs        = (Pi1.outputs, Pi2.outputs) sum,
    type step           = (Pi1.step, Pi2.step) sum,
    type ask_backdoor   = (Pi1.ask_backdoor, Pi2.ask_backdoor) sum,
    type backdoor       = (Pi1.backdoor, Pi2.backdoor) sum.

  (* Build the parallel composition of Pi1 and Pi2 *)
  
  module EIPara(P1:Pi1.E_INTERFACE, P2:Pi2.E_INTERFACE) : Pi12.E_INTERFACE = {
   
    proc inputs(i: Pi12.inputs) = {
      match i with
      | Left i => P1.inputs(i);
      | Right i => P2.inputs(i);
      end;
    }

    proc outputs(o : Pi12.ask_outputs) : Pi12.outputs option = {
      var r1, r2, r;
      match o with
      | Left o  => { r1 <@ P1.outputs(o); r <- omap Left r1; }
      | Right o => { r2 <@ P2.outputs(o); r <- omap Right r2; }
      end;
      return r;
    }
  
    proc step(m : Pi12.step) : unit = {
      match m with
      | Left m  => P1.step(m);
      | Right m => P2.step(m);
      end;
    }
  
    proc backdoor(m : Pi12.ask_backdoor) : Pi12.backdoor option = {
      var r1, r2, r;
      match m with 
      | Left m  => { r1 <@ P1.backdoor(m); r <- omap Left r1; }
      | Right m => { r2 <@ P2.backdoor(m); r <- omap Right r2; }
      end;
      return r;
    }
 
  }.

  module PPara (P1:Pi1.PROTOCOL, P2:Pi2.PROTOCOL) : Pi12.PROTOCOL = {
    proc init() = {
      P1.init();
      P2.init();
    }

    include EIPara(P1,P2)
  }.

end PARA.

abstract theory PARA_IR.

  clone EXEC_MODEL as Pi1.
  clone REAL_IDEAL as Pi2.

  clone PARA as R with
    type Pi1.inputs        <- PARA_IR.Pi1.inputs,
    type Pi1.ask_outputs   <- PARA_IR.Pi1.ask_outputs,
    type Pi1.outputs       <- PARA_IR.Pi1.outputs,
    type Pi1.step          <- PARA_IR.Pi1.step,
    type Pi1.ask_backdoor  <- PARA_IR.Pi1.ask_backdoor,
    type Pi1.backdoor      <- PARA_IR.Pi1.backdoor,
    type Pi2.inputs        <- PARA_IR.Pi2.REAL.inputs,
    type Pi2.ask_outputs   <- PARA_IR.Pi2.REAL.ask_outputs,
    type Pi2.outputs       <- PARA_IR.Pi2.REAL.outputs,
    type Pi2.step          <- PARA_IR.Pi2.REAL.step,
    type Pi2.ask_backdoor  <- PARA_IR.Pi2.REAL.ask_backdoor,
    type Pi2.backdoor      <- PARA_IR.Pi2.REAL.backdoor.

  clone PARA as I with
    type Pi1.inputs        <- PARA_IR.Pi1.inputs,
    type Pi1.ask_outputs   <- PARA_IR.Pi1.ask_outputs,
    type Pi1.outputs       <- PARA_IR.Pi1.outputs,
    type Pi1.step          <- PARA_IR.Pi1.step,
    type Pi1.ask_backdoor  <- PARA_IR.Pi1.ask_backdoor,
    type Pi1.backdoor      <- PARA_IR.Pi1.backdoor,
    type Pi2.inputs        <- PARA_IR.Pi2.REAL.inputs,
    type Pi2.ask_outputs   <- PARA_IR.Pi2.REAL.ask_outputs,
    type Pi2.outputs       <- PARA_IR.Pi2.REAL.outputs,
    type Pi2.step          <- PARA_IR.Pi2.IDEAL.step,
    type Pi2.ask_backdoor  <- PARA_IR.Pi2.IDEAL.ask_backdoor,
    type Pi2.backdoor      <- PARA_IR.Pi2.IDEAL.backdoor.

  clone REAL_IDEAL as RI with
    type REAL.inputs         <- R.Pi12.inputs,
    type REAL.ask_outputs    <- R.Pi12.ask_outputs,
    type REAL.outputs        <- R.Pi12.outputs,
    type REAL.step           <- R.Pi12.step,
    type REAL.ask_backdoor   <- R.Pi12.ask_backdoor,
    type REAL.backdoor       <- R.Pi12.backdoor,
    type IDEAL.step          <- I.Pi12.step,
    type IDEAL.ask_backdoor  <- I.Pi12.ask_backdoor,
    type IDEAL.backdoor      <- I.Pi12.backdoor.
   
  module (Sid(Sf:Pi2.SIMULATOR) : RI.SIMULATOR) (FB : RI.IDEAL.BACKDOORS) = {
  
    module FBPi = {
      proc step(m:Pi2.IDEAL.step) : unit = {
        FB.step(Right m);
      }
      
      proc backdoor(m:Pi2.IDEAL.ask_backdoor) : Pi2.IDEAL.backdoor option = {
        var r;
        r <@ FB.backdoor (Right m);
        return obind getr r;
      }
    }
    
    proc init = Sf(FBPi).init 
  
    proc step(m:R.Pi12.step) : unit = {
      match (m) with
      | Left m1  => { FB.step(Left m1); }
      | Right m2 => { Sf(FBPi).step(m2); }
      end;
    }
    
    proc backdoor(m:R.Pi12.ask_backdoor) : R.Pi12.backdoor option = {
      var r1, r2, r;
      match (m) with
      | Left  m1 => { r1 <@ FB.backdoor(Left m1); r <- omap Left (obind getl r1); } 
      | Right m2 => { r2 <@ Sf(FBPi).backdoor(m2); r <- omap Right r2; }
      end;
      return r;
    }
  }.

  module (CompZR(Z:RI.REAL.ENV, F1: Pi1.PROTOCOL) : Pi2.REAL.ENV) (P2:Pi2.REAL.E_INTERFACE) = {
    proc distinguish() = {
      var b;
      F1.init();
      b <@ Z(R.EIPara(F1,P2)).distinguish();
      return b;
    }
  }.
  
  section PROOF.

    declare module F1 <: Pi1.PROTOCOL.
    declare module P2 <: Pi2.REAL.PROTOCOL {-F1}.
    declare module F2 <: Pi2.IDEAL.PROTOCOL {-F1, -P2}.
    declare module S2 <: Pi2.SIMULATOR {-F1, -P2, -F2}.

    declare module Z  <: RI.REAL.ENV { -F1, -P2, -F2, -S2 }.

    equiv F2_step : Sid(S2, I.PPara(F1, F2)).FBPi.step ~ F2.step : ={arg, glob F2, glob F1} ==>  ={res, glob F2, glob F1}.
    proof.
      proc *; inline *; sp; match Right {1} 1; 1: by auto; smt(). 
      by call(:true); skip.
    qed.

    equiv F2_backdoor: Sid(S2, I.PPara(F1, F2)).FBPi.backdoor ~ F2.backdoor : ={arg, glob F2, glob F1} ==>  ={res, glob F2, glob F1}.
    proof.
      proc *; inline *; sp; match Right {1} 1; 1: by auto; smt(). 
      by wp; call(:true); skip => /> /#.
    qed.

    lemma compose &m : 
      Pr[RI.REAL.UC_emul(Z, R.PPara(F1, P2)).main() @ &m : res] -
      Pr[RI.REAL.UC_emul(Z, RI.CompS(I.PPara(F1,F2), Sid(S2))).main() @ &m : res] = 
      Pr[Pi2.REAL.UC_emul(CompZR(Z,F1), P2).main() @ &m : res] -
      Pr[Pi2.REAL.UC_emul(CompZR(Z,F1), Pi2.CompS(F2, S2)).main() @ &m : res].
    proof.
      congr.
      + by byequiv => //; proc; inline *; swap{1} 1 1; sim.
      congr.
      byequiv => //; proc; inline *; wp.
      call (: ={glob F1, glob F2, glob S2}); 1..2: sim.
      + proc; inline *; match => *; 1..2: smt().
        + sp; match Left {1} 1; 1: by auto; smt().
          by call(:true); skip.
        call(: ={glob F2, glob F1}); last by auto.
        + by apply F2_step.
        by apply F2_backdoor.
      + proc; inline *; match => *; 1..2: smt().
        + wp; sp; match Left {1} 1; 1: by auto; smt().
          by wp; call(:true); skip => /#.
        wp; call(: ={glob F2, glob F1}); last by auto.
        + by apply F2_step.
        by apply F2_backdoor.
      swap{2} 3 -2; sim />.
    qed.

  end section PROOF.

  abstract theory C.

  op cz  : cenv.  (* complexity of Z   *)
  op cf1 : cprot. (* complexity of F1  *)
  op cs2 : csim.  (* complexity of S2  *)

  axiom cz_pos   : cenv_pos cz.
  axiom cf1_pos  : cprot_pos cf1.
  axiom cs2_pos  : csim_pos cs2.

  clone Pi1.CP as CPi1 with 
    op cp <- cf1 
    proof * by smt (cf1_pos).

  clone RI.C as CRI with
    op c <- cz,
    (* complexity of the simulator for Para(F1,P2) *)
    op csi = {|
        cinit = cs2.`cinit;
        cstep = max 2 (1 + cs2.`cstep + cs2.`cs_s + 4 * cs2.`cs_b);
        cs_s  = max 1 cs2.`cs_s;
        cs_b  = cs2.`cs_b; 
        cbackdoor = max 7 (3 + cs2.`cbackdoor + cs2.`cb_s + 4 * cs2.`cb_b);
        cb_s  = cs2.`cb_s;
        cb_b  = max 1 cs2.`cb_b;
      |}
    proof *by smt(cz_pos cs2_pos).
  
  clone Pi2.C as CPi2 with
    op c = {|
        cd = cf1.`cpinit + cz.`cd + 
             (1 + cf1.`cpinputs) * cz.`ci + (4 + cf1.`cpoutputs) * cz.`co + (1 + cf1.`cpstep) * cz.`cs + (4 + cf1.`cpbackdoor) * cz.`cb;
        ci = cz.`ci;
        co = cz.`co;
        cs = cz.`cs;
        cb = cz.`cb;
      |},
    op csi <- cs2
    proof * by smt(cf1_pos cz_pos cs2_pos).

  section.

    declare module F1 <: CPi1.CPROTOCOL.
    declare module P2 <: Pi2.REAL.PROTOCOL {-F1}.
    declare module F2 <: Pi2.IDEAL.PROTOCOL {-F1, -P2}.
    declare module S2 <: CPi2.CSIMULATOR {-F1, -P2, -F2}.

    lemma ex_compose &m e : 
      (forall (Z<:CPi2.CENV{-P2, -F2, -S2}), 
         `|Pr[Pi2.REAL.UC_emul(Z, P2).main() @ &m : res] - 
            Pr[Pi2.REAL.UC_emul(Z, Pi2.CompS(F2,S2)).main() @ &m : res]| <= e) =>
      exists (S <: CRI.CSIMULATOR { +S2, -I.PPara(F1,F2)}), 
        forall (Z <: CRI.CENV{-F1, -P2, -F2, -S2}), 
         `|Pr[RI.REAL.UC_emul(Z, R.PPara(F1, P2)).main() @ &m : res] -
             Pr[RI.REAL.UC_emul(Z, RI.CompS(I.PPara(F1,F2), S)).main() @ &m : res]| <= e.
    proof.
      move=> h.
      exists (Sid(S2)); split.
      + split.
        + by move=> kbackdoor kstep FB hkb hks; proc true : time [].
        split => kbackdoor kstep FB hkb hks.
        + proc; exlim m => -[] mi. 
          + match Left 1; [1: by auto; smt() | 2: done].
            call(:true; time []); auto => />; smt(cs2_pos). 
          match Right 1; [1: by auto; smt() | 2: done].
          call(:true; time [Sid(S2, FB).FBPi.step     : [ '1; FB.step : 1],
                            Sid(S2, FB).FBPi.backdoor : [ N 4; FB.backdoor : 1]]).
          + by move=> * /=; proc; call (:true; time []); auto.
          + by move=> * /=; proc; call (:true; time []); auto.     
          skip => />; rewrite !bigi_constz /=; smt(cs2_pos). 
        proc; exlim m => -[] mi. 
        + match Left 1; [1:by auto; smt() | 2: done].
          wp; call(:true; time []); auto => />; smt(cs2_pos).
        match Right 1; [1: by auto; smt() | 2: done].
        wp; call(:true; time [Sid(S2, FB).FBPi.step     : [ '1; FB.step : 1],
                              Sid(S2, FB).FBPi.backdoor : [ N 4; FB.backdoor : 1]]).
        + by move=> * /=; proc; call (:true; time []); auto.
        + by move=> * /=; proc; call (:true; time []); auto.     
        skip => />; rewrite !bigi_constz /=; smt(cs2_pos).
      move=> Z.
      rewrite (compose F1 P2 F2 S2 Z).
      apply (h (CompZR(Z, F1))) => kbackdoor kstep koutputs kinputs I hkb hks hko hki.
      proc.
      call (:true; time [R.EIPara(F1, I).inputs   : [N (1 + cf1.`cpinputs)  ; I.inputs   : 1],
                         R.EIPara(F1, I).outputs  : [N (4 + cf1.`cpoutputs) ; I.outputs  : 1],
                         R.EIPara(F1, I).step     : [N (1 + cf1.`cpstep)    ; I.step     : 1],
                         R.EIPara(F1, I).backdoor : [N (4 + cf1.`cpbackdoor); I.backdoor : 1]]) => *.
      + proc; exlim i => -[] ii.
        + match Left 1; [1: by auto => /# | 2:done]. 
          by call(:true; time []); auto => /> /#.
        match Right 1; [1: by auto => /# | 2:done].
        by call(:true; time []); auto => />; smt (cf1_pos).
      + proc; exlim o => -[] oi.
        + match Left 1; [1: by auto => /# | 2:done]. 
          by wp; call(:true; time []); auto => /> /#.
        match Right 1; [1: by auto => /# | 2:done].
        by wp; call(:true; time []); auto => />; smt (cf1_pos).
      + proc; exlim m => -[] mi.
        + match Left 1; [1: by auto => /# | 2:done]. 
          by call(:true; time []); auto => /> /#.
        match Right 1; [1: by auto => /# | 2:done].
        by call(:true; time []); auto => />; smt (cf1_pos).
      + proc; exlim m => -[] mi.
        + match Left 1; [1: by auto => /# | 2:done]. 
          by wp; call(:true; time []); auto => /> /#.
        match Right 1; [1: by auto => /# | 2:done].
        by wp; call(:true; time []); auto => />; smt (cf1_pos).
      call(:true; time []); skip => />.
      rewrite !bigi_constz /=; smt(cz_pos cf1_pos).
    qed.
  end section.
  end C.

end PARA_IR.

abstract theory PARA_RI.

  clone REAL_IDEAL as Pi1.
  clone EXEC_MODEL as Pi2.

  clone PARA as R with
    type Pi1.inputs        <- PARA_RI.Pi1.REAL.inputs,
    type Pi1.ask_outputs   <- PARA_RI.Pi1.REAL.ask_outputs,
    type Pi1.outputs       <- PARA_RI.Pi1.REAL.outputs,
    type Pi1.step          <- PARA_RI.Pi1.REAL.step,
    type Pi1.ask_backdoor  <- PARA_RI.Pi1.REAL.ask_backdoor,
    type Pi1.backdoor      <- PARA_RI.Pi1.REAL.backdoor,
    type Pi2.inputs        <- PARA_RI.Pi2.inputs,
    type Pi2.ask_outputs   <- PARA_RI.Pi2.ask_outputs,
    type Pi2.outputs       <- PARA_RI.Pi2.outputs,
    type Pi2.step          <- PARA_RI.Pi2.step,
    type Pi2.ask_backdoor  <- PARA_RI.Pi2.ask_backdoor,
    type Pi2.backdoor      <- PARA_RI.Pi2.backdoor.

  clone PARA as I with
    type Pi1.inputs        <- PARA_RI.Pi1.REAL.inputs,
    type Pi1.ask_outputs   <- PARA_RI.Pi1.REAL.ask_outputs,
    type Pi1.outputs       <- PARA_RI.Pi1.REAL.outputs,
    type Pi1.step          <- PARA_RI.Pi1.IDEAL.step,
    type Pi1.ask_backdoor  <- PARA_RI.Pi1.IDEAL.ask_backdoor,
    type Pi1.backdoor      <- PARA_RI.Pi1.IDEAL.backdoor,
    type Pi2.inputs        <- PARA_RI.Pi2.inputs,
    type Pi2.ask_outputs   <- PARA_RI.Pi2.ask_outputs,
    type Pi2.outputs       <- PARA_RI.Pi2.outputs,
    type Pi2.step          <- PARA_RI.Pi2.step,
    type Pi2.ask_backdoor  <- PARA_RI.Pi2.ask_backdoor,
    type Pi2.backdoor      <- PARA_RI.Pi2.backdoor.

  clone REAL_IDEAL as RI with
    type REAL.inputs         <- R.Pi12.inputs,
    type REAL.ask_outputs    <- R.Pi12.ask_outputs,
    type REAL.outputs        <- R.Pi12.outputs,
    type REAL.step           <- R.Pi12.step,
    type REAL.ask_backdoor   <- R.Pi12.ask_backdoor,
    type REAL.backdoor       <- R.Pi12.backdoor,
    type IDEAL.step          <- I.Pi12.step,
    type IDEAL.ask_backdoor  <- I.Pi12.ask_backdoor,
    type IDEAL.backdoor      <- I.Pi12.backdoor.
   
  module (Sid(Sf:Pi1.SIMULATOR) : RI.SIMULATOR) (FB : RI.IDEAL.BACKDOORS) = {
  
    module FBPi = {
      proc step(m:Pi1.IDEAL.step) : unit = {
        FB.step(Left m);
      }
      
      proc backdoor(m:Pi1.IDEAL.ask_backdoor) : Pi1.IDEAL.backdoor option = {
        var r;
        r <@ FB.backdoor (Left m);
        return obind getl r;
      }
    }
    
    proc init = Sf(FBPi).init 

    proc step(m:R.Pi12.step) : unit = {
      match (m) with
      | Left m1  => { Sf(FBPi).step(m1); }
      | Right m2 => { FB.step(Right m2); }
      end;
    }
    
    proc backdoor(m:R.Pi12.ask_backdoor) : R.Pi12.backdoor option = {
      var r1, r2, r;
      match (m) with
      | Left  m1 => { r1 <@ Sf(FBPi).backdoor(m1); r <- omap Left r1; } 
      | Right m2 => { r2 <@ FB.backdoor(Right m2); r <- omap Right (obind getr r2); }
      end;
      return r;
    }
  }.

  module (CompZR(Z:RI.REAL.ENV, F2: Pi2.PROTOCOL) : Pi1.REAL.ENV) (P1:Pi1.REAL.E_INTERFACE) = {
    proc distinguish() = {
      var b;
      F2.init();
      b <@ Z(R.EIPara(P1,F2)).distinguish();
      return b;
    }
  }.
  
  section PROOF.

    declare module F2 <: Pi2.PROTOCOL.
    declare module P1 <: Pi1.REAL.PROTOCOL {-F2}.
    declare module F1 <: Pi1.IDEAL.PROTOCOL {-F2, -P1}.
    declare module S1 <: Pi1.SIMULATOR {-F2, -P1, -F1}.

    declare module Z  <: RI.REAL.ENV { -F2, -P1, -F1, -S1 }.

    equiv F1_step : Sid(S1, I.PPara(F1, F2)).FBPi.step ~ F1.step : ={arg, glob F2, glob F1} ==>  ={res, glob F2, glob F1}.
    proof.
      proc *; inline *; sp; match Left {1} 1; 1: by auto; smt(). 
      by call(:true); skip.
    qed.

    equiv F1_backdoor: Sid(S1, I.PPara(F1, F2)).FBPi.backdoor ~ F1.backdoor : ={arg, glob F2, glob F1} ==>  ={res, glob F2, glob F1}.
    proof.
      proc *; inline *; sp; match Left {1} 1; 1: by auto; smt(). 
      by wp; call(:true); skip => /> /#.
    qed.

    lemma compose &m : 
      Pr[RI.REAL.UC_emul(Z, R.PPara(P1, F2)).main() @ &m : res] -
      Pr[RI.REAL.UC_emul(Z, RI.CompS(I.PPara(F1,F2), Sid(S1))).main() @ &m : res] = 
      Pr[Pi1.REAL.UC_emul(CompZR(Z,F2), P1).main() @ &m : res] -
      Pr[Pi1.REAL.UC_emul(CompZR(Z,F2), Pi1.CompS(F1, S1)).main() @ &m : res].
    proof.
      congr.
      + byequiv => //; proc; inline *; sim.
      congr.
      byequiv => //; proc; inline *; wp.
      call (: ={glob F1, glob F2, glob S1}); 1..2: sim.
      + proc; inline *; match => *; 1..2: smt().
        + call(: ={glob F2, glob F1}); last by auto.
          + by apply F1_step.
          by apply F1_backdoor.
        sp; match Right {1} 1; 1: by auto; smt().
        by call(:true); skip.
      + proc; inline *; match => *; 1..2: smt().
        + wp; call(: ={glob F2, glob F1}); last by auto.
          + by apply F1_step.
          by apply F1_backdoor.
        wp; sp; match Right {1} 1; 1: by auto; smt().
        by wp; call(:true); skip => /#.
      swap{2} 3 -1; sim />.
    qed.

  end section PROOF.

  abstract theory C.

  op cz  : cenv.  (* complexity of Z   *)
  op cf2 : cprot. (* complexity of F2  *)
  op cs1 : csim.  (* complexity of S1  *)

  axiom cz_pos   : cenv_pos cz.
  axiom cf2_pos  : cprot_pos cf2.
  axiom cs1_pos  : csim_pos cs1.

  clone Pi2.CP as CPi2 with 
    op cp <- cf2 
    proof * by smt (cf2_pos).

  clone RI.C as CRI with
    op c <- cz,
    (* complexity of the simulator for Para(F1,P2) *)
    op csi = {|
        cinit = cs1.`cinit;
        cstep = max 2 (1 + cs1.`cstep + cs1.`cs_s + 4 * cs1.`cs_b);
        cs_s  = max 1 cs1.`cs_s;
        cs_b  = cs1.`cs_b; 
        cbackdoor = max 7 (3 + cs1.`cbackdoor + cs1.`cb_s + 4 * cs1.`cb_b);
        cb_s  = cs1.`cb_s;
        cb_b  = max 1 cs1.`cb_b;
      |}
    proof *by smt(cz_pos cs1_pos).
  
  clone Pi1.C as CPi1 with
    op c = {|
        cd = cf2.`cpinit + cz.`cd + 
             (1 + cf2.`cpinputs) * cz.`ci + (4 + cf2.`cpoutputs) * cz.`co + (1 + cf2.`cpstep) * cz.`cs + (4 + cf2.`cpbackdoor) * cz.`cb;
        ci = cz.`ci;
        co = cz.`co;
        cs = cz.`cs;
        cb = cz.`cb;
      |},
    op csi <- cs1
    proof * by smt(cf2_pos cz_pos cs1_pos).

  section.

    declare module F2 <: CPi2.CPROTOCOL.
    declare module P1 <: Pi1.REAL.PROTOCOL {-F2}.
    declare module F1 <: Pi1.IDEAL.PROTOCOL {-F2, -P1}.
    declare module S1 <: CPi1.CSIMULATOR {-F2, -P1}.

    lemma ex_compose &m e : 
      (forall (Z<:CPi1.CENV{-P1, -F1, -S1}), 
         `|Pr[Pi1.REAL.UC_emul(Z, P1).main() @ &m : res] - 
            Pr[Pi1.REAL.UC_emul(Z, Pi1.CompS(F1,S1)).main() @ &m : res]| <= e) =>
      exists (S <: CRI.CSIMULATOR { +S1, -I.PPara(F1,F2) }), 
        forall (Z <: CRI.CENV{-F2, -P1, -F1, -S1}), 
         `|Pr[RI.REAL.UC_emul(Z, R.PPara(P1, F2)).main() @ &m : res] -
            Pr[RI.REAL.UC_emul(Z, RI.CompS(I.PPara(F1,F2), S)).main() @ &m : res]| <= e.
    proof.
      move=> h.
      exists (Sid(S1)); split.
      + split.
        + by move=> kbackdoor kstep FB hkb hks; proc true : time [].
        split => kbackdoor kstep FB hkb hks.
        + proc; exlim m => -[] mi. 
          + match Left 1; [1: by auto; smt() | 2:done] .
            call(:true; time [Sid(S1, FB).FBPi.step     : [ '1; FB.step : 1],
                              Sid(S1, FB).FBPi.backdoor : [ N 4; FB.backdoor : 1]]).
            + by move=> * /=; proc; call (:true; time []); auto.
            + by move=> * /=; proc; call (:true; time []); auto.     
            skip => />; rewrite !bigi_constz /=; smt(cs1_pos). 
          match Right 1; [1: by auto; smt() | 2:done].
          call(:true; time []); auto => />; smt(cs1_pos). 
        proc; exlim m => -[] mi. 
        + match Left 1; [1: by auto; smt() | 2:done].
          wp; call(:true; time [Sid(S1, FB).FBPi.step     : [ '1; FB.step : 1],
                                Sid(S1, FB).FBPi.backdoor : [ N 4; FB.backdoor : 1]]).
          + by move=> * /=; proc; call (:true; time []); auto.
          + by move=> * /=; proc; call (:true; time []); auto.     
          skip => />; rewrite !bigi_constz /=; smt(cs1_pos).
        match Right 1; [1: by auto; smt() | 2:done].
        wp; call(:true; time []); auto => />; smt(cs1_pos).
      move=> Z.
      rewrite (compose F2 P1 F1 S1 Z).
      apply (h (CompZR(Z, F2))) => kbackdoor kstep koutputs kinputs I hkb hks hko hki.
      proc.
      call (:true; time [R.EIPara(I, F2).inputs   : [N (1 + cf2.`cpinputs)  ; I.inputs   : 1],
                         R.EIPara(I, F2).outputs  : [N (4 + cf2.`cpoutputs) ; I.outputs  : 1],
                         R.EIPara(I, F2).step     : [N (1 + cf2.`cpstep)    ; I.step     : 1],
                         R.EIPara(I, F2).backdoor : [N (4 + cf2.`cpbackdoor); I.backdoor : 1]]) => *.
      + proc; exlim i => -[] ii.
        + match Left 1; [1: by auto => /# | 2:done]. 
          by call(:true; time []); auto => />; smt (cf2_pos).
        match Right 1; [1: by auto => /# | 2:done].
        by call(:true; time []); auto => /> /#.
      + proc; exlim o => -[] oi.
        + match Left 1; [1: by auto => /# | 2:done]. 
          by wp; call(:true; time []); auto => />; smt (cf2_pos).
        match Right 1; [1: by auto => /# | 2:done].
        by wp; call(:true; time []); auto => /> /#.
      + proc; exlim m => -[] mi.
        + match Left 1; [1: by auto => /# | 2:done]. 
          by call(:true; time []); auto => />; smt (cf2_pos).
        match Right 1; [1: by auto => /# | 2:done].
        by call(:true; time []); auto => /> /#.
      + proc; exlim m => -[] mi.
        + match Left 1; [1: by auto => /# | 2:done]. 
          by wp; call(:true; time []); auto => />; smt (cf2_pos).
        match Right 1; [1: by auto => /# | 2:done].
        by wp; call(:true; time []); auto => /> /#.
      call(:true; time []); skip => />.
      rewrite !bigi_constz /=; smt(cz_pos cf2_pos).
    qed.
  end section.
  end C.

end PARA_RI.
