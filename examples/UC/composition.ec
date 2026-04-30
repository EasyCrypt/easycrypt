require import AllCore Real Distr.
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

op smap (fa:'a -> 'c) (fb:'b -> 'd) (s: ('a, 'b) sum) = 
  with s = Left a  => Left (fa a)
  with s = Right b => Right (fb b).

abstract theory ProtocolType.

(*
     
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

end EXEC_MODEL.

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

end NON_DUMMY.

theory NONDUMMY_EQUIV_DUMMY.

  clone import NON_DUMMY as NON_DUMMY.
  
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

  
  lemma dummy_nondummy (P<:RI.REAL.PROTOCOL) (F<:RI.IDEAL.PROTOCOL) &m eps :
    forall (S<: RI.SIMULATOR {-F}),
      (forall (Z<: RI.REAL.ENV {-P,-F,-S}),
        `| Pr[RI.REAL.UC_emul(Z,P).main() @ &m : res] -
           Pr[RI.REAL.UC_emul(Z,RI.CompS(F,S)).main() @ &m : res] | <= eps) =>
    forall (A<:ADV  {-F, -P, -S}),
      forall (Z<: NONDUMMY_RI.REAL.ENV {-A, -P, -F, -SeqSA, -S}),
        `| Pr[NONDUMMY_RI.REAL.UC_emul(Z,A_PROTOCOL(A,P)).main() @ &m : res] -
           Pr[NONDUMMY_RI.REAL.UC_emul(Z,NONDUMMY_RI.CompS(F,SeqSA(A,S))).main() @ &m : res] | <= eps.
  proof.
    move=> S hS A Z.
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

  lemma nondummy_dummy (P<:RI.REAL.PROTOCOL) (F<:RI.IDEAL.PROTOCOL) &m eps  (Mem <: MEM) (S<: NONDUMMY_RI.SIMULATOR {-F}):
    (forall (A<:ADV) (Z<: NONDUMMY_RI.REAL.ENV {-A, -P, -F, -S}),
        `| Pr[NONDUMMY_RI.REAL.UC_emul(Z,A_PROTOCOL(A,P)).main() @ &m : res] -
           Pr[NONDUMMY_RI.REAL.UC_emul(Z,NONDUMMY_RI.CompS(F,S)).main() @ &m : res] | <= eps) =>
      forall (Z<: RI.REAL.ENV {-P,-F,-S}),
        `| Pr[RI.REAL.UC_emul(Z,P).main() @ &m : res] -
           Pr[RI.REAL.UC_emul(Z,RI.CompS(F,S)).main() @ &m : res] | <= eps.
  proof.
    move=> hA.  
    have /= hS:= hA  (<:DUMMY_A).     
    move=> Z; have := hS Z. 
    have -> : Pr[NONDUMMY_RI.REAL.UC_emul(Z, A_PROTOCOL(DUMMY_A, P)).main() @ &m : res] = 
              Pr[RI.REAL.UC_emul(Z, P).main() @ &m : res].
    + byequiv => //. 
      proc; call (_: ={glob P}).
      + by proc *; inline *; call (:true).
      + by proc *; inline *; call (:true).
      + by proc *; inline *; call (:true); auto.
      + by proc *; inline *; wp; call (:true); auto.
      by inline *; call(:true); auto => /> ?? 4!->.
    have -> // : Pr[NONDUMMY_RI.REAL.UC_emul(Z, NONDUMMY_RI.CompS(F, S)).main() @ &m : res] =
              Pr[RI.REAL.UC_emul(Z, RI.CompS(F, S)).main() @ &m : res].
    byequiv => //.
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
        wp; call (_: true); auto => /> &2; rewrite /get_as_Right /= => rr.
        by case (rr = None) => /#.
      + proc; match; 1,2: smt().
        + move=> m1 m2; wp; inline *; match Left {1} 2; 1: by auto => /#.
          wp; call (_: ={glob Ff}); 1,2:sim; auto => /> ?rr.
          case (rr = None) =>/#.
        move=> m1 m2; wp; inline *; call (_: ={glob Rho, glob Ff}). 
        + proc *; inline *; match Right {1} 3; 1: by auto => /#.
          by call (_: true); auto => /> /#.
        + proc *; inline *; match Right {1} 3; 1: by auto => /#.
          wp; call (_: true); auto => /> ??rr.
          by case (rr = None) => /#.
        by auto => />.
      by swap{1} 2 1; sim />. 
    qed.
 
  end section COMP.

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
          auto; call (_: true);auto => /> ??rr.
          by case (rr = None) => /#.
        by auto => />.
      + proc; match;1,2: smt().
        + move=> m1 m2; inline *; match Left {1} 2; 1: by auto => /> /#.
          wp;call (_: ={glob Ff} ); 1,2:sim.
          auto => /> ?rr.
          by case (rr = None) => /#.
        move=> m1 m2; inline *; wp; call (_: ={glob Rho, glob Ff}). 
        + proc *; inline *; match Right {1} 3; 1: by auto => /> /#.
          by call (_: true); auto => /> /#.
        + proc *; inline *; match Right {1} 3; 1: by auto => /> /#.
          auto; call (_: true);auto => /> ??rr.
          by case (rr = None) => /#.
        by auto => />.
      sim />.
     qed.

  end section StrongCOMP.


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
      wp; call(:true); skip => />rr.
      by case (rr = None) => /#.
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
          wp; call(:true); auto => /> => rr.
          by case (rr = None) => /#.
        wp; call(: ={glob F2, glob F1}); last by auto.
        + by apply F2_step.
        by apply F2_backdoor.
      swap{2} 3 -2; sim />.
    qed.

  end section PROOF.


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
      wp; call(:true); auto => /> rr.
      by case (rr = None) => /#.
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
        wp; call(:true); auto => /> rr.
        by case (rr = None) => /#.
      swap{2} 3 -1; sim />.
    qed.

  end section PROOF.


end PARA_RI.

