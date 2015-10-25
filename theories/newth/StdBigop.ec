(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2015 - IMDEA Software Institute
 * Copyright (c) - 2012--2015 - Inria
 * 
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
require import Pred Int IntExtra Real Ring List.
require (*--*) NewBigop NewBigalg.

(* -------------------------------------------------------------------- *)
theory BIA.
clone include NewBigalg with
  type t <- int,
  op ZM.zeror <- 0,
  op ZM.( + ) <- Int.(+),
  op ZM.( - ) <- Int.(-),
  op ZM.([-]) <- Int.([-])
  proof ZM.* by smt.

  lemma nosmt sumzE ss : sumz ss = BIA.big predT (fun x => x) ss.
  proof. by elim: ss=> [|s ss ih] //=; rewrite BIA.big_cons -ih. qed.
      
  lemma nosmt big_constz (P : 'a -> bool) x s:
    big P (fun i => x) s = x * (count P s).
  proof.
    rewrite big_const -Support.iteropE -IntID.intmulpE.
    by apply/count_ge0. by rewrite IntID.intmulz mulzC.
  qed.  
end BIA.

clone NewBigop as BIM with
  type t <- int,
  op Support.idm <- 1,
  op Support.(+) <- Int.( * )
  proof Support.Axioms.* by smt.

(* -------------------------------------------------------------------- *)
clone NewBigalg as BRA with
  type t <- real,
  op ZM.zeror <- 0%r,
  op ZM.( + ) <- Real.(+),
  op ZM.( - ) <- Real.(-),
  op ZM.([-]) <- Real.([-])
  proof ZM.* by smt.

clone NewBigop as BRM with
  type t <- real,
  op Support.idm <- 1%r,
  op Support.(+) <- Real.( * )
  proof Support.Axioms.* by smt.

(* -------------------------------------------------------------------- *)
require import Bool.

clone NewBigop as BBA with
  type t <- bool,
  op Support.idm <- false,
  op Support.(+) <- Bool.( ^^ )
  proof Support.Axioms.* by (delta; smt).  

clone NewBigop as BBM with
  type t <- bool,
  op Support.idm <- true,
  op Support.(+) <- Pervasive.( /\ )
  proof Support.Axioms.* by (delta; smt).  

clone NewBigop as BBO with
  type t <- bool,
  op Support.idm <- false,
  op Support.(+) <- Pervasive.( || )
  proof Support.Axioms.* by (delta; smt).  
