require NewBigop.


(* -------------------------------------------------------------------- *)
require import Int.

clone NewBigop as BIA with
  type t <- int,
  op Support.idm <- 0,
  op Support.(+)  <- Int.( + )
  proof Support.Axioms.* by (delta;smt).

clone NewBigop as BIM with
  type t <- int,
  op Support.idm <- 1,
  op Support.(+)  <- Int.( * )
  proof Support.Axioms.* by (delta;smt).


(* -------------------------------------------------------------------- *)
require import Real.

clone NewBigop as BRA with
  type t <- real,
  op Support.idm <- 0%r,
  op Support.(+)  <- Real.( + )
  proof Support.Axioms.* by (delta;smt).

clone NewBigop as BRM with
  type t <- real,
  op Support.idm <- 1%r,
  op Support.(+)  <- Real.( * )
  proof Support.Axioms.* by (delta;smt).

(* -------------------------------------------------------------------- *)
require import Bool.

clone NewBigop as BBA with
  type t <- bool,
  op Support.idm <- false,
  op Support.(+)  <- Bool.( ^^ )
  proof Support.Axioms.* by (delta;smt).  

clone NewBigop as BBM with
  type t <- bool,
  op Support.idm <- true,
  op Support.(+)  <- Pervasive.( /\ )
  proof Support.Axioms.* by (delta;smt).  
