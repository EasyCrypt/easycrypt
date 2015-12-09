(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2015 - IMDEA Software Institute
 * Copyright (c) - 2012--2015 - Inria
 * 
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
require import Ring StdRing Int Real.
require (*--*) Number.

(* -------------------------------------------------------------------- *)
theory IntOrder.
clone include Number.RealDomain
  with type t <- int,

  pred Domain.unit (z : int) <- (z = 1 \/ z = -1),
  op   Domain.zeror  <- 0,
  op   Domain.oner   <- 1,
  op   Domain.( + )  <- Int.( + ),
  op   Domain.([-])  <- Int.([-]),
  op   Domain.( * )  <- Int.( * ),
  op   Domain.( / )  <- Int.( * ),
  op   Domain.invr   <- (fun (z : int) => z),
  op   Domain.intmul <- IntID.intmul,
  op   Domain.ofint  <- IntID.ofint,
  op   Domain.exp    <- IntID.exp,

  op   "`|_|" <- Int."`|_|",
  op   ( <= ) <- Int.(<=),
  op   ( <  ) <- Int.(< )

  proof Domain.* by smt, Axioms.* by smt

  remove abbrev Domain.(-).
end IntOrder.
  
(* -------------------------------------------------------------------- *)
clone Number.RealField as RealOrder
  with type t <- real,

  op   Field.zeror  <- 0%r,
  op   Field.oner   <- 1%r,
  op   Field.( + )  <- Real.( + ),
  op   Field.([-])  <- Real.([-]),
  op   Field.( * )  <- Real.( * ),
  op   Field.( / )  <- Real.( / ),
  op   Field.invr   <- Real.inv,
  op   Field.intmul <- RField.intmul,
  op   Field.ofint  <- RField.ofint,
  op   Field.exp    <- RField.exp,

  op   "`|_|" <- Real.Abs."`|_|",
  op   ( <= ) <- Real.(<=),
  op   ( <  ) <- Real.(< )

  proof Field.* by smt, Axioms.* by smt full

  remove abbrev Field.(-).
