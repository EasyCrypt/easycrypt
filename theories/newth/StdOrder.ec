(* --------------------------------------------------------------------
 * Copyright (c) - 2012-2015 - IMDEA Software Institute and INRIA
 * Distributed under the terms of the CeCILL-B licence.
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
require import StdRing Int Real.
require (*--*) NewNumber.

(* -------------------------------------------------------------------- *)
clone NewNumber as IntOrder
  with type t <- int,

  (* FIXME: should use theory substitution *)
  pred Domain.unit (z : int) <- (z = 1 \/ z = -1),
  op   Domain.zeror <- 0,
  op   Domain.oner  <- 1,
  op   Domain.( + ) <- Int.( + ),
  op   Domain.([-]) <- Int.([-]),
  op   Domain.( - ) <- Int.( - ),
  op   Domain.( * ) <- Int.( * ),
  op   Domain.( / ) <- Int.( * ),
  op   Domain.invr  <- (fun (z : int) => z),

  op   "`|_|" <- Int."`|_|",
  op   ( <= ) <- Int.(<=),
  op   ( <  ) <- Int.(< )

  proof Domain.* by smt, Axioms.* by smt.

(* -------------------------------------------------------------------- *)
clone NewNumber as RealOrder
  with type t <- real,

  (* FIXME: should use theory substitution *)
  pred Domain.unit (z : real) <- (z <> 0%r),
  op   Domain.zeror <- 0%r,
  op   Domain.oner  <- 1%r,
  op   Domain.( + ) <- Real.( + ),
  op   Domain.([-]) <- Real.([-]),
  op   Domain.( - ) <- Real.( - ),
  op   Domain.( * ) <- Real.( * ),
  op   Domain.( / ) <- Real.( / ),
  op   Domain.invr  <- Real.inv,

  op   "`|_|" <- Real.Abs."`|_|",
  op   ( <= ) <- Real.(<=),
  op   ( <  ) <- Real.(< )

  proof Domain.* by smt, Axioms.* by smt full.
