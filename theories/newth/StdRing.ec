(* --------------------------------------------------------------------
 * Copyright (c) - 2012-2015 - IMDEA Software Institute and INRIA
 * Distributed under the terms of the CeCILL-B licence.
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
require import NewLogic Int Real.
require (*--*) Ring.

(* -------------------------------------------------------------------- *)
axiom invr0: inv 0%r = 0%r.
axiom divr0: forall x, x / 0%r = 0%r.

(* -------------------------------------------------------------------- *)
clone Ring.Field as RField with
  type t <- real,
  op   zeror <- 0%r,
  op   oner  <- 1%r,
  op   ( + ) <- Real.( + ),
  op   [ - ] <- Real.([-]),
  op   ( - ) <- Real.( - ),
  op   ( * ) <- Real.( * ),
  op   ( / ) <- Real.( / ),
  op   invr  <- Real.inv
  proof * by smt.
