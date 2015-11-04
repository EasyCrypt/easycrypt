(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2015 - IMDEA Software Institute
 * Copyright (c) - 2012--2015 - Inria
 * 
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
require import StdRing Int Real.
require (*--*) Number.

(* -------------------------------------------------------------------- *)
theory IntOrder.
clone include Number
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

lemma lezWP (z1 z2 : int) : (z1 <= z2) || (z2 <= z1).
proof. by case: (z1 <= z2)=> //=; rewrite -ltzNge => /ltrW. qed.
end IntOrder.
  
(* -------------------------------------------------------------------- *)
clone Number as RealOrder
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
