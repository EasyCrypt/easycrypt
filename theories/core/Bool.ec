(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
require import Int.
require FinType.

op (^^) (b1 b2:bool) = b1 = !b2.

lemma nosmt xor_false b: b ^^ false = b
by [].

lemma nosmt xor_true b: b ^^ true = !b
by [].

lemma nosmt xorA b1 b2 b3: (b1 ^^ b2) ^^ b3 = b1 ^^ (b2 ^^ b3)
by [].

lemma nosmt xorC b1 b2: b1 ^^ b2 = b2 ^^ b1
by [].

lemma nosmt xorK b: b ^^ b = false
by [].

clone FinType as BoolFin with
  type t    <- bool,
  op enum <- List.(::) true (List.(::) false List."[]"),
  op card <- 2
proof enum_spec by case.

schema cost_eqbool `{P} {b1 b2:bool} : cost [P: b1 = b2] = cost[P:b1] + cost[P:b2] + 1.
hint simplify cost_eqbool.