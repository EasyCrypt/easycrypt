(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
require (*--*) Ring.
require export Core Int Real Xint.
(*---*) export Ring.IntID.

(* -------------------------------------------------------------------- *)
schema cost_oget ['a] `{P} {o: 'a option} : 
  cost [P : oget o] = cost [P:o] + N 1.
hint simplify cost_oget.

(* Cost on integer operations *)
op cincr : int -> int.
op ceqint : int -> int.
op cltint : int -> int.
op cleint : int -> int.

axiom ge0_cincr m  : 0 <= cincr m.
axiom ge0_ceqint m : 0 <= ceqint m.
axiom ge0_cltint m : 0 <= cltint m.
axiom ge0_cleint m : 0 <= cleint m.

schema cost_incr {n:int} (m:int) : cost[`|n| <= m : n + 1] = cost[true:n] + N (cincr m).

schema cost_eqint {n1 n2:int} (m:int) : 
  cost[`|n1| <= m /\ `|n2| <= m : n1 = n2] = cost[true:n1] + cost[true:n2] + N (ceqint m).

schema cost_ltint {n1 n2:int} (m:int) : 
  cost[`|n1| <= m /\ `|n2| <= m : n1 < n2] = cost[true:n1] + cost[true:n2] + N (cltint m).

schema cost_leint {n1 n2:int} (m:int) : 
  cost[`|n1| <= m /\ `|n2| <= m : n1 < n2] = cost[true:n1] + cost[true:n2] + N (cleint m).


hint simplify cost_incr, cost_eqint, cost_ltint, cost_leint.
