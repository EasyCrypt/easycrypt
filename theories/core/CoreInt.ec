(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
op zero   : int = 0.
op one    : int = 1.
op lt     : int -> int -> bool.
op le     = fun x y => lt x y \/ x = y.
op add    : int -> int -> int.
op opp    : int -> int.
op mul    : int -> int -> int.
op absz   = fun x => (le 0 x) ? x : opp x.

axiom nosmt intind (p:int -> bool):
  (p 0) =>
  (forall i, le 0 i => p i => p (add i 1)) =>
  (forall i, le 0 i => p i).
