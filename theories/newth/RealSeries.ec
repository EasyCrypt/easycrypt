(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2015 - IMDEA Software Institute
 * Copyright (c) - 2012--2015 - Inria
 * 
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
require import Bool Option Fun Distr Int IntExtra Real RealExtra.
require import StdRing StdOrder StdBigop NewList RealSeq.
(*---*) import IterOp BRA.

pragma +implicits.

(* -------------------------------------------------------------------- *)
op partial (s : int -> real) (n : int) : real =
  BRA.bigi predT s 0 n.

pred convergeto (s : int -> real) (x : real) =
  RealSeq.convergeto (partial s) x.
