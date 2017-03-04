(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2017 - Inria
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcParsetree
open EcCoreGoal.FApi

(* -------------------------------------------------------------------- *)
module Low : sig
  val t_hoare_rcond   : bool -> int -> backward
  val t_bdhoare_rcond : bool -> int -> backward
  val t_equiv_rcond   : side -> bool -> int -> backward
end

(* -------------------------------------------------------------------- *)
val t_rcond : oside -> bool -> int -> backward
