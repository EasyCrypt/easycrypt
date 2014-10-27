(* --------------------------------------------------------------------
 * Copyright (c) - 2012-2014 - IMDEA Software Institute and INRIA
 * Distributed under the terms of the CeCILL-C license
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
