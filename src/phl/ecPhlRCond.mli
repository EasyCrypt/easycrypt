(* --------------------------------------------------------------------
 * Copyright (c) - 2012-2014 - IMDEA Software Institute and INRIA
 * Distributed under the terms of the CeCILL-C license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcCoreGoal.FApi

(* -------------------------------------------------------------------- *)
module Low : sig
  val t_hoare_rcond   : bool -> int -> backward
  val t_bdhoare_rcond : bool -> int -> backward
  val t_equiv_rcond   : bool -> bool -> int -> backward
end

(* -------------------------------------------------------------------- *)
val t_rcond : bool option -> bool -> int -> backward
