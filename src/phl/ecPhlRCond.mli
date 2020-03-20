(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcParsetree
open EcCoreGoal.FApi

(* -------------------------------------------------------------------- *)
module Low : sig
  val t_hoare_rcond   : bool -> codepos1 -> backward
  val t_bdhoare_rcond : bool -> codepos1 -> backward
  val t_equiv_rcond   : side -> bool -> codepos1 -> backward
end

(* -------------------------------------------------------------------- *)
val t_rcond : oside -> bool -> codepos1 -> backward
