(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2021 - Inria
 * Copyright (c) - 2012--2021 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcSymbols
open EcParsetree
open EcCoreGoal.FApi

(* -------------------------------------------------------------------- *)
module Low : sig
  val t_hoare_rcond   : bool -> codepos1 -> backward
  val t_bdhoare_rcond : bool -> codepos1 -> backward
  val t_equiv_rcond   : side -> bool -> codepos1 -> backward
end

(* -------------------------------------------------------------------- *)
module LowMatch : sig
  val t_hoare_rcond_match   : symbol -> codepos1 -> backward
  val t_bdhoare_rcond_match : symbol -> codepos1 -> backward
  val t_equiv_rcond_match   : side -> symbol -> codepos1 -> backward
end

(* -------------------------------------------------------------------- *)
val t_rcond : oside -> bool -> codepos1 -> backward
val t_rcond_match : oside -> symbol -> codepos1 -> backward
