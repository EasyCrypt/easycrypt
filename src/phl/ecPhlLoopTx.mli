(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2015 - IMDEA Software Institute
 * Copyright (c) - 2012--2015 - Inria
 * 
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcParsetree
open EcTypes
open EcCoreGoal.FApi

(* -------------------------------------------------------------------- *)
type fission_t    = oside * codepos * (int * (int * int))
type fusion_t     = oside * codepos * (int * (int * int))
type unroll_t     = oside * codepos
type splitwhile_t = pexpr * oside * codepos

val t_fission    : oside -> codepos -> int * (int * int) -> backward
val t_fusion     : oside -> codepos -> int * (int * int) -> backward
val t_unroll     : oside -> codepos -> backward
val t_splitwhile : expr -> oside -> codepos -> backward


(* -------------------------------------------------------------------- *)
val process_fission    : fission_t -> backward
val process_fusion     : fusion_t -> backward
val process_unroll     : unroll_t -> backward
val process_splitwhile : splitwhile_t -> backward
