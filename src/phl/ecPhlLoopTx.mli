(* --------------------------------------------------------------------
 * Copyright (c) - 2012-2014 - IMDEA Software Institute and INRIA
 * Distributed under the terms of the CeCILL-C license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcParsetree
open EcTypes
open EcCoreGoal.FApi

(* -------------------------------------------------------------------- *)
type fission_t    = bool option * codepos * (int * (int * int))
type fusion_t     = bool option * codepos * (int * (int * int))
type unroll_t     = bool option * codepos
type splitwhile_t = pexpr * bool option * codepos

val t_fission    : bool option -> codepos -> int * (int * int) -> backward
val t_fusion     : bool option -> codepos -> int * (int * int) -> backward
val t_unroll     : bool option -> codepos -> backward
val t_splitwhile : expr -> bool option -> codepos -> backward


(* -------------------------------------------------------------------- *)
val process_fission    : fission_t -> backward
val process_fusion     : fusion_t -> backward
val process_unroll     : unroll_t -> backward
val process_splitwhile : splitwhile_t -> backward
