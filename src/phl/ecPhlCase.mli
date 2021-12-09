(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2021 - Inria
 * Copyright (c) - 2012--2021 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcFol
open EcCoreGoal.FApi

(* -------------------------------------------------------------------- *)
val t_hoare_case   : ?simplify:bool -> form -> backward
val t_choare_case  : ?simplify:bool -> form -> backward
val t_bdhoare_case : ?simplify:bool -> form -> backward
val t_equiv_case   : ?simplify:bool -> form -> backward

val t_hl_case : ?simplify:bool -> form -> backward
