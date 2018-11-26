(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcParsetree
open EcFol
open EcCoreGoal.FApi

(* -------------------------------------------------------------------- *)
val t_hr_exists_elim  : backward
val t_hr_exists_intro : form list -> backward

(* -------------------------------------------------------------------- *)
val process_exists_intro : elim:bool -> pformula list -> backward
val process_ecall : oside -> pqsymbol * ptyannot option * pformula list -> backward
