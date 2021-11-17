(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2021 - Inria
 * Copyright (c) - 2012--2021 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcParsetree
open EcMatching


(* -------------------------------------------------------------------- *)
val default_start_name : string
val default_end_name   : string
val default_name       : string

(* -------------------------------------------------------------------- *)
val trans_stmt : pim_regexp -> regexp_instr

val trans_block : pim_block -> regexp_instr
