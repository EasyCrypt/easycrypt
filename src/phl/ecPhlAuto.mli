(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcSymbols
open EcCoreGoal.FApi

(* -------------------------------------------------------------------- *)
val t_exfalso     : backward
val t_phl_trivial : backward
val t_pl_trivial  : ?bases:symbol list -> backward
val t_auto        : backward
