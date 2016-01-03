(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2016 - Inria
 * 
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcUtils
open EcParsetree
open EcTypes
open EcFol
open EcCoreGoal.FApi

(* -------------------------------------------------------------------- *)
type bhl_infos_t = (form, ty -> form option, ty -> form) rnd_tac_info
type rnd_infos_t = (pformula, pformula option, pformula) rnd_tac_info
type mkbij_t     = EcTypes.ty -> EcTypes.ty -> EcFol.form

(* -------------------------------------------------------------------- *)
val wp_equiv_disj_rnd : side -> backward
val wp_equiv_rnd      : (mkbij_t pair) option -> backward

(* -------------------------------------------------------------------- *)
val t_hoare_rnd   : backward
val t_bdhoare_rnd : bhl_infos_t -> backward
val t_equiv_rnd   : oside -> (mkbij_t option) pair -> backward

(* -------------------------------------------------------------------- *)
val process_rnd : oside -> rnd_infos_t -> backward
