(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2015 - IMDEA Software Institute
 * Copyright (c) - 2012--2015 - Inria
 * 
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcUtils
open EcParsetree
open EcCoreGoal.FApi

(* -------------------------------------------------------------------- *)
type i_pat =
  | IPpat
  | IPif    of s_pat pair
  | IPwhile of s_pat

and s_pat = (int * i_pat) list

(* -------------------------------------------------------------------- *)
val t_inline_bdhoare : s_pat -> backward
val t_inline_hoare   : s_pat -> backward
val t_inline_equiv   : side  -> s_pat -> backward

(* -------------------------------------------------------------------- *)
val process_inline : inline_info -> backward
