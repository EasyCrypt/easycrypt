(* -------------------------------------------------------------------- *)
open EcUtils
open EcParsetree
open EcCoreGoal.FApi

(* -------------------------------------------------------------------- *)
type i_pat =
  | IPpat
  | IPif    of s_pat pair
  | IPwhile of s_pat
  | IPmatch of s_pat list

and s_pat = (int * i_pat) list

(* -------------------------------------------------------------------- *)
val t_inline_bdhoare : use_tuple:bool -> s_pat -> backward
val t_inline_hoare   : use_tuple:bool -> s_pat -> backward
val t_inline_equiv   : use_tuple:bool -> side  -> s_pat -> backward

(* -------------------------------------------------------------------- *)
val process_inline : inline_info -> backward
