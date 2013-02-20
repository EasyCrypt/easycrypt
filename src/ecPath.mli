(* -------------------------------------------------------------------- *)
open EcMaps
open EcSymbols

(* -------------------------------------------------------------------- *)
type path = private {
  p_node : path_desc;
  p_tag  : int
}

and path_desc =
| Pident of symbol
| Pqname of path * symbol

val p_equal   : path -> path -> bool
val p_compare : path -> path -> int
val p_hash    : path -> int

val pident : symbol -> path
val pqname : path * symbol -> path

module Mp : Map.S  with type key = path
module Sp : Mp.Set with type elt = path

val p_tostring  : path -> string
val p_tolist    : path -> symbol list
val p_toqsymbol : path -> qsymbol
val p_prefix    : path -> path option
val p_basename  : path -> symbol

(* -------------------------------------------------------------------- *)
type mpath = private {
  mp_node : mpath_desc;
  mp_tag  : int;
}

and mpath_desc =
| MCtop of topmcsymbol
| MCDot of mpath * mcsymbol

and mcsymbol    = symbol    * mpath list
and topmcsymbol = topsymbol * mpath list

and topsymbol =
| TopIdent  of EcIdent.t
| TopSymbol of symbol

val mp_equal   : mpath -> mpath -> bool
val mp_compare : mpath -> mpath -> int
val mp_hash    : mpath -> int

val mtop : mcsymbol -> mpath
val mdot : mpath * mcsymbol -> mpath

module Mmp : Map.S   with type key = mpath
module Smp : Mmp.Set with type elt = mpath

val mp_tostring : mpath -> string

(* -------------------------------------------------------------------- *)
type xpath = private {
  xp_node : xpath_desc;
  xp_tag  : int;
}

and xpath_desc = {
  xp_context : mpath;
  xp_symbol  : symbol;
}

val xp_equal   : xpath -> xpath -> bool
val xp_compare : xpath -> xpath -> int
val xp_hash    : xpath -> int

val xpath : mpath -> symbol -> xpath

module Mxp : Map.S   with type key = xpath
module Sxp : Mxp.Set with type elt = xpath

val xp_tostring : xpath -> string
