(* -------------------------------------------------------------------- *)
open EcMaps
open EcSymbols

(* -------------------------------------------------------------------- *)
type path = private {
  p_node : path_node;
  p_tag  : int
}

and path_node =
| Pident of symbol
| Plocal of EcIdent.t
| Pqname of path * symbol

type mpath = private {
  mp_node : path * mpath list list;
  mp_tag  : int;
}

(* -------------------------------------------------------------------- *)
val psymbol   : symbol -> path
val pident    : EcIdent.t -> path
val pqname    : path * symbol -> path

val p_equal   : path -> path -> bool
val p_compare : path -> path -> int
val p_hash    : path -> int

(* -------------------------------------------------------------------- *)
val mpath   : path -> mpath list list -> mpath
val mident  : EcIdent.t -> mpath
val msymbol : symbol -> mpath
val mqname  : mpath -> symbol -> mpath list -> mpath

val mp_equal   : mpath -> mpath -> bool
val mp_compare : mpath -> mpath -> int
val mp_hash    : mpath -> int

val path_of_mpath : mpath -> path
val args_of_mpath : mpath -> mpath list list

(* -------------------------------------------------------------------- *)
val tostring  : path -> string
val create    : string -> path
val toqsymbol : path -> qsymbol
val basename  : path -> symbol
val prefix    : path -> path option
val rootname  : path -> symbol
val extend    : path option -> symbol -> path
val concat    : path -> path -> path
val tolist    : path -> symbol list 

(* -------------------------------------------------------------------- *)
val mp_tostring : mpath -> string

(* -------------------------------------------------------------------- *)
module Mp : Map.S  with type key = path
module Sp : Mp.Set with type elt = path

module Mmp : Map.S   with type key = mpath
module Smp : Mmp.Set with type elt = mpath
