(* -------------------------------------------------------------------- *)
open EcMaps
open EcSymbols

(* -------------------------------------------------------------------- *)
type path = private {
  p_node : path_node;
  p_tag  : int
}

and path_node =
| Psymbol of symbol
| Pident  of EcIdent.t
| Pqname  of path * symbol

(* -------------------------------------------------------------------- *)
val psymbol   : symbol -> path
val pident    : EcIdent.t -> path
val pqname    : path * symbol -> path

val p_equal   : path -> path -> bool
val p_compare : path -> path -> int
val p_hash    : path -> int

(* -------------------------------------------------------------------- *)
val tostring  : path -> string
val toqsymbol : path -> qsymbol
val basename  : path -> symbol
val prefix    : path -> path option
val rootname  : path -> symbol
val extend    : path option -> symbol -> path
val tolist    : path -> symbol list 

(* -------------------------------------------------------------------- *)
module Mp : Map.S  with type key = path
module Sp : Mp.Set with type elt = path





(* -------------------------------------------------------------------- *)

type mpath = private {
  m_node : path * mpath list list;
  m_tag  : int;
}

(* -------------------------------------------------------------------- *)
val mpath   : path -> mpath list list -> mpath
val mident  : EcIdent.t -> mpath
val msymbol : symbol -> mpath
val mqname  : mpath -> symbol -> mpath list -> mpath

val m_equal   : mpath -> mpath -> bool
val m_compare : mpath -> mpath -> int
val m_hash    : mpath -> int

(* -------------------------------------------------------------------- *)
val path_of_mpath : mpath -> path
(* mpath_of_path : apply path to the list of empty list*)
val mpath_of_path : path  -> mpath 
val args_of_mpath : mpath -> mpath list list
(* -------------------------------------------------------------------- *)
(* For dump *)
val m_tostring : mpath -> string

(* -------------------------------------------------------------------- *)
module Mm : Map.S   with type key = mpath
module Sm : Mm.Set with type elt = mpath
