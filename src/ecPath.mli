(* -------------------------------------------------------------------- *)
open EcIdent
open EcMaps
open EcSymbols

(* -------------------------------------------------------------------- *)
type path = private {
  p_node : path_node;
  p_tag  : int
}

and path_node =
| Psymbol of symbol
| Pqname  of path * symbol

(* -------------------------------------------------------------------- *)
val psymbol : symbol -> path
val pqname  : path -> symbol -> path

val p_equal   : path -> path -> bool
val p_compare : path -> path -> int
val p_hash    : path -> int

(* -------------------------------------------------------------------- *)
val tostring  : path -> string
val toqsymbol : path -> qsymbol
val basename  : path -> symbol
val prefix    : path -> path option
val rootname  : path -> symbol
val tolist    : path -> symbol list 
val p_size    : path -> int

(* -------------------------------------------------------------------- *)
module Mp : Map.S  with type key = path
module Sp : Mp.Set with type elt = path
module Hp : EcMaps.EHashtbl.S with type key = path

(* -------------------------------------------------------------------- *)
type mpath = private {
  m_top  : mpath_top;
  m_args : mpath list;
  m_tag  : int;
}

and mpath_top =
[ | `Abstract of ident
  | `Concrete of path * path option ]

(* -------------------------------------------------------------------- *)
val mpath     : mpath_top -> mpath list -> mpath
val mpath_abs : ident -> mpath list -> mpath
val mqname    : mpath -> symbol -> mpath

val mident    : ident -> mpath
val mpath_crt : path -> mpath list -> path option -> mpath

val m_equal   : mpath -> mpath -> bool
val mt_equal  : mpath_top -> mpath_top -> bool
val m_compare : mpath -> mpath -> int
val m_hash    : mpath -> int
val m_apply   : mpath -> mpath list -> mpath
val m_fv : int EcIdent.Mid.t -> mpath -> int EcIdent.Mid.t

(* -------------------------------------------------------------------- *)
type xpath = private {
  x_top : mpath;
  x_sub : path;
  x_tag : int;
}

val xpath : mpath -> path -> xpath
val xqname : xpath -> symbol -> xpath

val x_equal   : xpath -> xpath -> bool
(* This function make sense only var xpath representing a program variable 
   and if the mpath (x_top) is in normal form *)
val x_equal_na : xpath -> xpath -> bool
val x_compare : xpath -> xpath -> int
val x_hash    : xpath -> int

val x_fv : int EcIdent.Mid.t -> xpath -> int EcIdent.Mid.t

(* -------------------------------------------------------------------- *)
val m_tostring : mpath -> string
val x_tostring : xpath -> string

(* -------------------------------------------------------------------- *)
module Mm : Map.S   with type key = mpath
module Sm : Mm.Set with type elt = mpath
module Hm : EcMaps.EHashtbl.S with type key = mpath

(* -------------------------------------------------------------------- *)
module Mx : Map.S   with type key = xpath
module Sx : Mx.Set with type elt = xpath
module Hx : EcMaps.EHashtbl.S with type key = xpath

(* -------------------------------------------------------------------- *)
val p_subst : path Mp.t -> path -> path

val m_subst : (path -> path) -> mpath Mid.t -> mpath -> mpath
val x_subst : (mpath -> mpath) -> xpath -> xpath
val x_substm : (path -> path) -> mpath Mid.t -> xpath -> xpath
