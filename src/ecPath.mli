(* -------------------------------------------------------------------- *)
open EcMaps
open EcSymbols

(* -------------------------------------------------------------------- *)
(* We distinguish 3 kinds of paths:
 * - [path] is the type of paths without functor applications. It is
 *   designed to uniquely designate objects definition. Lookups using
 *   paths are possible and lead to [suspended objects], i.e. object
 *   definitions under a set of module parameters.
 *
 * - [mpath] is the type of paths of fully applied module when these ones
 *   are used as container. It is defined as a [path] and the list of
 *   functor application parameters.
 *
 * - [xpath] is the type of paths for concrete objects. It is defined as
 *   a [mpath] (the container path) and a [symbol] (the name of the
 *   object in the container). (FIXME: Currently unused)
 *)

(* -------------------------------------------------------------------- *)
type path = private {
  p_node : path_node;
  p_tag  : int
}

and path_node =
| Psymbol of symbol
| Pident  of EcIdent.t
| Pqname  of path * symbol

type proot = [ `Symbol of symbol | `Ident of EcIdent.t ]

(* -------------------------------------------------------------------- *)
val psymbol   : symbol -> path
val pident    : EcIdent.t -> path
val pqname    : path -> symbol -> path

val p_equal   : path -> path -> bool
val p_compare : path -> path -> int
val p_hash    : path -> int
val p_fv      : int EcIdent.Mid.t -> path -> int EcIdent.Mid.t

(* -------------------------------------------------------------------- *)
val tostring  : path -> string
val toqsymbol : path -> qsymbol
val basename  : path -> symbol
val prefix    : path -> path option
val rootname  : path -> symbol
val extend    : path option -> symbol -> path
val tolist    : path -> symbol list 
val p_size    : path -> int

(* -------------------------------------------------------------------- *)
module Mp : Map.S  with type key = path
module Sp : Mp.Set with type elt = path
module Hp : EcMaps.EHashtbl.S with type key = path

(* -------------------------------------------------------------------- *)
type path_kind =
| PKmodule
| PKother

type mpath = private {
  m_path : path;
  m_kind : path_kind list; 
  m_args : mpath list list;
  m_tag  : int;
}

val name_path : path -> symbol (* ? *)
val name_mpath : mpath -> symbol (* ? *)

(* -------------------------------------------------------------------- *)
val mpath   : path -> path_kind list -> mpath list list -> mpath
val mident  : EcIdent.t -> mpath
val msymbol : symbol -> mpath
val mqname  : mpath -> path_kind -> symbol -> mpath list -> mpath

val m_equal   : mpath -> mpath -> bool
val m_compare : mpath -> mpath -> int
val m_hash    : mpath -> int

val m_split : mpath -> (mpath * path_kind * symbol * mpath list) option
val m_apply : mpath -> mpath list -> mpath

val m_fv    : int EcIdent.Mid.t -> mpath -> int EcIdent.Mid.t

(* -------------------------------------------------------------------- *)
type xpath = private {
  xp_node : mpath * symbol;
  xp_tag  : int;
}

(* -------------------------------------------------------------------- *)
val xpath   : mpath -> symbol -> xpath
val x_name  : xpath -> symbol
val x_scope : xpath -> mpath

val x_equal   : xpath -> xpath -> bool
val x_compare : xpath -> xpath -> int
val x_hash    : xpath -> int

(* -------------------------------------------------------------------- *)

(* Create a [mpath] from a [path] assuming that all components are
 * non-applied (i.e. applied to an empty list of arguments *)
val mpath_of_path : path  -> mpath 

(* Project a [mpath] to is associated [path], [arguments] and [kinds] *)
val path_of_mpath  : mpath -> path
val args_of_mpath  : mpath -> mpath list list
val kinds_of_mpath : mpath -> path_kind list

(* -------------------------------------------------------------------- *)

(* [mpath/xpath] dump *)
val m_tostring : mpath -> string
val x_tostring : xpath -> string

(* -------------------------------------------------------------------- *)
module Mm : Map.S   with type key = mpath
module Sm : Mm.Set with type elt = mpath
module Hm : EcMaps.EHashtbl.S with type key = mpath

(* -------------------------------------------------------------------- *)
val p_subst : path Mp.t -> path -> path

val m_subst : (path -> path) -> mpath EcIdent.Mid.t -> mpath -> mpath

(* -------------------------------------------------------------------- *)
module Msubp : sig
  (* Maps implementation with [path] as keys. When asking the value of
   * a [path], retrieve the longest prefix of [path] that has been
   * associated to a value, and return this one. It is an error to give
   * paths prefixed by an [ident] to any of these functions. *)

  type +'a t

  val empty : 'a t
  val add   : path -> 'a -> 'a t -> 'a t
  val find  : path -> 'a t -> 'a option
end
