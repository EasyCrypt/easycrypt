(* -------------------------------------------------------------------- *)
open EcMaps
open EcSymbols

(* -------------------------------------------------------------------- *)
(* An epath is either
 * - A [EPath EcPath.path] that denotes a full path from the <top> context.
 *   For a given environment, it is ensured that such a path
 *   denotes at most a single object. Environment also ensures that two
 *   containers of different kind (e.g. theory/module) cannot be denoted
 *   by the same path.
 * - A [EModule EcIdent.t path] that denotes a (possibly empty) path prefixed
 *   by a bound module parameter. Two different modules parameters can share
 *   the same name but must have different UID.
 *)

type path = 
  | Pident of symbol
  | Pqname of path * symbol

type epath =
| EPath   of path
| EModule of EcIdent.t * symbol option

type cref =
| CRefPath of path                      (* Top-level component    *)
| CRefMid  of EcIdent.t                 (* Bound module component *)

type xcref = cref * xcref list

(* -------------------------------------------------------------------- *)
val p_equal   : path -> path -> bool
val p_compare : path -> path -> int

val ep_equal   : epath -> epath -> bool
val ep_compare : epath -> epath -> int

val cref_equal  : cref -> cref -> bool
val xcref_equal : xcref -> xcref -> bool


(* -------------------------------------------------------------------- *)
val tostring      : path  -> string
val ep_tostring   : epath -> string
val cref_tostring : cref  -> string

(* -------------------------------------------------------------------- *)
val create    : string -> path
val toqsymbol : path -> qsymbol
val basename  : path -> symbol
val prefix    : path -> path option
val rootname  : path -> symbol
val extend    : path option -> symbol -> path
val concat    : path -> path -> path
val tolist    : path -> symbol list 

(* -------------------------------------------------------------------- *)
module Mp : Map.S  with type key = path
module Sp : Mp.Set with type elt = path

module Mep : Map.S   with type key = epath
module Sep : Mep.Set with type elt = epath

(* -------------------------------------------------------------------- *)
module Msubp : sig
  (* Maps implementation with [path] as keys. When asking the value of
   * a [path], retrieve the longest prefix of [path] that has been
   * associated to a value, and return this one. *)

  type +'a t

  val empty : 'a t
  val add   : path -> 'a -> 'a t -> 'a t
  val find  : path -> 'a t -> 'a option
end
