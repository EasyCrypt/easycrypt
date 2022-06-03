(* -------------------------------------------------------------------- *)
open EcPath
open EcFol
open EcTyping

(* -------------------------------------------------------------------- *)

type pattern = (ptnmap * EcUnify.unienv) * form

type search = [
  | `ByPath    of Sp.t
  | `ByPattern of pattern
  | `ByOr      of search list
]

type search_result =
  (path * [`Axiom of EcDecl.axiom | `Schema of EcDecl.ax_schema]) list

val search : EcEnv.env -> search list -> search_result

val sort : Sp.t -> search_result -> search_result
