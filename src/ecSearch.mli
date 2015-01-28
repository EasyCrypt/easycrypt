(* -------------------------------------------------------------------- *)
open EcPath
open EcFol
open EcTyping

(* -------------------------------------------------------------------- *)
type search = [
  | `ByPath    of path
  | `ByPattern of ((ptnmap * EcUnify.unienv) * form)
]

val search : EcEnv.env -> search list -> (path * EcDecl.axiom) list
