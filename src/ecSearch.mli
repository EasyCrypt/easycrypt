(* -------------------------------------------------------------------- *)
open EcPath
open EcFol
open EcTyping

(* -------------------------------------------------------------------- *)
type search = [
  | `ByPath    of Sp.t
  | `ByPattern of ((ptnmap * EcUnify.unienv) * form)
]

val search : EcEnv.env -> search list -> (path * EcDecl.axiom) list
