(* -------------------------------------------------------------------- *)
open EcPath
open EcFol
open EcTyping

(* -------------------------------------------------------------------- *)

type pattern = (ptnmap * EcUnify.unienv) * form

type search = [
  | `ByPath    of Sp.t 
  | `ByPattern of pattern
]

val search : EcEnv.env -> search list -> (path * EcDecl.axiom) list
