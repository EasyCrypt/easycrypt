(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2016 - Inria
 * 
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

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
val sort : Sp.t -> (path * EcDecl.axiom) list -> (path * EcDecl.axiom) list
