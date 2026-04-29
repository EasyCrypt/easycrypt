(* -------------------------------------------------------------------- *)
open EcAst
open EcDecl
open EcEnv

(* -------------------------------------------------------------------- *)
val infer : env -> ty -> typeclass -> tcwitness option

(* -------------------------------------------------------------------- *)
(* Flatten the parent chain: [tc; tc.parent; tc.grandparent; ...].
   Args are substituted along the chain. *)
val ancestors : env -> typeclass -> typeclass list
