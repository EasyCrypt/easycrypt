(* -------------------------------------------------------------------- *)
open Types

(* -------------------------------------------------------------------- *)
(* TODO: change 'a this scope *)

exception CanNotUnify of ty * ty

val unify : 'a -> ty UidGen.Muid.t -> ty -> ty -> ty UidGen.Muid.t
