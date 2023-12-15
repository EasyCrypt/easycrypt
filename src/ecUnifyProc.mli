open EcTypes
open EcModules
open EcSymbols

(*---------------------------------------------------------------------------------------*)
(* `Unification` of procedures *)
(*
  Given: r <@ foo(a1: t1, a2: t2, ...); and s1; s2; ...; sr.
  Attempt to find values for a1, a2, ... such that, the body of `foo` with a1, a2, ...
  replaced will exactly match s1; s2; ..., and that `r <- res` match sr.
  Where `res` is the return expression of `foo`.

  Currently, this is done by traversing the respective ASTs and when a relevant
  program variable is encountered on the lhs, use the rhs expression.

  FIXME: This is incredibly basic and should be iterated on with a more advanced
  procedure unification algorithm.
 *)

(*---------------------------------------------------------------------------------------*)
type u_error =
  | UE_InvalidRetInstr
  | UE_UnexpectedReturn
  | UE_ExprNotInLockstep of expr * expr
  | UE_InstrNotInLockstep of instr * instr
  | UE_DifferentProgramLengths of stmt * stmt

exception UnificationError of u_error

(*---------------------------------------------------------------------------------------*)
type u_value =
  | Empty
  | Fixed of expr

type umap = u_value Msym.t

(*---------------------------------------------------------------------------------------*)
(* The following functions attempt to unify unknown program variables
   in the lhs with expressions from the rhs *)
val unify_exprs : umap -> expr -> expr -> umap
val unify_instrs : umap -> instr -> instr -> umap
val unify_stmts : umap -> stmt -> stmt -> umap
val unify_func : umap -> function_def -> stmt -> instr option -> lvalue option * umap
