open EcTypes
open EcModules
open EcSymbols

(*---------------------------------------------------------------------------------------*)
type u_error =
  | UE_AliasNoRet
  | UE_AliasNotPv
  | UE_InvalidRetInstr
  | UE_AbstractFun
  | UE_TypeMismatch of expr * expr
  | UE_UnificationFailArg of symbol
  | UE_UnificationFailPv of symbol
  | UE_LvNotInLockstep of lvalue * lvalue
  | UE_ExprNotInLockstep of expr * expr
  | UE_InstrNotInLockstep of instr * instr
  | UE_DifferentProgramLengths of stmt * stmt

exception UnificationError of u_error

(*---------------------------------------------------------------------------------------*)
(* `Unification` of procedures *)
(*
  The basic problem is:
    Given `r <@ f(a1, ..., an);` and a statement `s`, attempt to find values for
    `r`, `a1`,..., `an` such that inlining `f` will exactly match s.

  There are two modes of operation:
  - Exact: assume `s` is of the form `b`; `r <- e;` and perform unification of
    `b` with `f.body` and `e` with `f.res`.
  - Alias: assume `f.ret` is a program variable or tuple of program variables, only
    perform unification with `s` and `f.body`.

  Both modes result in a closed function call instruction `r' <@ f(a'1, ..., a'n);`
 *)
val unify_func : EcEnv.env -> [`Exact | `Alias] -> EcPath.xpath -> stmt -> stmt
