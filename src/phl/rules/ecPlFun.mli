(* -------------------------------------------------------------------- *)
open EcSymbols
open EcPath
open EcAst
open EcModules
open EcEnv
open EcCoreGoal

(* -------------------------------------------------------------------- *)
(* Computations shared by the procedure rules ([proc]) of every logic:
   unfolding a concrete procedure ([Ec<Logic>FunDef]), the oracle and
   losslessness conditions of the abstract-procedure rules
   ([Ec<Logic>FunAbs], [EcEquivFunAbsUpto]) and the single-call statement
   of [proc*] ([Ec<Logic>FunToCode]). *)

(* -------------------------------------------------------------------- *)
(* Concrete procedures. *)

(* Fails with a user-facing error when [f] is abstract. *)
val check_concrete : proofenv -> env -> xpath -> unit

(* Same, for the subgoal builders: fails with [Failure "<name>: ..."]. *)
val ensure_concrete : string -> env -> xpath -> unit

(* [subst_pre env fs m s] extends [s] with [arg{m} := (x1, ..., xn){m}],
   [x1 ... xn] the parameters of the signature [fs]. *)
val subst_pre : env -> funsig -> memory -> EcPV.PVM.subst -> EcPV.PVM.subst

(* -------------------------------------------------------------------- *)
(* Abstract procedures. *)

(* [check_oracle_use env top o]: the oracle [o] does not write the globals
   of the abstract module [top] (fails otherwise). *)
val check_oracle_use : env -> mpath -> xpath -> unit

(* [lossless_hyps env top f]: the procedure [f] of the abstract functor
   [top] is lossless when its oracles are:
     forall (O1 <: T1 {-top}) ... (On <: Tn {-top}),
       islossless o_1 => ... => islossless o_k => islossless top(O1..On).f
   [o_1 ... o_k] being the oracles [f] may call. *)
val lossless_hyps : env -> mpath -> symbol -> form

(* -------------------------------------------------------------------- *)
(* Procedure to code ([proc*]). *)

(* [to_code env f m]: the statement [r <@ f(a1, ..., an)] in memory [m],
   extended with fresh local variables [a1 ... an] (the parameters of
   [f], unnamed ones named [arg<i>]) and [r]. Returns the memory, the
   statement, [r] and [a1 ... an]. Deterministic. *)
val to_code :
  env -> xpath -> memory -> memenv * stmt * ovariable * variable list

(* [add_var env x m v m' s] extends [s] with [x{m} := v{m'}]. *)
val add_var :
     env -> prog_var -> memory -> ovariable -> memory
  -> EcPV.PVM.subst -> EcPV.PVM.subst

(* [add_var_tuple env x m vs m' s] extends [s] with
   [x{m} := (v1, ..., vn){m'}]. *)
val add_var_tuple :
     env -> prog_var -> memory -> variable list -> memory
  -> EcPV.PVM.subst -> EcPV.PVM.subst
