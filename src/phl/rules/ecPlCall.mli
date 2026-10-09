(* -------------------------------------------------------------------- *)
open EcPath
open EcAst
open EcEnv

(* -------------------------------------------------------------------- *)
(* Computations shared by the [call] rules of every logic
   ([Ec<Logic>Call]). *)

(* [wp_asgn_call ?mc env lv r Q]: [Q] with the result [r] assigned to the
   left-value [lv] of the call (let-bound), [Q] itself when the call has no
   left-value. [r] and [Q] are in the same memory. [~mc] gives the two
   memories of a two-sided [Q]. *)
val wp_asgn_call :
     ?mc:(memory * memory)
  -> env -> lvalue option -> ss_inv -> ss_inv -> ss_inv

(* [subst_args_call env m a s] extends [s] with [arg{m} := a{m}]. *)
val subst_args_call :
  env -> memory -> expr -> EcPV.PVM.subst -> EcPV.PVM.subst

(* [call_error env tc f1 f2]: fails with the error of [call] given a
   specification of [f1] when the last statement calls [f2]. *)
val call_error : env -> EcCoreGoal.tcenv1 -> xpath -> xpath -> 'a

(* [single_call name s]: [s] is a single call [lv <@ f(a)], returned as
   [(lv, f, a)]; fails with [Failure "<name>: ..."] otherwise. *)
val single_call : string -> stmt -> lvalue option * xpath * expr list
