(* -------------------------------------------------------------------- *)
open EcAst

(* -------------------------------------------------------------------- *)
(* Type-aware construction of operator/function applications as forms,
   with on-the-fly normalisation. Used by the circuit translation to bring
   applications into a reduced, translatable shape. The type-inference and
   reduction helpers are internal. *)

(* Raised by [f_app_safe ~full:true] when the operator is applied to too
   few arguments (its result type is still a function). *)
exception InsufficientArguments

(* [f_app_safe ~full env p args] builds the application of the operator at
   path [p] to [args], inferring and instantiating its type variables.
   With [~full:true] (the default) it raises [InsufficientArguments] when
   the result type is still a function. *)
val f_app_safe :
  ?full:bool -> EcEnv.env -> EcPath.path -> form list -> form

(* [fapply_safe ~redmode hyps f fs] applies the function-form [f] to the
   argument-forms [fs], normalising the result by call-by-value under
   [redmode] (default [EcReduction.full_red]). *)
val fapply_safe :
     ?redmode:EcReduction.reduction_info
  -> EcEnv.LDecl.hyps
  -> form
  -> form list
  -> form
