(* -------------------------------------------------------------------- *)
open EcAst

(* -------------------------------------------------------------------- *)
(* Type-aware construction of operator/function applications as forms,
   with on-the-fly normalisation. Used by the circuit translation to bring
   applications into a reduced, translatable shape. The type-inference and
   reduction helpers are internal. *)

(* [f_app_safe env p args] builds the application of the operator at path
   [p] to [args], inferring and instantiating its type variables. *)
val f_app_safe : EcEnv.env -> EcPath.path -> form list -> form

(* [fapply_safe ~redmode hyps f fs] applies the function-form [f] to the
   argument-forms [fs], normalising the result by call-by-value under
   [redmode] (default [EcReduction.full_red]). *)
val fapply_safe :
     ?redmode:EcReduction.reduction_info
  -> EcEnv.LDecl.hyps
  -> form
  -> form list
  -> form
