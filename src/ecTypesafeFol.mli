(* -------------------------------------------------------------------- *)
open EcAst

(* -------------------------------------------------------------------- *)
(* Type-aware construction of operator/function applications as forms,
   with on-the-fly normalisation. Used by the circuit translation to bring
   applications into a reduced, translatable shape. *)

(* [f_app_safe env ?typarams ?rty op args] builds the application of the
   operator at path [op] to [args], instantiating its type variables.
   [?typarams] seeds the type parameters of the unification environment and
   [?rty] fixes the expected result type. It is an internal error (assert)
   if the application does not type — unification fails, or type variables
   remain unresolved. *)
val f_app_safe :
     EcEnv.env
  -> ?typarams:EcDecl.ty_params
  -> ?rty:EcTypes.ty
  -> EcPath.path
  -> form list
  -> form

(* [fapply_safe ~redmode hyps f fs] applies the function-form [f] to the
   argument-forms [fs], normalising the result by call-by-value under
   [redmode] (default [EcReduction.full_red]). *)
val fapply_safe :
     ?redmode:EcReduction.reduction_info
  -> EcEnv.LDecl.hyps
  -> form
  -> form list
  -> form
