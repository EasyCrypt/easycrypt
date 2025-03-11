open EcPath
open EcAst
open EcEnv

module Uses : sig
  val to_form : env -> functor_params -> EcModules.uses -> memory -> form
end

val ff_alpha_equal : functor_fun -> functor_fun -> bool
val ff_ntr_compare : functor_fun -> functor_fun -> int

val ff_norm_restr : env -> functor_fun -> mem_restr
val ff_norm : env -> functor_fun -> memory -> form
val ff_norm_ty : env -> functor_fun -> ty

val fun_uses_mr : env -> xpath -> mem_restr

val module_uses_mr : env -> mpath -> module_type option -> mem_restr

val module_uses_ty : env -> mpath -> module_type option -> ty

val module_uses_form : env -> mpath -> module_type option -> memory -> form

val module_uses : env -> mpath -> module_type option -> functor_params * EcModules.uses

val norm_globs_restrs : env -> form -> form

val equal    : env -> mem_restr -> mem_restr -> bool
val subset   : env -> mem_restr -> mem_restr -> bool
val disjoint : env -> mem_restr -> mem_restr -> bool
val is_mem   : env -> bool -> xpath -> mem_restr -> bool
