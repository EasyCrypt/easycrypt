open EcPath
open EcAst
(* Nothing is allowed *)
val mr_empty : mem_restr

(* the full memory *)
val mr_full   : mem_restr


val mr_union : mem_restr -> mem_restr -> mem_restr
val mr_inter : mem_restr -> mem_restr -> mem_restr
val mr_diff  : mem_restr -> mem_restr -> mem_restr

val mr_globals : Sx.t -> mem_restr


val functor_fun : functor_params -> xpath -> functor_fun
val mr_globfun  : functor_params -> xpath -> mem_restr
val mr_globfuns : functor_params -> Sx.t -> mem_restr
