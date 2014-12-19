(* --------------------------------------------------------------------
 * Copyright (c) - 2012-2014 - IMDEA Software Institute and INRIA
 * Distributed under the terms of the CeCILL-C license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
module PPEnv : sig
  type t

  val ofenv : EcEnv.env -> t
end

(* -------------------------------------------------------------------- *)
type 'a pp = Format.formatter -> 'a -> unit

val pp_id    : 'a pp -> 'a pp
val pp_if    : bool -> 'a pp -> 'a pp -> 'a pp
val pp_maybe : bool -> ('a pp -> 'a pp) -> 'a pp -> 'a pp

val pp_enclose:
       pre:('a, 'b, 'c, 'd, 'd, 'a) format6
   -> post:('a, 'b, 'c, 'd, 'd, 'a) format6
   -> 'a pp -> 'a pp

val pp_paren : 'a pp -> 'a pp

val pp_list : ('a, 'b, 'c, 'd, 'd, 'a) format6 -> 'a pp -> 'a list pp

val pp_pv      : PPEnv.t -> EcTypes.prog_var pp
val pp_local   : PPEnv.t -> EcIdent.ident pp
val pp_opname  : PPEnv.t -> EcPath.path pp
val pp_funname : PPEnv.t -> EcPath.xpath pp
val pp_topmod  : PPEnv.t -> EcPath.mpath pp
val pp_form    : PPEnv.t -> EcFol.form pp
val pp_type    : PPEnv.t -> EcTypes.ty pp
val pp_tyname  : PPEnv.t -> EcPath.path pp

val pp_typedecl : PPEnv.t -> (EcPath.path * EcDecl.tydecl                ) pp
val pp_opdecl   : ?long:bool -> PPEnv.t -> (EcPath.path * EcDecl.operator) pp
val pp_axiom    : ?long:bool -> PPEnv.t -> (EcPath.path * EcDecl.axiom   ) pp
val pp_theory   : PPEnv.t -> (EcPath.path * EcTheory.ctheory             ) pp
val pp_modtype  : PPEnv.t -> (EcModules.module_type * EcModules.mod_restr) pp
val pp_modexp   : PPEnv.t -> EcModules.module_expr                         pp
val pp_modsig   : PPEnv.t -> (EcPath.path * EcModules.module_sig         ) pp

val pp_mem : PPEnv.t -> EcIdent.t pp

val pp_tyvar    : PPEnv.t -> EcIdent.t pp
val pp_tyunivar : PPEnv.t -> EcUid.uid pp
val pp_path     : EcPath.path pp

val pp_equivS : PPEnv.t -> EcFol.equivS pp
val pp_goal   : PPEnv.t -> (int * (EcBaseLogic.hyps * EcFol.form)) pp

val pp_stmt  : PPEnv.t -> EcModules.stmt pp 
val pp_instr : PPEnv.t -> EcModules.instr pp 
