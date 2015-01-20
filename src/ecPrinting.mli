(* --------------------------------------------------------------------
 * Copyright (c) - 2012-2015 - IMDEA Software Institute and INRIA
 * Distributed under the terms of the CeCILL-C license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcIdent
open EcPath
open EcTypes
open EcFol
open EcDecl
open EcModules
open EcTheory

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

val pp_pv      : PPEnv.t -> prog_var pp
val pp_local   : PPEnv.t -> ident pp
val pp_opname  : PPEnv.t -> path pp
val pp_funname : PPEnv.t -> xpath pp
val pp_topmod  : PPEnv.t -> mpath pp
val pp_form    : PPEnv.t -> form pp
val pp_type    : PPEnv.t -> ty pp
val pp_tyname  : PPEnv.t -> path pp

val pp_typedecl : PPEnv.t -> (path * tydecl                ) pp
val pp_opdecl   : ?long:bool -> PPEnv.t -> (path * operator) pp
val pp_axiom    : ?long:bool -> PPEnv.t -> (path * axiom   ) pp
val pp_theory   : PPEnv.t -> (path * (ctheory * thmode)    ) pp
val pp_modtype  : PPEnv.t -> (module_type * mod_restr      ) pp
val pp_modexp   : PPEnv.t -> (module_expr                  ) pp
val pp_modsig   : PPEnv.t -> (path * module_sig            ) pp

val pp_mem : PPEnv.t -> EcIdent.t pp

val pp_tyvar    : PPEnv.t -> ident pp
val pp_tyunivar : PPEnv.t -> EcUid.uid pp
val pp_path     : path pp

val pp_equivS : PPEnv.t -> equivS pp
val pp_goal   : PPEnv.t -> (int * (EcBaseLogic.hyps * EcFol.form)) pp

val pp_stmt  : PPEnv.t -> stmt pp 
val pp_instr : PPEnv.t -> instr pp 
