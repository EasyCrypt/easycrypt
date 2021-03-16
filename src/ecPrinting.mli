(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcIdent
open EcSymbols
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
  val add_locals : ?force:bool -> t -> EcIdent.t list -> t
end

(* -------------------------------------------------------------------- *)
type prpo_display = { prpo_pr : bool; prpo_po : bool; }

(* -------------------------------------------------------------------- *)
val string_of_hcmp : EcFol.hoarecmp -> string
val string_of_cpos1 : EcParsetree.codepos1 -> string

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

(* -------------------------------------------------------------------- *)
val pp_pv      : PPEnv.t -> prog_var pp
val pp_local   : ?fv:Sid.t -> PPEnv.t -> ident pp
val pp_opname  : PPEnv.t -> path pp
val pp_funname : PPEnv.t -> xpath pp
val pp_topmod  : PPEnv.t -> mpath pp
val pp_expr    : PPEnv.t -> expr pp
val pp_form    : PPEnv.t -> form pp
val pp_type    : PPEnv.t -> ty pp
val pp_tyname  : PPEnv.t -> path pp
val pp_axname  : PPEnv.t -> path pp

val pp_mem      : PPEnv.t -> EcIdent.t pp
val pp_tyvar    : PPEnv.t -> ident pp
val pp_tyunivar : PPEnv.t -> EcUid.uid pp
val pp_path     : path pp

(* -------------------------------------------------------------------- *)
val pp_typedecl : PPEnv.t -> (path * tydecl                ) pp
val pp_opdecl   : ?long:bool -> PPEnv.t -> (path * operator) pp
val pp_added_op : PPEnv.t -> operator pp
val pp_axiom    : ?long:bool -> PPEnv.t -> (path * axiom   ) pp
val pp_theory   : PPEnv.t -> (path * (ctheory * thmode)    ) pp
val pp_modtype1 : PPEnv.t -> module_type                     pp
val pp_modtype  : PPEnv.t -> (module_type * mod_restr      ) pp
val pp_modexp   : PPEnv.t -> (mpath * module_expr          ) pp
val pp_modsig   : PPEnv.t -> (path * module_sig            ) pp

(* -------------------------------------------------------------------- *)
val pp_hoareS   : PPEnv.t -> ?prpo:prpo_display -> hoareS  pp
val pp_bdhoareS : PPEnv.t -> ?prpo:prpo_display -> bdHoareS pp
val pp_equivS   : PPEnv.t -> ?prpo:prpo_display -> equivS  pp

val pp_stmt  : ?lineno:bool -> PPEnv.t -> stmt pp
val pp_instr : PPEnv.t -> instr pp

(* -------------------------------------------------------------------- *)
type ppgoal = (EcBaseLogic.hyps * EcFol.form) * [
  | `One of int
  | `All of (EcBaseLogic.hyps * EcFol.form) list
]

val pp_hyps : PPEnv.t -> EcEnv.LDecl.hyps pp
val pp_goal : PPEnv.t -> prpo_display -> ppgoal pp

(* -------------------------------------------------------------------- *)
module ObjectInfo : sig
  type db = [`Rewrite of qsymbol | `Solve of symbol]

  val pr_ty  : Format.formatter -> EcEnv.env -> qsymbol -> unit
  val pr_op  : Format.formatter -> EcEnv.env -> qsymbol -> unit
  val pr_th  : Format.formatter -> EcEnv.env -> qsymbol -> unit
  val pr_ax  : Format.formatter -> EcEnv.env -> qsymbol -> unit
  val pr_mod : Format.formatter -> EcEnv.env -> qsymbol -> unit
  val pr_mty : Format.formatter -> EcEnv.env -> qsymbol -> unit
  val pr_rw  : Format.formatter -> EcEnv.env -> qsymbol -> unit
  val pr_at  : Format.formatter -> EcEnv.env -> symbol -> unit
  val pr_db  : Format.formatter -> EcEnv.env -> db -> unit
  val pr_any : Format.formatter -> EcEnv.env -> qsymbol -> unit
end
