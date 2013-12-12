(* -------------------------------------------------------------------- *)
open EcIdent
open EcPath
open EcTypes
open EcFol
open EcModules
open EcEnv

(* -------------------------------------------------------------------- *)
type 'a eqtest = env -> 'a -> 'a -> bool

module EqTest : sig
  val for_type_exn : env -> ty -> ty -> unit

  val for_type       : ty       eqtest
  val for_pv_norm    : prog_var eqtest
  val for_instr_norm : instr    eqtest
  val for_stmt_norm  : stmt     eqtest
  val for_expr_norm  : expr     eqtest
end

val is_alpha_eq : LDecl.hyps -> form -> form -> bool

(* -------------------------------------------------------------------- *)
type reduction_info = {
  beta    : bool;
  delta_p : Sp.t option;          (* None means all *)
  delta_h : Sid.t option;         (* None means all *)
  zeta    : bool;                 (* reduce let  *)
  iota    : bool;                 (* reduce case *)
  logic   : bool;                 (* perform logical simplification *)
  modpath : bool;                 (* reduce module path *)
}

val full_red     : reduction_info
val no_red       : reduction_info
val beta_red     : reduction_info
val betaiota_red : reduction_info

val h_red_opt : reduction_info -> LDecl.hyps -> form -> form option
val h_red     : reduction_info -> LDecl.hyps -> form -> form

val simplify : reduction_info -> LDecl.hyps -> form -> form

val is_conv    : LDecl.hyps -> form -> form -> bool
val check_conv : LDecl.hyps -> form -> form -> unit
