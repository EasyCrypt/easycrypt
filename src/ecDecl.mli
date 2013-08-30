(* -------------------------------------------------------------------- *)
open EcUtils
open EcTypes
open EcFol

(* -------------------------------------------------------------------- *)
type ty_params = EcIdent.t list

type tydecl = {
  tyd_params : ty_params;
  tyd_type   : EcTypes.ty option;
}

(* -------------------------------------------------------------------- *)
type locals = EcIdent.t list 

type operator_kind = 
  | OB_oper of EcTypes.expr option
  | OB_pred of EcFol.form option

type operator = {
  op_tparams : EcIdent.t list;
  op_ty      : EcTypes.ty;        
  op_kind    : operator_kind;
}

val op_ty : operator -> ty
val is_pred : operator -> bool

val mk_op   : EcIdent.t list -> ty -> expr option -> operator
val mk_pred : EcIdent.t list -> ty list -> form option -> operator

(* -------------------------------------------------------------------- *)
type axiom_kind = [`Axiom | `Lemma]

type axiom = {
  ax_tparams : EcIdent.t list;
  ax_spec    : EcFol.form option;
  ax_kind    : axiom_kind;
  ax_nosmt   : bool;
}

(* -------------------------------------------------------------------- *)
type typeclass = {
  tc_ops : (EcIdent.t * EcTypes.ty) list;
  tc_axs : form list;
}
