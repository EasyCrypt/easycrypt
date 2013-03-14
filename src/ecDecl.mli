(* -------------------------------------------------------------------- *)
open EcDebug
open EcUtils
open EcTypes
open EcFol

(* -------------------------------------------------------------------- *)
type ty_params = EcIdent.t list

type tydecl = {
  tyd_params : ty_params;
  tyd_type   : EcTypes.ty option;
}

val tydecl_dump : tydecl -> dnode

(* -------------------------------------------------------------------- *)
type locals = EcIdent.t list 

type 'b operator_info = (locals * 'b) option

type operator_kind = 
  | OB_oper of EcTypes.tyexpr operator_info
  | OB_pred of EcFol.form operator_info

type operator = {
  op_params : EcIdent.t list;
  op_dom    : EcTypes.dom;        
  op_codom  : EcTypes.ty;
  op_kind   : operator_kind;
}

val op_sig : operator -> tysig
val is_pred : operator -> bool

val mk_op   : EcIdent.t list -> dom -> ty -> tyexpr operator_info -> operator
val mk_pred : EcIdent.t list -> dom -> form operator_info -> operator

val op_dump : operator -> dnode

(* -------------------------------------------------------------------- *)
type axiom_kind = 
  | Axiom 
  | Lemma of EcFol.judgment option (* None means cloned lemma *)

type axiom = {
  ax_params : EcIdent.t list;
  ax_spec   : EcFol.form option;
  ax_kind   : axiom_kind
}

val ax_dump : axiom -> dnode
