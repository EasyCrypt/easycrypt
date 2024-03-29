(* -------------------------------------------------------------------- *)
open EcUid
open EcIdent
open EcPath
open EcAst
open EcTypes
open EcCoreModules
open EcCoreFol

(* -------------------------------------------------------------------- *)
type sc_instanciate = {
  sc_memtype : memtype;
  sc_mempred : mem_pr Mid.t;
  sc_expr    : expr Mid.t;
}

(* -------------------------------------------------------------------- *)
type f_subst

type 'a substitute = f_subst -> 'a -> 'a
(* form before subst -> form after -> resulting form *)
type tx = before:form -> after:form -> form
type 'a tx_substitute = ?tx:tx -> 'a substitute
type 'a subst_binder = f_subst -> 'a -> f_subst * 'a

(* -------------------------------------------------------------------- *)
val f_subst_init :
       ?freshen:bool
    -> ?tu:ty Muid.t
    -> ?tv:ty Mid.t
    -> ?esloc:expr Mid.t
    -> unit
    -> f_subst

(* -------------------------------------------------------------------- *)
module Tuni : sig
  val univars   : ty -> Suid.t
  val subst1    : (uid * ty) -> f_subst
  val subst     : ty Muid.t -> f_subst
  val subst_dom : ty Muid.t -> dom -> dom
  val occurs    : uid -> ty -> bool
  val fv        : ty -> Suid.t
end

(* -------------------------------------------------------------------- *)
module Tvar : sig
  val init    : EcIdent.t list -> ty list -> ty Mid.t
  val subst1  : (EcIdent.t * ty) -> ty -> ty
  val subst   : ty Mid.t -> ty -> ty
  val f_subst : freshen:bool -> EcIdent.t list -> ty list -> form -> form
end

(* -------------------------------------------------------------------- *)
val add_elocal  : (EcIdent.t * ty) subst_binder
val add_elocals : (EcIdent.t * ty) list subst_binder
val bind_elocal : f_subst -> EcIdent.t -> expr -> f_subst


(* -------------------------------------------------------------------- *)
val ty_subst : ty substitute
val e_subst  : expr substitute
val s_subst  : stmt substitute

(* -------------------------------------------------------------------- *)
module Fsubst : sig
  val f_subst_id  : f_subst
  val is_subst_id : f_subst -> bool

  val f_subst_init :
       ?freshen:bool
    -> ?tu:ty Muid.t
    -> ?tv:ty Mid.t
    -> ?esloc:expr Mid.t
    -> unit -> f_subst

  val f_bind_local  : f_subst -> EcIdent.t -> form -> f_subst
  val f_bind_mem    : f_subst -> EcIdent.t -> EcIdent.t -> f_subst
  val f_bind_absmod : f_subst -> EcIdent.t -> EcIdent.t -> f_subst
  val f_bind_mod    : f_subst -> EcIdent.t -> EcPath.mpath -> (EcIdent.t -> form) -> f_subst
  val f_bind_rename : f_subst -> EcIdent.t -> EcIdent.t -> ty -> f_subst

  val has_mem : f_subst -> EcAst.memory -> bool

  val f_subst   : form tx_substitute

  val f_subst_local : EcIdent.t -> form -> form -> form
  val f_subst_mem   : EcIdent.t -> EcIdent.t -> form -> form

  val f_subst_tvar :
    freshen:bool ->
    EcTypes.ty EcIdent.Mid.t ->
    form -> form

  val add_binding  : binding subst_binder
  val add_bindings : bindings subst_binder

  val lp_subst  : lpattern    subst_binder
  val mp_subst  : mpath       substitute
  val x_subst   : xpath       substitute
  val pv_subst  : prog_var    substitute
  val s_subst   : stmt        substitute
  val e_subst   : expr        substitute
  val me_subst  : memenv      substitute
  val m_subst   : EcIdent.t   substitute
  val mr_subst  : mod_restr   substitute
  val mty_subst : module_type substitute
  val oi_subst  : PreOI.t     substitute
  val gty_subst : gty         substitute
end
