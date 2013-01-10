(* -------------------------------------------------------------------- *)
open EcUtils
open EcSymbols
open EcParsetree
open EcUidgen
open EcIdent

(* -------------------------------------------------------------------- *)
type ty =
  | Tunivar of EcUidgen.uid
  | Tvar    of EcIdent.t 
  | Ttuple  of ty list
  | Tconstr of EcPath.path * ty list

type dom   = ty list
type tysig = dom * ty 

(* -------------------------------------------------------------------- *)
val tunit      : ty
val tbool      : ty
val tint       : ty
val tbitstring : ty
val tlist      : ty -> ty

(* -------------------------------------------------------------------- *)
module Tuni : sig
  val subst1    : (uid * ty) -> ty -> ty
  val subst     : ty Muid.t -> ty -> ty
  val subst_dom : ty Muid.t -> dom -> dom
  val occur     : uid -> ty -> bool
  val fv        : ty -> Suid.t
  val fv_sig    : tysig -> Suid.t
end

module Tvar : sig
  val subst1  : (EcIdent.t * ty) -> ty -> ty
  val subst   : ty Mid.t -> ty -> ty
  val init    : EcIdent.t list -> ty list -> ty Mid.t
  val fv      : ty -> Sid.t
  val fv_sig  : tysig -> Sid.t
end

(* -------------------------------------------------------------------- *)
(* [map f t] applies [f] on strict-subterm of [t] (not recursive) *)
val map : (ty -> ty) -> ty -> ty
(* [sub_exists f t] true if one of the strict-subterm of [t] valid [f] *)
val sub_exists : (ty -> bool) -> ty -> bool

(* -------------------------------------------------------------------- *)
type lpattern =
  | LSymbol of EcIdent.t
  | LTuple  of EcIdent.t list

type pvar_kind = 
  | PVglob
  | PVloc 

type prog_var = 
    { pv_name : EcPath.path;
      pv_kind : pvar_kind }

type tyexpr =
  | Eint      of int                              (* int. literal       *)
  | Eflip                                         (* flip               *)
  | Einter    of tyexpr * tyexpr                  (* interval sampling  *)
  | Ebitstr   of tyexpr                           (* bitstring sampling *)
  | Eexcepted of tyexpr * tyexpr                  (* restriction        *)
  | Elocal    of EcIdent.t * ty         (* local variable binded by let *)
  | Evar      of prog_var  * ty                   (* module variable    *)
                               
  | Eapp      of EcPath.path * tyexpr list * ty   (* op. application    *)
  | Elet      of lpattern * tyexpr * tyexpr       (* let binding        *)
  | Etuple    of tyexpr list                      (* tuple constructor  *)
  | Eif       of tyexpr * tyexpr * tyexpr         (* _ ? _ : _          *)

(* -------------------------------------------------------------------- *)
val e_map : (ty -> ty) -> (tyexpr -> tyexpr) -> tyexpr -> tyexpr
val ids_of_lpattern : lpattern -> EcIdent.t list

(* -------------------------------------------------------------------- *)
module Esubst : sig
  val mapty : (ty -> ty) -> tyexpr -> tyexpr

  val uni : ty Muid.t -> tyexpr -> tyexpr 

end

(* -------------------------------------------------------------------- *)
module Dump : sig
  val ty_dump : EcDebug.ppdebug -> ty -> unit
  val ex_dump : EcDebug.ppdebug -> tyexpr -> unit
end
