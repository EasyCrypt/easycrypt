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

type dom = ty list
type tysig = dom * ty 

type ty_decl = { td_params : EcIdent.t list; td_body : ty; }

(* -------------------------------------------------------------------- *)
val tunit      : ty
val tbool      : ty
val tint       : ty
val tbitstring : ty

val tlist      : ty -> ty

val mkunivar : unit -> ty

(* -------------------------------------------------------------------- *)
  
(* [freshen n ty] replaces the [n] type variables by fresh
 * unification variables
 *)
val freshen : EcIdent.t list -> ty -> ty
val freshendom : EcIdent.t list -> dom -> dom
val freshensig : EcIdent.t list -> tysig -> tysig

(* -------------------------------------------------------------------- *)
module Subst : sig
  val uni1 : (uid * ty) -> ty -> ty
  val uni  : ty Muid.t -> ty -> ty
end

(* -------------------------------------------------------------------- *)
(* [map f t] applies [f] on strict-subterm of [t] (not recursive) *)
val map : (ty -> ty) -> ty -> ty
(* [sub_exists f t] true if one of the strict-subterm of [t] valid [f] *)
val sub_exists : (ty -> bool) -> ty -> bool

val occur_uni : EcUidgen.uid -> ty -> bool

(* -------------------------------------------------------------------- *)
exception UnBoundUni of EcUidgen.uid
exception UnBoundVar of EcIdent.t 

val full_inst_uni : ty Muid.t -> ty -> ty
val inst_uni : ty Muid.t -> ty -> ty
val inst_uni_dom : ty Muid.t -> dom -> dom
val inst_var : ty EcIdent.Mid.t -> ty -> ty
val init_substvar : EcIdent.t list -> ty list -> ty EcIdent.Mid.t

(* -------------------------------------------------------------------- *)
type lpattern =
  | LSymbol of EcIdent.t
  | LTuple  of EcIdent.t list

type tyexpr =
  | Eint      of int                              (* int. literal       *)
  | Eflip                                         (* flip               *)
  | Einter    of tyexpr * tyexpr                  (* interval sampling  *)
  | Ebitstr   of tyexpr                           (* bitstring sampling *)
  | Eexcepted of tyexpr * tyexpr                  (* restriction        *)
  | Elocal    of EcIdent.t * ty                   (* local variable     *)
  | Evar      of EcPath.path * ty                 (* module variable    *)
  | Eapp      of EcPath.path * tyexpr list * ty   (* op. application    *)
  | Elet      of lpattern * tyexpr * tyexpr       (* let binding        *)
  | Etuple    of tyexpr list                      (* tuple constructor  *)
  | Eif       of tyexpr * tyexpr * tyexpr         (* _ ? _ : _          *)

(* -------------------------------------------------------------------- *)
val e_map : (ty -> ty) -> (tyexpr -> tyexpr) -> tyexpr -> tyexpr
val ids_of_lpattern : lpattern -> EcIdent.t list
(* -------------------------------------------------------------------- *)
module Esubst : sig
  val uni : ty Muid.t -> tyexpr -> tyexpr 
end
