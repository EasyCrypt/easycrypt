(* -------------------------------------------------------------------- *)
open EcUtils
open EcSymbols
open EcParsetree
open EcUidgen
open EcIdent

(* -------------------------------------------------------------------- *)
type tybase = Tunit | Tbool | Tint | Treal | Tbitstring

val tyb_equal : tybase -> tybase -> bool

type ty =
  | Tbase   of tybase
  | Tunivar of EcUidgen.uid
  | Tvar    of EcIdent.t 
  | Ttuple  of ty list
  | Tconstr of EcPath.path * ty list

type dom = ty list
type tysig = dom * ty 

type ty_decl = { td_params : EcIdent.t list; td_body : ty; }

(* -------------------------------------------------------------------- *)
val tunit      : unit -> ty
val tbool      : unit -> ty
val tint       : unit -> ty
val tbitstring : unit -> ty

val tlist : ty -> ty
val tmap  : ty -> ty -> ty

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
  | Eunit                                   (* unit literal      *)
  | Ebool   of bool                         (* bool literal      *)
  | Eint    of int                          (* int. literal      *)
  | Elocal  of EcIdent.t * ty                 (* local variable    *)
  | Evar    of EcPath.path * ty               (* module variable   *)
  | Eapp    of EcPath.path * tyexpr list      (* op. application   *)
  | Elet    of lpattern * tyexpr * tyexpr   (* let binding       *)
  | Etuple  of tyexpr list                  (* tuple constructor *)
  | Eif     of tyexpr * tyexpr * tyexpr     (* _ ? _ : _         *)
  | Ernd    of tyrexpr                      (* random expression *)

and tyrexpr =
  | Rbool                                    (* flip               *)
  | Rinter    of tyexpr * tyexpr             (* interval sampling  *)
  | Rbitstr   of tyexpr                      (* bitstring sampling *)
  | Rexcepted of tyrexpr * tyexpr            (* restriction        *)
  | Rapp      of EcPath.path * tyexpr list     (* p-op. application  *)

val e_map : (ty -> ty) -> (tyexpr -> tyexpr) -> (tyrexpr -> tyrexpr) ->
            tyexpr -> tyexpr
val re_map :  (tyexpr -> tyexpr) -> (tyrexpr -> tyrexpr) ->
            tyrexpr -> tyrexpr
module Esubst : sig
  val uni : ty Muid.t -> tyexpr -> tyexpr 
end
