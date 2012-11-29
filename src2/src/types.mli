(* -------------------------------------------------------------------- *)
open Utils
open Symbols
open Parsetree
open UidGen
(* -------------------------------------------------------------------- *)
type tybase = Tunit | Tbool | Tint | Treal | Tbitstring

val tyb_equal : tybase -> tybase -> bool

type ty =
  | Tbase   of tybase
  | Tvar    of string * UidGen.uid
  | Tunivar of UidGen.uid
  | Trel    of string * int
  | Ttuple  of ty Parray.t 
  | Tconstr of Path.path * ty Parray.t 

type ty_decl = int * ty

(* -------------------------------------------------------------------- *)
val tunit      : unit -> ty
val tbool      : unit -> ty
val tint       : unit -> ty
val tbitstring : unit -> ty

val tlist : ty -> ty
val tmap  : ty -> ty -> ty

val mkunivar : unit -> ty

(* -------------------------------------------------------------------- *)
(* [map f t] applies [f] on strict-subterm of [t] (not recursive) *)
val map : (ty -> ty) -> ty -> ty
(* [sub_exists f t] true if one of the strict-subterm of [t] valid [f] *)
val sub_exists : (ty -> bool) -> ty -> bool

val occur_uni : UidGen.uid -> ty -> bool

(* -------------------------------------------------------------------- *)
exception UnBoundRel of int
exception UnBoundUni of UidGen.uid
exception UnBoundVar of UidGen.uid

val full_inst_rel : ty Parray.t -> ty -> ty
val full_inst_uni : ty Muid.t -> ty -> ty
val full_inst_var : ty Muid.t -> ty -> ty
val full_inst     : ty Muid.t * ty Muid.t -> ty -> ty
val inst_uni : ty Muid.t -> ty -> ty

(* -------------------------------------------------------------------- *)
type lpattern =
  | LSymbol of Ident.t
  | LTuple  of Ident.t list

type tyexpr =
  | Eunit                                   (* unit literal      *)
  | Ebool   of bool                         (* bool literal      *)
  | Eint    of int                          (* int. literal      *)
  | Elocal  of Ident.t * ty                 (* local variable    *)
  | Evar    of Path.path * ty               (* module variable   *)
  | Eapp    of Path.path * tyexpr list      (* op. application   *)
  | Elet    of lpattern * tyexpr * tyexpr   (* let binding       *)
  | Etuple  of tyexpr list                  (* tuple constructor *)
  | Eif     of tyexpr * tyexpr * tyexpr     (* _ ? _ : _         *)
  | Ernd    of tyrexpr                      (* random expression *)

and tyrexpr =
  | Rbool                                    (* flip               *)
  | Rinter    of tyexpr * tyexpr             (* interval sampling  *)
  | Rbitstr   of tyexpr                      (* bitstring sampling *)
  | Rexcepted of tyrexpr * tyexpr            (* restriction        *)
  | Rapp      of Path.path * tyexpr list     (* p-op. application  *)
