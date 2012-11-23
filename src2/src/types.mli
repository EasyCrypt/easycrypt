(* -------------------------------------------------------------------- *)
open Symbols
open Parsetree
open UidGen
(* -------------------------------------------------------------------- *)
type tybase = Tunit | Tbool | Tint | Treal

val tyb_equal : tybase -> tybase -> bool

type ty =
  | Tbase   of tybase
  | Tvar    of UidGen.uid
  | Tunivar of UidGen.uid
  | Trel    of int
  | Ttuple  of ty list
  | Tconstr of Path.path * ty list

(* -------------------------------------------------------------------- *)
val tunit : unit -> ty
val tbool : unit -> ty
val tint  : unit -> ty

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

val full_inst_rel : ty array -> ty -> ty
val full_inst_uni : ty Muid.t -> ty -> ty
val full_inst_var : ty Muid.t -> ty -> ty
val full_inst     : ty Muid.t * ty Muid.t -> ty -> ty
val inst_uni : ty Muid.t -> ty -> ty











(** TODO move this *)
(* -------------------------------------------------------------------- *)
type local = symbol * int

type tyexpr =
  | Eunit                                   (* unit literal      *)
  | Ebool   of bool                         (* bool literal      *)
  | Eint    of int                          (* int. literal      *)
  | Elocal  of local * ty                   (* local variable    *)
  | Eident  of Path.path * ty               (* symbol            *)
  | Eapp    of Path.path * tyexpr list      (* op. application   *)
  | Elet    of lpattern * tyexpr * tyexpr   (* let binding       *)
  | Etuple  of tyexpr list                  (* tuple constructor *)
  | Eif     of tyexpr * tyexpr * tyexpr     (* _ ? _ : _         *)
  | Ernd    of tyrexpr                      (* random expression *)

and tyrexpr =
  | Rbool                                   (* flip               *)
  | Rinter    of tyexpr * tyexpr            (* interval sampling  *)
  | Rbitstr   of tyexpr                     (* bitstring sampling *)
  | Rexcepted of tyrexpr * tyexpr           (* restriction        *)
  | Rapp      of Path.path * tyexpr list    (* p-op. application  *)
