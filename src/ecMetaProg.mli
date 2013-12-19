(* -------------------------------------------------------------------- *)
open EcMaps
open EcUid
open EcParsetree
open EcIdent
open EcTypes
open EcModules
open EcEnv
open EcFol
open EcUnify

(* -------------------------------------------------------------------- *)
module Zipper : sig
  type ipath =
  | ZTop
  | ZWhile  of expr * spath
  | ZIfThen of expr * spath * stmt
  | ZIfElse of expr * stmt  * spath

  and spath = (instr list * instr list) * ipath

  type zipper = {
    z_head : instr list;                (* instructions on my left (rev)       *)
    z_tail : instr list;                (* instructions on my right (me incl.) *)
    z_path : ipath ;                    (* path (zipper) leading to me         *)
  }

  exception InvalidCPos

  (* [zipper] soft constructor *)
  val zipper : instr list -> instr list -> ipath -> zipper

  (* Return the zipper for the stmt [stmt] at code position [codepos].
   * Raise [InvalidCPos] if [codepos] is not valid for [stmt]. *)
  val zipper_of_cpos : codepos -> stmt -> zipper

  (* Zip the zipper, returning the corresponding statement *)
  val zip : zipper -> stmt

  (* [after ~strict zpr] returns all the statements that come after the
   * zipper cursor. They are returned as a list of statements, where the head
   * is the list of instructions coming directly after the cursor at the
   * same level, the next element is the ones coming after the cursor
   * parent block, and so forth. The cursor is included iff [strict] is [true].
   *)   
  val after : strict:bool -> zipper -> instr list list

  type ('a, 'state) folder = 'a -> 'state -> instr -> 'state * instr list

  (* [fold cl cpos f state s] create the zipper for [s] at [cpos], and apply
   * [f] to it, along with [v] and the state [state]. [f] must return the
   * new [state] and a new [zipper]. These last are directly returned.
   *
   * Raise [InvalidCPos] if [cpos] is not valid for [s], or any exception
   * raised by [f].
   *)
  val fold : 'a -> codepos -> ('a, 'state) folder -> 'state -> stmt -> 'state * stmt
end

(* -------------------------------------------------------------------- *)
(* Expressions / formulas matching for tactics                          *)
(* -------------------------------------------------------------------- *)
module IMatch : sig
  (* pattern can be
   * - b         => match single instruction with b, see below
   * - [b1...bn] => match one of b1 ... bn
   * - p*        => repeat p
   * - p+        => repeat p, at least 1 time
   * - p{n}      => match p `n' times
   * - (p)       => pattern grouping, for back-reference
   *
   * instruction pattern can be
   * - _ => any
   * - i => if-then-else
   * - w => while-loop
   *)

  type t
  type mtch

  exception InvalidPattern of string

  val compile : string -> t
  val match_  : t -> instr list -> mtch option

  val get : mtch -> int -> instr list

  val get_as_while : mtch -> int -> instr * (expr * stmt)
  val get_as_if    : mtch -> int -> instr * (expr * stmt * stmt)
end

(* -------------------------------------------------------------------- *)
(* Formulas rigid unification                                           *)
(* -------------------------------------------------------------------- *)
type 'a evmap

module EV : sig
  val empty     : 'a evmap
  val of_idents : ident list -> 'a evmap

  val add   : ident -> 'a evmap -> 'a evmap
  val get   : ident -> 'a evmap -> [`Unset | `Set of 'a] option
  val doget : ident -> 'a evmap -> 'a
  val fold  : (ident -> 'a -> 'b -> 'b) -> 'a evmap -> 'b -> 'b
end

(* -------------------------------------------------------------------- *)
exception MatchFailure

type fmoptions = {
  fm_delta : bool;
}

val fmrigid : fmoptions
val fmdelta : fmoptions

val f_match :
     fmoptions
  -> EcEnv.LDecl.hyps
  -> unienv * form evmap
  -> ptn:form
  -> form
  -> unienv * (uid -> ty option) * form evmap

(* -------------------------------------------------------------------- *)
type ptnpos = private [`Select of int | `Sub of ptnpos] Mint.t

exception InvalidPosition
exception InvalidOccurence

module FPosition : sig
  val empty : ptnpos

  val is_empty : ptnpos -> bool

  val tostring : ptnpos -> string

  val select : ?o:Sint.t -> (Sid.t -> form -> int option) -> form -> ptnpos

  val select_form : LDecl.hyps -> Sint.t option -> form -> form -> ptnpos

  val is_occurences_valid : Sint.t -> ptnpos -> bool

  val occurences : ptnpos -> int

  val filter : Sint.t -> ptnpos -> ptnpos

  val map : ptnpos -> (form -> form) -> form -> form

  val topattern : ?x:EcIdent.t -> ptnpos -> form -> EcIdent.t * form
end
