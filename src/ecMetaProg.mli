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
(* Formulas rigid unification                                           *)
(* -------------------------------------------------------------------- *)
type 'a evmap

module EV : sig
  val empty     : 'a evmap
  val of_idents : ident list -> 'a evmap

  val add    : ident -> 'a evmap -> 'a evmap
  val set    : ident -> 'a -> 'a evmap -> 'a evmap
  val get    : ident -> 'a evmap -> [`Unset | `Set of 'a] option
  val doget  : ident -> 'a evmap -> 'a
  val fold   : (ident -> 'a -> 'b -> 'b) -> 'a evmap -> 'b -> 'b
  val filled : 'a evmap -> bool
end

(* -------------------------------------------------------------------- *)
exception MatchFailure

type fmoptions = {
  fm_delta : bool;
}

val fmrigid : fmoptions
val fmdelta : fmoptions

val f_match_core :
     fmoptions
  -> EcEnv.LDecl.hyps
  -> unienv * form evmap
  -> ptn:form
  -> form
  -> unienv * form evmap

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
  type select = [`Accept of int | `Reject | `Continue]

  val empty : ptnpos

  val is_empty : ptnpos -> bool

  val tostring : ptnpos -> string

  val select : ?o:Sint.t -> (Sid.t -> int list -> form -> select) -> form -> ptnpos

  val select_form : ?posf:int -> LDecl.hyps -> Sint.t option -> form -> form -> ptnpos

  val is_occurences_valid : Sint.t -> ptnpos -> bool

  val occurences : ptnpos -> int

  val filter : Sint.t -> ptnpos -> ptnpos

  val map : ptnpos -> (form -> form) -> form -> form

  val topattern : ?x:EcIdent.t -> ptnpos -> form -> EcIdent.t * form
end
