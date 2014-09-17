(* --------------------------------------------------------------------
 * Copyright (c) - 2012-2014 - IMDEA Software Institute and INRIA
 * Distributed under the terms of the CeCILL-C license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcUtils
open EcFol
open EcRing
open EcField
open EcDecl
open EcEnv

module RState : sig
  type rstate

  val empty   : rstate
  val add     : LDecl.hyps -> form -> rstate -> int * rstate
  val get     : int -> rstate -> form option
  val update  : rstate -> int list -> form list -> rstate
end

(* -------------------------------------------------------------------- *)
val rapp   : ring -> EcPath.path -> form list -> form
val rzero  : ring -> form
val rone   : ring -> form
val radd   : ring -> form -> form -> form
val ropp   : ring -> form -> form
val rmul   : ring -> form -> form -> form
val rexp   : ring -> form -> int -> form
val rsub   : ring -> form -> form -> form
val rofint : ring -> int -> form

(* -------------------------------------------------------------------- *)
val fzero  : field -> form
val fone   : field -> form
val fadd   : field -> form -> form -> form
val fopp   : field -> form -> form
val fmul   : field -> form -> form -> form
val fexp   : field -> form -> int -> form
val fsub   : field -> form -> form -> form
val finv   : field -> form -> form
val fdiv   : field -> form -> form -> form
val fofint : field -> int -> form

(* -------------------------------------------------------------------- *)
val emb_rzero : ring  -> form
val emb_fzero : field -> form

val emb_rone : ring  -> form
val emb_fone : field -> form

(* -------------------------------------------------------------------- *)
type eq = form * form

(* -------------------------------------------------------------------- *)
type cring
type cfield

val cring_of_ring   : ring  -> cring
val cfield_of_field : field -> cfield
val ring_of_cring   : cring -> ring 
val field_of_cfield : cfield-> field

(* -------------------------------------------------------------------- *)
val toring:
     LDecl.hyps
  -> cring                              (* ring structure *)
  -> RState.rstate                      (* reification state *)
  -> form                               (* formula to reify *)
  -> pexpr * RState.rstate              (* (reification, mutated state) *)

val ofring:
     ring                               (* ring structure *)
  -> RState.rstate                      (* reification state *)
  -> pexpr -> form

val ring_simplify_pe:
     cring                              (* ring structure *)
  -> pexpr pair list                    (* hypotheses (equations) *)
  -> pexpr                              (* expression to simplify *)
  -> pexpr                              (* simplified formula *)

val ring_simplify:
     LDecl.hyps
  -> cring                              (* ring structure *)
  -> eq list                            (* hypotheses (equations) *)
  -> form                               (* formula to simplify *)
  -> form                               (* simplified formula *)

val ring_eq:
    LDecl.hyps
  -> cring                              (* ring structure *)
  -> eq list                            (* hypotheses (equations) *)
  -> form                               (* LHS *)
  -> form                               (* RHS *)
  -> form

(* -------------------------------------------------------------------- *)
val tofield:
     EcEnv.LDecl.hyps
  -> cfield                             (* field structure *)
  -> RState.rstate                      (* reification state *)
  -> form                               (* formula to reify *)
  -> fexpr * RState.rstate              (* (reification, mutated state) *)

val offield:
     field                              (* field structure *)
  -> RState.rstate                      (* reification state *)
  -> fexpr -> form

val field_simplify_pe:
     cfield                             (* field structure *)
  -> pexpr pair list                    (* hypotheses (equations) *)
  -> fexpr                              (* formula to simplify *)
  -> pexpr list * pexpr pair            (* (!=0 conditions, (num, den)) *)

val field_simplify:
     LDecl.hyps
  -> cfield                             (* field structure *)
  -> eq list                            (* hypotheses (equations) *)
  -> form                               (* formula to simplify *)
  -> form list * form pair              (* (!=0 conditions, (num, den)) *)

val field_eq:
     LDecl.hyps
  -> cfield                             (* field structure *)
  -> eq list                            (* hypotheses (equations) *)
  -> form                               (* LHS *)
  -> form                               (* RHS *)
  -> form list * form pair pair         (* (!=0 conditions, (num, den) pair) *)
