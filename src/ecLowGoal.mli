(* --------------------------------------------------------------------
 * Copyright (c) - 2012-2014 - IMDEA Software Institute and INRIA
 * Distributed under the terms of the CeCILL-C license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcLocation
open EcParsetree
open EcUtils
open EcSymbols
open EcIdent
open EcPath
open EcTypes
open EcFol
open EcReduction
open EcProvers
open EcMatching
open EcCoreGoal

(* -------------------------------------------------------------------- *)
exception InvalidProofTerm         (* invalid proof term *)

type side    = [`Left|`Right]
type lazyred = EcProofTyping.lazyred

(* -------------------------------------------------------------------- *)
val t_admit : FApi.backward
val t_true  : FApi.backward
val t_fail  : FApi.backward
val t_id    : FApi.backward

(* -------------------------------------------------------------------- *)
val alpha_find_in_hyps : EcEnv.LDecl.hyps -> EcFol.form -> EcIdent.t
val t_assumption    : [`Alpha | `Conv] -> FApi.backward
val t_absurd_hyp    : ?id:EcIdent.t -> FApi.backward
val t_logic_trivial : FApi.backward
val t_trivial       : FApi.backward option -> FApi.backward

(* -------------------------------------------------------------------- *)
val t_simplify : ?delta:bool -> FApi.backward
val t_simplify_with_info : reduction_info -> FApi.backward

(* -------------------------------------------------------------------- *)
val t_change : form -> tcenv1 -> tcenv1

(* -------------------------------------------------------------------- *)
val t_reflex       : ?reduce:lazyred -> FApi.backward
val t_transitivity : ?reduce:lazyred -> form -> FApi.backward
val t_symmetry     : ?reduce:lazyred -> FApi.backward

(* -------------------------------------------------------------------- *)
module LowApply : sig
  type ckenv = [`Tc of rtcenv | `Hyps of EcEnv.LDecl.hyps * proofenv]

  val check : [`Elim | `Intro] -> proofterm -> ckenv -> proofterm * form
end

(* Main low-level MP tactic. Apply a fully constructed proof-term to
 * the focused goal. If the proof-term contains PTCut-terms, create the
 * related subgoals. Raise [InvalidProofTerm] is the proof-term is not
 * valid (not typable or not a proof of the focused goal). *)
val t_apply : proofterm -> FApi.backward

(* Apply a proof term of the form [p<:ty1...tyn> f1...fp _ ... _]
 * constructed from the path, type parameters, and formulas given to
 * the function. The [int] argument gives the number of premises to
 * skip before applying [p]. *)
val t_apply_s : path -> ty list -> ?args:(form list) -> ?sk:int -> FApi.backward

(* Apply a proof term of the form [h f1...fp _ ... _] constructed from
 * the local hypothesis and formulas given to the function. The [int]
 * argument gives the number of premises to skip before applying
 * [p]. *)
val t_apply_hyp : EcIdent.t -> ?args:(form list) -> ?sk:int -> FApi.backward

(* Apply a proof term of the form [h f1...fp] constructed from the
 * given handle and formulas given to the function.  The [int] argument
 * gives the number of premises to skip before applying [p]. *)
val t_apply_hd : handle -> ?args:(form list) -> ?sk:int -> FApi.backward

(* -------------------------------------------------------------------- *)
(* Introduction of logical operators (backward). *)
val t_or_intro_s  : bool -> [`Left|`Right] -> form pair -> FApi.backward
val t_and_intro_s : bool -> form pair -> FApi.backward
val t_iff_intro_s : form pair -> FApi.backward

val t_or_intro  : ?reduce:lazyred -> side -> FApi.backward
val t_and_intro : ?reduce:lazyred -> FApi.backward
val t_iff_intro : ?reduce:lazyred -> FApi.backward

val t_left  : ?reduce:lazyred -> FApi.backward
val t_right : ?reduce:lazyred -> FApi.backward

(* -------------------------------------------------------------------- *)
val t_split : ?closeonly:bool -> ?reduce:lazyred -> FApi.backward

(* -------------------------------------------------------------------- *)
val t_exists_intro_s : pt_arg list -> FApi.backward

(* -------------------------------------------------------------------- *)
val t_tuple_intro_s : form pair list -> FApi.backward
val t_tuple_intro   : ?reduce:lazyred -> FApi.backward

(* -------------------------------------------------------------------- *)
(* Elimination of logical operators (backward). The top-level
 * assumption is the one that is searched for eliminiation. Do a
 * generalization first if needed. *)
val t_elim_false    : FApi.backward
val t_elim_and      : FApi.backward
val t_elim_or       : FApi.backward
val t_elim_if       : FApi.backward
val t_elim_iff      : FApi.backward
val t_elim_eq_tuple : FApi.backward
val t_elim_exists   : FApi.backward
val t_elim          : ?reduce:lazyred -> FApi.backward
val t_elim_hyp      : EcIdent.t -> FApi.backward

(* Elimination using an custom elimination principle. *)
val t_elimT_form : proofterm -> ?sk:int -> form -> FApi.backward
val t_elimT_form_global : path -> ?typ:(ty list) -> ?sk:int -> form -> FApi.backward

(* Eliminiation using an elimation principle of an induction type *)
val t_elimT_ind : ?reduce:lazyred -> [ `Case | `Ind ] -> FApi.backward

(* -------------------------------------------------------------------- *)
(* Boolean LEM                                                          *)
val t_case : form -> FApi.backward

(* -------------------------------------------------------------------- *)
(* Logical cut                                                          *)
val t_cut    : form -> FApi.backward
val t_cutdef : proofterm -> form -> FApi.backward

(* -------------------------------------------------------------------- *)
type vsubst = [
  | `Local of EcIdent.t
  | `Glob  of EcPath.mpath * EcMemory.memory
  | `PVar  of EcTypes.prog_var * EcMemory.memory
]

type subst_kind = {
  sk_local : bool;
  sk_pvar  : bool;
  sk_glob  : bool;
}

val  full_subst_kind : subst_kind
val empty_subst_kind : subst_kind

type rwspec = [`LtoR|`RtoL] * ptnpos option

val t_rewrite     : proofterm -> rwspec -> FApi.backward
val t_rewrite_hyp : EcIdent.t -> rwspec -> FApi.backward

type tside = [`All | `LtoR | `RtoL]

val t_subst:
     ?kind:subst_kind
  -> ?clear:bool
  -> ?var:vsubst
  -> ?tside:tside
  -> ?eqid:EcIdent.t
  -> FApi.backward

(* -------------------------------------------------------------------- *)
type iname  = [`Symbol of symbol      | `Ident of EcIdent.t     ]
type inames = [`Symbol of symbol list | `Ident of EcIdent.t list]

val t_intros   : ident mloc list -> FApi.backward
val t_intro_i  : ident -> FApi.backward
val t_intro_s  : iname -> FApi.backward

val t_intros_i : ident list -> FApi.backward
val t_intros_s : inames -> FApi.backward

val t_intros_i_1 : ident list -> tcenv1 -> tcenv1

val t_intros_i_seq : ?clear:bool -> ident list -> FApi.backward -> FApi.backward
val t_intros_s_seq : inames -> FApi.backward -> FApi.backward

(* -------------------------------------------------------------------- *)
val t_generalize_hyps : ?clear:bool -> EcIdent.t list -> FApi.backward
val t_generalize_hyp  : ?clear:bool -> EcIdent.t -> FApi.backward

(* -------------------------------------------------------------------- *)
val t_clear  : ident -> FApi.backward
val t_clears : ident list -> FApi.backward

(* -------------------------------------------------------------------- *)
type pgoptions =  {
  pgo_split  : bool;
  pgo_solve  : bool;
  pgo_subst  : bool;
  pgo_disjct : bool;
  pgo_delta  : pgo_delta;
}

and pgo_delta = {
  pgod_case  : bool;
  pgod_split : bool;
}

module PGOptions : sig
  val default : pgoptions
  val merge   : pgoptions -> ppgoptions -> pgoptions
end

val t_progress : 
     ?options:pgoptions -> 
     ?ti:(EcIdent.t -> EcCoreGoal.FApi.backward) ->
     FApi.backward -> FApi.backward

(* -------------------------------------------------------------------- *)
val t_congr : form pair -> form pair list * ty -> FApi.backward

(* -------------------------------------------------------------------- *)
val t_smt : strict:bool -> bool * hints -> prover_infos -> FApi.backward
