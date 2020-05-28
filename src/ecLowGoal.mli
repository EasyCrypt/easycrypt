(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-C-V1 license
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
val (@!) : FApi.backward -> FApi.backward -> FApi.backward
val (@+) : FApi.backward -> FApi.backward list -> FApi.backward
val (@>) : FApi.backward -> FApi.backward -> FApi.backward

val (@~)  : FApi.backward -> FApi.tactical -> FApi.backward
val (@!+) : FApi.tactical -> FApi.backward -> FApi.tactical
val (@~+) : FApi.tactical -> FApi.backward list -> FApi.tactical

val t_admit   : FApi.backward
val t_true    : FApi.backward
val t_fail    : FApi.backward
val t_id      : FApi.backward
val t_close   : ?who:string -> FApi.backward -> FApi.backward
val t_shuffle : EcIdent.t list -> FApi.backward

(* -------------------------------------------------------------------- *)
val alpha_find_in_hyps : EcEnv.LDecl.hyps -> EcFol.form -> EcIdent.t
val t_assumption       : [`Alpha | `Conv] -> FApi.backward
val t_absurd_hyp       : ?conv:xconv -> ?id:EcIdent.t -> FApi.backward
val t_logic_trivial    : FApi.backward
val t_trivial          : ?subtc:FApi.backward -> FApi.backward

(* -------------------------------------------------------------------- *)
type simplify_t =
  ?target:ident -> ?delta:bool -> ?logic:rlogic_info -> FApi.backward

type simplify_with_info_t =
  ?target:ident -> reduction_info -> FApi.backward

type smode = [ `Cbv | `Cbn ]

val t_cbv : simplify_t
val t_cbn : simplify_t

val t_cbv_with_info : simplify_with_info_t
val t_cbn_with_info : simplify_with_info_t

val t_simplify : ?mode:smode -> simplify_t
val t_simplify_with_info : ?mode:smode -> simplify_with_info_t

(* -------------------------------------------------------------------- *)
val t_change : ?target:ident -> form -> tcenv1 -> tcenv1

(* -------------------------------------------------------------------- *)
val t_reflex       : ?reduce:lazyred -> FApi.backward
val t_transitivity : ?reduce:lazyred -> form -> FApi.backward
val t_symmetry     : ?reduce:lazyred -> FApi.backward

(* -------------------------------------------------------------------- *)
module LowApply : sig
  type ckenv = [
    | `Tc   of rtcenv * ident option
    | `Hyps of EcEnv.LDecl.hyps * proofenv
  ]

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
module Apply : sig
  open EcMatching
  open EcProofTerm

  type reason = [`DoNotMatch | `IncompleteInference]

  exception NoInstance of (bool * reason * pt_env * (form * form))

  val t_apply_bwd_r :
    ?mode:fmoptions -> ?canview:bool -> pt_ev -> FApi.backward

  val t_apply_bwd :
    ?mode:fmoptions -> ?canview:bool -> proofterm -> FApi.backward

  val t_apply_bwd_hi:
       ?dpe:bool -> ?mode:fmoptions -> ?canview:bool
    -> proofterm -> FApi.backward
end

(* -------------------------------------------------------------------- *)
(* Introduction of logical operators (backward). *)
val t_or_intro_s  : [`Asym | `Sym] -> [`Left|`Right] -> form pair -> FApi.backward
val t_and_intro_s : [`Asym | `Sym] -> form pair -> FApi.backward
val t_iff_intro_s : form pair -> FApi.backward

val t_or_intro  : ?reduce:lazyred -> side -> FApi.backward
val t_and_intro : ?reduce:lazyred -> FApi.backward
val t_iff_intro : ?reduce:lazyred -> FApi.backward

val t_left  : ?reduce:lazyred -> FApi.backward
val t_right : ?reduce:lazyred -> FApi.backward

val t_or_intro_prind : ?reduce:lazyred -> side -> FApi.backward

(* -------------------------------------------------------------------- *)
val t_split : ?closeonly:bool -> ?reduce:lazyred -> FApi.backward
val t_split_prind : ?reduce:lazyred -> FApi.backward

(* -------------------------------------------------------------------- *)
val t_exists_intro_s : pt_arg list -> FApi.backward

(* -------------------------------------------------------------------- *)
val t_tuple_intro_s : form pair list -> FApi.backward
val t_tuple_intro   : ?reduce:lazyred -> FApi.backward

(* -------------------------------------------------------------------- *)
(* Elimination of logical operators (backward). The top-level
 * assumption is the one that is searched for elimination. Do a
 * generalization first if needed. *)
val t_elim_false    : ?reduce:lazyred -> FApi.backward
val t_elim_and      : ?reduce:lazyred -> FApi.backward
val t_elim_or       : ?reduce:lazyred -> FApi.backward
val t_elim_if       : ?reduce:lazyred -> FApi.backward
val t_elim_iff      : ?reduce:lazyred -> FApi.backward
val t_elim_eq_tuple : ?reduce:lazyred -> FApi.backward
val t_elim_exists   : ?reduce:lazyred -> FApi.backward
val t_elim          : ?reduce:lazyred -> FApi.backward
val t_elim_hyp      : EcIdent.t -> FApi.backward
val t_elim_prind    : ?reduce:lazyred -> [ `Case | `Ind ] -> FApi.backward
val t_elim_iso_and  : ?reduce:lazyred -> tcenv1 -> int * tcenv
val t_elim_iso_or   : ?reduce:lazyred -> tcenv1 -> int list * tcenv

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
type rwmode = [`Bool | `Eq]

val t_rewrite :
     ?xconv:xconv -> ?keyed:bool -> ?target:ident -> ?mode:rwmode -> ?donot:bool
  -> proofterm -> rwspec -> FApi.backward

val t_rewrite_hyp :
     ?xconv:xconv -> ?mode:rwmode -> ?donot:bool -> EcIdent.t
  -> rwspec -> FApi.backward

type tside = [`All of [`LtoR | `RtoL] option | `LtoR | `RtoL]

val t_subst:
     ?kind:subst_kind
  -> ?tg:Sid.t
  -> ?clear:bool
  -> ?var:vsubst
  -> ?tside:tside
  -> ?eqid:EcIdent.t
  -> FApi.backward

(* -------------------------------------------------------------------- *)
type iname  = [
  | `Symbol of symbol
  | `Fresh
  | `Ident  of EcIdent.t
]

type inames = [`Symbol of symbol list | `Ident of EcIdent.t list]

val t_intros   : ident mloc list -> FApi.backward
val t_intro_i  : ident -> FApi.backward
val t_intro_s  : iname -> FApi.backward

val t_intros_i : ident list -> FApi.backward
val t_intros_s : inames -> FApi.backward

val t_intros_i_1 : ident list -> tcenv1 -> tcenv1

val t_intros_i_seq : ?clear:bool -> ident list -> FApi.backward -> FApi.backward
val t_intros_s_seq : inames -> FApi.backward -> FApi.backward

val t_intros_n : int -> FApi.backward

(* -------------------------------------------------------------------- *)
type genclear = [`Clear | `TryClear | `NoClear]

val t_generalize_hyps_x :
     ?missing:bool
  -> ?naming:(ident -> symbol option)
  -> ?letin:bool
  -> (genclear * EcIdent.t) list
  -> FApi.backward

val t_generalize_hyps :
     ?clear:[`Yes|`No|`Try] -> ?missing:bool
  -> ?naming:(ident -> symbol option)
  -> ?letin:bool
  -> EcIdent.t list -> FApi.backward

val t_generalize_hyp  :
     ?clear:[`Yes|`No|`Try] -> ?missing:bool
  -> ?naming:(ident -> symbol option)
  -> ?letin:bool
  -> EcIdent.t -> FApi.backward

(* -------------------------------------------------------------------- *)
val t_clear1  : ?leniant:bool -> ident -> tcenv1 -> tcenv1
val t_clears1 : ?leniant:bool -> ident list -> tcenv1 -> tcenv1

val t_clear  : ?leniant:bool -> ident -> FApi.backward
val t_clears : ?leniant:bool -> ident list -> FApi.backward

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
val t_crush     : ?delta:bool -> ?tsolve:FApi.backward -> FApi.backward
val t_crush_fwd : ?delta:bool -> int -> FApi.backward

(* -------------------------------------------------------------------- *)
val t_congr : form pair -> form pair list * ty -> FApi.backward

(* -------------------------------------------------------------------- *)
type smtmode = [`Standard | `Strict | `Report of EcLocation.t option]

val t_smt: mode:smtmode -> prover_infos -> FApi.backward

(* -------------------------------------------------------------------- *)
val t_solve : ?canfail:bool -> ?bases:symbol list -> ?depth:int -> FApi.backward
