(* -------------------------------------------------------------------- *)
open EcIdent
open EcSymbols
open EcParsetree
open EcTypes
open EcDecl
open EcFol
open EcEnv

(* -------------------------------------------------------------------- *)
type location = {
  plc_parent : location option;
  plc_name   : string;
  plc_loc    : EcLocation.t;
}

exception TcError of location * string Lazy.t

(* -------------------------------------------------------------------- *)
(* Proof-node ID                                                        *)
(* -------------------------------------------------------------------- *)
type handle

(* -------------------------------------------------------------------- *)
(* EasyCrypt proof-term:                                                *)
(*                                                                      *)
(*  pt ::= pt-head pt-arg*                                              *)
(*                                                                      *)
(*  pt-head ::=                                                         *)
(*   |  form<ft>                   (cut <ft> - generate subgoal)        *)
(*   |  handle                     (formula associated to <handle>)     *)
(*   |  local<id>                  (local hypothesis <id>)              *)
(*   |  global<p,tyargs>           (global lemma <p<:tyargs>>)          *)
(*                                                                      *)
(* pt-arg ::=                                                           *)
(*   | formula                     (∀-elimination)                      *)
(*   | memory                      (∀[mem]-elimination)                 *)
(*   | module-path                 (∀[mod]-elimination)                 *)
(*   | pt                          (⇒-elimination)                      *)
(* -------------------------------------------------------------------- *)

type proofterm = { pt_head : pt_head; pt_args : pt_arg list; }

and pt_head =
| PTCut    of EcFol.form
| PTHandle of handle
| PTLocal  of EcIdent.t
| PTGlobal of EcPath.path * (ty list)

and pt_arg =
| PAFormula of EcFol.form
| PAMemory  of EcMemory.memory
| PAModule  of (EcPath.mpath * EcModules.module_sig)
| PASub     of proofterm option

val paformula : EcFol.form -> pt_arg
val pamemory  : EcMemory.memory -> pt_arg
val pamodule  : EcPath.mpath * EcModules.module_sig -> pt_arg

(* -------------------------------------------------------------------- *)
(* EasyCrypt rewrite proof-term:                                        *)
(*  rwpt := pt * position list                                          *)
(*    <pt>: equality-proof term                                         *)
(*                                                                      *)
(*  position := EcMatching.ptnpos - pattern position                    *)
(* -------------------------------------------------------------------- *)
type rwproofterm = {
  rpt_proof : proofterm;
  rpt_occrs : EcMatching.ptnpos;
}

(* -------------------------------------------------------------------- *)
(* The type [proof] represents the state an interactive proof at top
 * level, i.e. the set of goals (opened or closed) + the list of
 * opened, top-level goals. It cannot be use for proof-progress. Instead,
 * a [proofenv] or [tcenv] must be created (resp. for forward / backward
 * reasoning) first.
 *
 * A [proofenv] represents the set of goals (opened or closed) of a given
 * [proof]. An API is provided that allows the creation of new *closed*
 * goals, i.e. for doing forward reasoning from existing (proven or not)
 * facts.
 *
 * A [tcenv] represents the set of opened goals of a given [proof]. These
 * goals are organized as a tree + a focus (i.e. a pointed leaf of the
 * tree). An API is provided allowing reasoning in a mix of backward /
 * forward reasoning, creating open of closed goals or solving the
 * current focus. The [tcenv] handle the focus automatically when goals
 * are created, closed or when composing tactics; but can also be
 * manipulated explicitely via tacticals. *)

type proof
type proofenv
type tcenv

type pregoal = {
  g_uid   : handle;
  g_hyps  : LDecl.hyps;
  g_concl : form;
}

type validation =
| VSmt                               (* SMT call *)
| VAdmit                             (* admit *)
| VIntros  of (handle * idents)      (* intros *)
| VConv    of (handle * Sid.t)       (* weakening + conversion *)
| VRewrite of (handle * rwproofterm) (* rewrite *)
| VApply   of proofterm              (* modus ponens *)

| VExtern  : 'a * handle list -> validation (* external (hl/phl/prhl/...) proof-node *)

(* -------------------------------------------------------------------- *)
val tcenv_of_proof : proof -> tcenv
val proof_of_tcenv : tcenv -> proof

(* Start a new interactive proof in a given local context
 * [LDecl.hyps] for given [form]. Mainly, a [proof] records the set
 * of all goals (closed or not - i.e. a proof-environment) + the list
 * of opened, top-level goals. *)
val start : LDecl.hyps -> form -> proof

(* Return the first opened goal of this interactive proof and the
 * number of open goals. *)
val opened : proof -> (int * pregoal) option

(* -------------------------------------------------------------------- *)
val tc_error :
  proofenv -> ?loc:EcLocation.t -> string -> 'a

val tc_lookup_error :
  proofenv -> ?loc:EcLocation.t -> [`Lemma] -> qsymbol -> 'a

(* -------------------------------------------------------------------- *)
(* Functional API                                                       *)
(* -------------------------------------------------------------------- *)
module FApi : sig
  (* - [forward tactic]: take a proofenv, i.e. a set of goals (proven or
   *   not) and generate a new (1-level proven) goal [handle]. Examples
   *   of such tactics are forward congruence or closed rewriting.
   *
   * - [backward tactic]: take a tcenv, i.e. an opened goal, and make
   *   progress over it, potentially creating new subgoals. Examples of
   *   such tactics are backward apply, rewriting, backward congruence.
   *
   * - [mixward tactic]: take a tcenv a apply a forward tactic to its
   *   associated proof-environment, potentially creating subgoals.
   *   Examples of such tactics are forward apply, conditional closed
   *   rewriting.
   *)

  exception InvalidStateException of string

  type forward  = proofenv -> proofenv * handle
  type backward = tcenv -> tcenv
  type mixward  = tcenv -> tcenv * handle

  (* Create a new opened goal for the given [form] in the backward
   * environment [tcenv]. If no local context [LDecl.hyps] is given,
   * use the one of the focused goal in [tcenv] -- it is then an
   * internal error is no goal is focused. By default, the goal is
   * created as the last sibling of the current focus. Return the
   * mutated [tcenv] along with the handle of the new goal. *)
  val newgoal : tcenv -> ?hyps:LDecl.hyps -> form -> tcenv * handle

  (* Mark the focused goal in [tcenv] as solved using the given
   * [validation]. It is an internal error if no goal is focused. The
   * focus is then changed to the next opened sibling. *)
  val close : tcenv -> validation -> tcenv

  (* Mutate current goal in [tcenv]. Focused goal will be marked as
   * resolved using the given [validation] producer. This producer is
   * applied to the goal freshly created, using given formulas and
   * focused goal local context. *)
  val mutate : tcenv -> (handle -> validation) -> form -> tcenv

  (* Same as xmutate, but for an external node resolution depending on
   * a unbounded numbers of premises. The ['a] argument is the external
   * validation node. *)
  val xmutate : tcenv -> 'a -> form list -> tcenv

  (* Apply a forward tactic to a backward environment, using the
   * proof-environment of the latter *)
  val bwd_of_fwd : forward -> tcenv -> tcenv * handle

  (* Insert a new fact in a proof-environment *)
  val newfact :
       proofenv -> validation -> LDecl.hyps -> form
    -> proofenv * handle

  (* Accessors for focused goal parts *)
  val tc_penv  : tcenv -> proofenv
  val tc_flat  : tcenv -> LDecl.hyps * form
  val tc_eflat : tcenv -> env * LDecl.hyps * form
  val tc_hyps  : tcenv -> LDecl.hyps
  val tc_goal  : tcenv -> form

  (* Tacticals *)
  type ontest    = int -> proofenv -> handle -> bool
  type direction = [ `Left | `Right ]

  val on     : backward -> ontest -> tcenv -> tcenv
  val first  : backward -> int -> tcenv -> tcenv
  val last   : backward -> int -> tcenv -> tcenv
  val rotate : direction -> int -> tcenv -> tcenv

  val seq  : backward -> backward -> tcenv -> tcenv
  val lseq : backward list -> tcenv -> tcenv

  val seq_subgoal : backward -> backward list -> backward
end

val (!!) : tcenv -> proofenv

(* -------------------------------------------------------------------- *)
(* Imperative API                                                       *)
(* -------------------------------------------------------------------- *)
module RApi : sig
  type rproofenv
  type rtcenv

  val rtcenv_of_tcenv  : tcenv  -> rtcenv
  val  tcenv_of_rtcenv : rtcenv ->  tcenv

  (* For the following functions, see the [FApi] module *)
  val pf_get_pregoal_by_id : handle -> rproofenv -> pregoal
  val tc_get_pregoal_by_id : handle -> rtcenv -> pregoal

  val newgoal : rtcenv -> ?hyps:LDecl.hyps -> form -> handle
  val close   : rtcenv -> validation -> unit

  val bwd_of_fwd : FApi.forward -> rtcenv -> handle

  (* Accessors for focused goal parts *)
  val tc_penv  : rtcenv -> proofenv
  val tc_flat  : rtcenv -> LDecl.hyps * form
  val tc_eflat : rtcenv -> env * LDecl.hyps * form
  val tc_hyps  : rtcenv -> LDecl.hyps
  val tc_goal  : rtcenv -> form

  (* Recast a rtcenv-imperative function as a tcenv-pure function. *)
  val of_pure   : tcenv  -> (rtcenv -> 'a) -> 'a * tcenv
  val to_pure   : rtcenv -> (tcenv -> tcenv * 'a) -> 'a
  val to_pure_u : rtcenv -> (tcenv -> tcenv) -> unit

  (* [freeze] returns a copy of the input [rtcenv], whereas [restore]
   * copies the contents of [src:rtcenv] to [dst:rtcenv]. These
   * operations are done in constant time. *)
  val freeze  : rtcenv -> rtcenv
  val restore : dst:rtcenv -> src:rtcenv -> unit
end

type rproofenv = RApi.rproofenv
type rtcenv    = RApi.rtcenv

(* -------------------------------------------------------------------- *)
module Exn : sig
  (* Apply the given function in the context of a proof-environment,
   * adding some more location informations when a typing error is
   * raised *)
  val recast_pe : proofenv -> (unit -> 'a) -> 'a
  val recast_tc : tcenv -> (LDecl.hyps -> 'a) -> 'a
end

(* -------------------------------------------------------------------- *)
module TcTyping : sig
  (* Top-level typing functions, but applied in the context of a
   * proof-environment. See the [Exn] module for more information. *)

  val unienv_of_hyps : LDecl.hyps -> EcUnify.unienv
  val pf_check_tvi   : proofenv -> ty_params -> EcUnify.tvi -> unit

  (* Typing in the environment implied by [LDecl.hyps]. *)
  val process_form_opt : LDecl.hyps -> pformula -> ty option -> form
  val process_form     : LDecl.hyps -> pformula -> ty -> form
  val process_formula  : LDecl.hyps -> pformula -> form

  (* Typing in the [LDecl.hyps] implied by the proof env.
   * Typing exceptions are recasted in the proof env. context *)
  val pf_process_form_opt : proofenv -> LDecl.hyps -> pformula -> ty option -> form
  val pf_process_form     : proofenv -> LDecl.hyps -> pformula -> ty -> form
  val pf_process_formula  : proofenv -> LDecl.hyps -> pformula -> form

  (* Typing in the [proofenv] implies for the [tcenv].
   * Typing exceptions are recasted in the proof env. context *)
  val tc_process_form_opt : tcenv -> pformula -> ty option -> form
  val tc_process_form     : tcenv -> pformula -> ty -> form
  val tc_process_formula  : tcenv -> pformula -> form
end
