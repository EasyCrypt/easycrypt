(* --------------------------------------------------------------------
 * Copyright (c) - 2012-2015 - IMDEA Software Institute and INRIA
 * Distributed under the terms of the CeCILL-C license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcUtils
open EcIdent
open EcSymbols
open EcTypes
open EcFol
open EcEnv

(* -------------------------------------------------------------------- *)
type location = {
  plc_parent : location option;
  plc_name   : string option;
  plc_loc    : EcLocation.t;
}

exception TcError of bool * location option * string Lazy.t

(* -------------------------------------------------------------------- *)
exception InvalidGoalShape

(* -------------------------------------------------------------------- *)
type clearerror = [
  | `ClearInGoal of EcIdent.t list
  | `ClearDep    of EcIdent.t pair
]

exception ClearError of clearerror Lazy.t

(* -------------------------------------------------------------------- *)
(* Proof-node ID                                                        *)
(* -------------------------------------------------------------------- *)
type handle

val eq_handle : handle -> handle -> bool

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

(* -------------------------------------------------------------------- *)
val is_ptcut    : pt_head -> bool
val is_pthandle : pt_head -> bool
val is_ptlocal  : pt_head -> bool
val is_ptglobal : pt_head -> bool

(* -------------------------------------------------------------------- *)
val is_paformula : pt_arg -> bool
val is_pamemory  : pt_arg -> bool
val is_pamodule  : pt_arg -> bool
val is_pasub     : pt_arg -> bool

val paformula : EcFol.form -> pt_arg
val pamemory  : EcMemory.memory -> pt_arg
val pamodule  : EcPath.mpath * EcModules.module_sig -> pt_arg
val paglobal  : EcPath.path -> ty list -> pt_arg
val palocal   : EcIdent.t -> pt_arg

(* -------------------------------------------------------------------- *)
(* EasyCrypt rewrite proof-term:                                        *)
(*  rwpt := pt * position list * local hyp                              *)
(*    <pt>: equality-proof term                                         *)
(*                                                                      *)
(*  position := EcMatching.ptnpos - pattern position                    *)
(* -------------------------------------------------------------------- *)
type rwproofterm = {
  rpt_proof : proofterm;
  rpt_occrs : EcMatching.ptnpos option;
  rpt_lc    : ident option;
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
 * manipulated explicitely via tacticals.
 *
 * A [tcenv1] is a [tcenv] where it is statically known that the focused
 * goal has sibling goals. A coercion is given from [tcenv1] to [tcenv].
 *)

type proof
type proofenv
type tcenv1
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
| VLConv   of (handle * ident)       (* hypothesis conversion *)
| VRewrite of (handle * rwproofterm) (* rewrite *)
| VApply   of proofterm              (* modus ponens *)

  (* external (hl/phl/prhl/...) proof-node *)
| VExtern  : 'a * handle list -> validation

(* -------------------------------------------------------------------- *)
val tcenv1_of_proof   : proof  -> tcenv1
val tcenv_of_proof    : proof  -> tcenv
val proof_of_tcenv    : tcenv  -> proof
val proofenv_of_proof : proof  -> proofenv

(* Start a new interactive proof in a given local context
 * [LDecl.hyps] for given [form]. Mainly, a [proof] records the set
 * of all goals (closed or not - i.e. a proof-environment) + the list
 * of opened, top-level goals. *)
val start : LDecl.hyps -> form -> proof

(* Return the first opened goal of this interactive proof and the
 * number of open goals. *)
val opened : proof -> (int * pregoal) option

(* Return the list of opened goals - by handle *)
val all_hd_opened : proof -> handle list

(* Return the list of opened goals - by pregoal *)
val all_opened : proof -> pregoal list

(* Check if a proof is done *)
val closed : proof -> bool

(* -------------------------------------------------------------------- *)
val tc_error :
     proofenv -> ?catchable:bool -> ?loc:EcLocation.t -> ?who:string
  -> ('a, Format.formatter, unit, 'b) format4 -> 'a

val tacuerror : ?catchable:bool -> ('a, Format.formatter, unit, 'b) format4 -> 'a

val tc_error_lazy :
     proofenv -> ?catchable:bool -> ?loc:EcLocation.t -> ?who:string
  -> (Format.formatter -> unit) -> 'a

val tc_error_clear :
     proofenv -> ?catchable:bool -> ?loc:EcLocation.t -> ?who:string
  -> clearerror Lazy.t -> 'a

(* -------------------------------------------------------------------- *)
type symkind = [`Lemma | `Operator | `Local]

val tc_lookup_error :
  proofenv -> ?loc:EcLocation.t -> ?who:string -> symkind -> qsymbol -> 'a

(* -------------------------------------------------------------------- *)
val reloc : EcLocation.t -> ('a -> 'b) -> 'a -> 'b

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
   *)

  exception InvalidStateException of string

  type forward   = proofenv -> proofenv * handle
  type backward  = tcenv1 -> tcenv
  type ibackward = int -> backward
  type tactical  = tcenv -> tcenv

  val tcenv_of_tcenv1 : tcenv1 -> tcenv
  val as_tcenv1 : tcenv -> tcenv1

  val get_pregoal_by_id : handle -> proofenv -> pregoal

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
  val mutate  : tcenv  -> (handle -> validation) -> ?hyps:LDecl.hyps -> form -> tcenv
  val mutate1 : tcenv1 -> (handle -> validation) -> ?hyps:LDecl.hyps -> form -> tcenv1

  (* Same as xmutate, but for an external node resolution depending on
   * a unbounded numbers of premises. The ['a] argument is the external
   * validation node. *)
  val xmutate  : tcenv  -> 'a -> form list -> tcenv
  val xmutate1 : tcenv1 -> 'a -> form list -> tcenv

  val xmutate_hyps  : tcenv  -> 'a -> (LDecl.hyps * form) list -> tcenv
  val xmutate1_hyps : tcenv1 -> 'a -> (LDecl.hyps * form) list -> tcenv

  (* Apply a forward tactic to a backward environment, using the
   * proof-environment of the latter *)
  val bwd1_of_fwd  : forward -> tcenv1 -> tcenv1 * handle
  val  bwd_of_fwd  : forward -> tcenv  -> tcenv  * handle

  (* Insert a new fact in a proof-environment *)
  val newfact :
       proofenv -> validation -> LDecl.hyps -> form
    -> proofenv * handle

  (* Check if a tcenv is closed (no focused goal *)
  val tc_done   : tcenv -> bool
  val tc_count  : tcenv -> int
  val tc_opened : tcenv -> handle list

  (* Accessors for focused goal parts (tcenv) *)
  val tc_handle  : tcenv -> handle
  val tc_penv    : tcenv -> proofenv
  val tc_goal    : tcenv -> form
  val tc_env     : tcenv -> EcEnv.env
  val tc_flat    : ?target:ident -> tcenv -> LDecl.hyps * form
  val tc_eflat   : ?target:ident -> tcenv -> env * LDecl.hyps * form
  val tc_hyps    : ?target:ident -> tcenv -> LDecl.hyps

  (* Accessors for focused goal parts (tcenv1) *)
  val tc1_handle : tcenv1 -> handle
  val tc1_penv   : tcenv1 -> proofenv
  val tc1_flat   : ?target:ident -> tcenv1 -> LDecl.hyps * form
  val tc1_eflat  : ?target:ident -> tcenv1 -> env * LDecl.hyps * form
  val tc1_hyps   : ?target:ident -> tcenv1 -> LDecl.hyps
  val tc1_goal   : tcenv1 -> form
  val tc1_env    : tcenv1 -> EcEnv.env

  (* Low-level tactic markers *)
  val t_low0 : string -> backward -> backward
  val t_low1 : string -> ('a -> backward) -> 'a -> backward
  val t_low2 : string -> ('a -> 'b -> backward) -> ('a -> 'b -> backward)
  val t_low3 : string -> ('a -> 'b -> 'c -> backward) -> ('a -> 'b -> 'c -> backward)
  val t_low4 : string -> ('a -> 'b -> 'c -> 'd -> backward) ->  ('a -> 'b -> 'c -> 'd -> backward)

  (* Tacticals *)
  type direction = [ `Left | `Right ]
  type tfocus    = (int -> bool)

  val t_focus      : backward -> tactical
  val t_onalli     : (int -> backward) -> tactical
  val t_onall      : backward -> tactical
  val t_onfsub     : (int -> backward option) -> tactical
  val t_onselecti  : tfocus -> ?ttout:ibackward -> ibackward -> tactical
  val t_onselect   : tfocus -> ?ttout:backward -> backward -> tactical
  val t_on1        : int -> ?ttout:backward -> backward -> tactical
  val t_firsts     : backward -> int -> tactical
  val t_lasts      : backward -> int -> tactical
  val t_subfirsts  : backward list -> tactical
  val t_sublasts   : backward list -> tactical
  val t_first      : backward -> tactical
  val t_last       : backward -> tactical
  val t_rotate     : direction -> int -> tactical
  val t_swap_goals : int -> int -> tactical

  val t_sub    : backward list -> tactical

  val t_seq    : backward -> backward -> backward
  val t_seqs   : backward list -> backward

  val t_seqsub : backward -> backward list -> backward
  val t_on1seq : int -> backward -> ?ttout:backward -> backward -> backward

  val t_try    : backward -> backward
  val t_switch : ?on:[`All|`Focus] -> backward -> ifok:backward -> iffail:backward -> backward
  val t_do_r   : ?focus:int -> [`All | `Maybe] -> int option -> backward -> tcenv -> tcenv
  val t_do     : [`All | `Maybe] -> int option -> backward -> backward
  val t_repeat : backward -> backward

  val t_or       : backward -> backward -> backward
  val t_ors_pmap : ('a -> backward option) -> 'a list -> backward
  val t_ors_map  : ('a -> backward) -> 'a list -> backward
  val t_ors      : backward list -> backward

  val t_internal : ?info:string -> backward -> backward
end

val (!!) : tcenv1 -> proofenv
val (!$) : tcenv  -> proofenv
val (!@) : tcenv1 -> tcenv

(* -------------------------------------------------------------------- *)
(* Imperative API                                                       *)
(* -------------------------------------------------------------------- *)
module RApi : sig
  type rproofenv
  type rtcenv

  val rtcenv_of_tcenv  : tcenv  -> rtcenv
  val  tcenv_of_rtcenv : rtcenv ->  tcenv
  val rtcenv_of_tcenv1 : tcenv1 -> rtcenv

  (* For the following functions, see the [FApi] module *)
  val pf_get_pregoal_by_id : handle -> rproofenv -> pregoal
  val tc_get_pregoal_by_id : handle -> rtcenv -> pregoal

  val newgoal : rtcenv -> ?hyps:LDecl.hyps -> form -> handle
  val close   : rtcenv -> validation -> unit

  val bwd_of_fwd : FApi.forward -> rtcenv  -> handle

  (* Accessors for focused goal parts (rtcenv) *)
  val tc_penv  : rtcenv -> proofenv
  val tc_flat  : ?target:ident -> rtcenv -> LDecl.hyps * form
  val tc_eflat : ?target:ident -> rtcenv -> env * LDecl.hyps * form
  val tc_hyps  : ?target:ident -> rtcenv -> LDecl.hyps
  val tc_goal  : rtcenv -> form
  val tc_env   : rtcenv -> env

  (* Recast a rtcenv-imperative function as a tcenv-pure function. *)
  val of_pure_u : ( tcenv -> tcenv) -> rtcenv -> unit
  val to_pure_u : (rtcenv -> unit ) ->  tcenv -> tcenv

  val of_pure : (tcenv -> 'a * tcenv) -> rtcenv -> 'a
  val to_pure : (rtcenv -> 'a) -> tcenv -> tcenv * 'a

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
  val recast_pe  : proofenv -> LDecl.hyps -> (unit -> 'a) -> 'a
  val recast_tc  : tcenv -> (LDecl.hyps -> 'a) -> 'a
  val recast_tc1 : tcenv1 -> (LDecl.hyps -> 'a) -> 'a
end
