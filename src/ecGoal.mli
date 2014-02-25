(* -------------------------------------------------------------------- *)
open EcIdent
open EcTypes
open EcEnv
open EcFol

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
| PASub     of proofterm

(* -------------------------------------------------------------------- *)
(* EasyCrypt rewrite proof-term:                                        *)
(*  rwpt := pt * position list                                          *)
(*    <pt>: equality-proof term                                         *)
(*                                                                      *)
(*  position := term position (to be defined)                           *)
(* -------------------------------------------------------------------- *)
type position

type rwproofterm = {
  rpt_proof : proofterm;
  rtp_occrs : position list;
}

(* -------------------------------------------------------------------- *)
type proof
type proofenv
type tcenv

type pregoal = {
  g_uid   : handle;
  g_hyps  : LDecl.hyps;
  g_concl : form;
}

type validation =
| VSmt     : validation                 (* SMT call *)
| VAdmit   : validation                 (* admit *)
| VConv    : Sid.t -> validation        (* weakening + conversion *)
| VApply   : proofterm -> validation    (* modus ponens *)
| VRewrite : rwproofterm -> validation  (* rewrite *)
| VExtern  : 'a -> validation           (* external (hl/phl/prhl/...) proof-node *)


(* -------------------------------------------------------------------- *)
(* Functional API                                                       *)
(* -------------------------------------------------------------------- *)
module Api : sig
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

  val start   : LDecl.hyps -> form -> proof
  val focused : proof -> (int * pregoal) option

  val newgoal : tcenv -> ?hyps:LDecl.hyps -> form -> tcenv * handle
  val close   : tcenv -> validation -> tcenv

  (* Tacticals *)
  type ontest    = int -> proofenv -> handle -> bool
  type direction = [ `Left | `Right ]

  val on     : backward -> ontest -> tcenv -> tcenv
  val first  : backward -> int -> tcenv -> tcenv
  val last   : backward -> int -> tcenv -> tcenv
  val rotate : direction -> int -> tcenv -> tcenv

  val seq  : backward -> backward -> tcenv -> tcenv
  val lseq : backward list -> tcenv -> tcenv
end

(* -------------------------------------------------------------------- *)
(* Imperative API                                                       *)
(* -------------------------------------------------------------------- *)
module type IApi = sig
  type rprooftree
  type rtcenv
  type rtcenvs

  (* Same API as [Api], but mutating the state. We also provide
   * a freeze/thaw couple of operations. *)
  val freeze : rtcenv -> rtcenv
  val thaw   : rtcenv -> rtcenv

  (* + missing syntax for easing goals manipulations (using ocaml ppx) *)
end

(* -------------------------------------------------------------------- *)
module HiLevel : sig
  open EcParsetree

  val apply : ptactic list -> proof -> proof
end
