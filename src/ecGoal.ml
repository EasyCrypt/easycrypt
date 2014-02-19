(* -------------------------------------------------------------------- *)
open EcIdent
open EcTypes
open EcFol
open EcEnv

(* -------------------------------------------------------------------- *)
module ID : sig
  type id = private int

  val gen : unit -> int

  module Map : EcMaps.Map.S with type key = id
end = struct
  type id = int

  let gen () = EcUid.unique ()

  module Map = EcMaps.Mint
end

(* -------------------------------------------------------------------- *)
type handle = ID.id

(* -------------------------------------------------------------------- *)
(* EasyCrypt proof-term:                                                *)
(*                                                                      *)
(*  pt ::= pt-head pt-arg*                                              *)
(*                                                                      *)
(*  pt-head ::=                                                         *)
(*   |  form<ft>                   (cut <ft> - generate subgoal         *)
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
type proof = {
  pr_env   : proofenv;
  pr_goals : handle list;
}

and proofenv = {
  pr_uid   : ID.id;          (* unique ID for this proof *)
  pr_main  : ID.id;          (* top goal, contains the final result *)
  pr_goals : goal ID.Map.t;  (* set of all goals, closed and opened *)
}

and pregoal = {
  g_uid   : ID.id;                      (* this goal ID *)
  g_hyps  : LDecl.hyps;                 (* goal local environment *)
  g_concl : form;                       (* goal conclusion *)
}

and goal = {
  g_goal       : pregoal;
  g_validation : validation;
}

and validation =
| VSmt     : validation                 (* SMT call *)
| VAdmit   : validation                 (* admit *)
| VConv    : Sid.t                      (* weakening + conversion *)
| VApply   : proofterm -> validation    (* modus ponens *)
| VRewrite : rwproofterm -> validation  (* rewrite *)
| VExtern  : 'a -> validation           (* external (hl/phl/prhl/...) proof-node *)

and tcenv = {
  tce_proofenv   : proofenv;           (* top-level proof environment *)
  tce_goal       : pregoal;            (* local goal *)
  tce_subgoals   : pregoal list;       (* generated subgoals *)
  tce_validation : validation option;  (* pending validation *)
}

and location = {
  plc_parent : location option;
  plc_name   : string;
  plc_loc    : EcLocation.t;
}

(* -------------------------------------------------------------------- *)
(* Functional API                                                       *)
(* -------------------------------------------------------------------- *)
module type Api = sig
  (* - [forward tactic]: take a proofenv, i.e. a set of goals (proven or
   *   not) and generate a new (1-level proven) goal [handle]. Examples
   *   of such tactics are forward congruence or closed rewriting.
   *
   * - [backward tactic]: take a tcenv, i.e. a opened goal, and make
   *   progress over it, potentially creating new subgoals. Examples of
   *   such tactics are backward apply, rewriting, backward congruence.
   *
   * - [mixward tactic]: take a tcenv a apply a forward tactic to its
   *   associated proof-environment, potentially creating subgoals.
   *   Examples of such tactics are forward apply, conditional closed
   *   rewriting.
   *)

  type 'a forward  = 'a -> proofenv -> proofenv * handle
  type 'a backward = 'a -> tcenv -> tcenv
  type 'a mixward  = 'a -> tcenv -> tcenv * handle

  val create : LDecl.hyps -> form -> proof

  val newgoal : tcenv -> ?hyps:LDecl.hyps -> form -> tcenv * handle
  val close   : tcenv -> validation -> tcenv
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
