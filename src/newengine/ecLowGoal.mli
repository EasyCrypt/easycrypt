(* -------------------------------------------------------------------- *)
open EcLocation
open EcIdent
open EcPath
open EcTypes
open EcFol
open EcCoreGoal

(* -------------------------------------------------------------------- *)
exception InvalidProofTerm

(* -------------------------------------------------------------------- *)
val t_admit   : FApi.backward

(* -------------------------------------------------------------------- *)

(* Main low-level MP tactic. Tactic a fully constructed proof-term to
 * the focused goal. If the proof-term contains PTCut-terms, create the
 * related subgoals. If [focus] is [true], do the MP in the context of
 * the focus goal - see [FApi.oncurrent]. Raise [InvalidProofTerm] is
 * the proof-term is not valid (not typable or not a proof of the
 * focused goal). *)
val t_apply : ?focus:bool -> proofterm -> FApi.backward

(* Apply a proof term of the forms [p<:ty1...tyn> f1...fp _ ... _]
 * constructed for the path, type parameters, and formulas given to
 * the function. The [int] argument gives the number of premises to
 * skip before applying [p]. *)
val t_apply_s :
  ?focus:bool -> path -> ty list -> form list -> int -> FApi.backward

(* -------------------------------------------------------------------- *)
val t_cut : form -> FApi.backward

(* -------------------------------------------------------------------- *)
val t_rewrite : proofterm -> EcMatching.ptnpos -> FApi.backward

(* -------------------------------------------------------------------- *)
val t_intros  : ident mloc list -> FApi.backward
val t_intro_i : ident -> FApi.backward
