(* -------------------------------------------------------------------- *)
open EcLocation
open EcUtils
open EcIdent
open EcPath
open EcTypes
open EcFol
open EcCoreGoal

(* -------------------------------------------------------------------- *)
exception InvalidProofTerm         (* invalid proof term *)
exception InvalidGoalShape         (* invalid goal shape for tactic *)

type side = [`Left|`Right]

(* -------------------------------------------------------------------- *)
val t_admit : FApi.backward
val t_true  : FApi.backward

(* -------------------------------------------------------------------- *)
val t_reflex : ?reduce:bool -> FApi.backward

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
val t_or_intro_s  : bool -> [`Left|`Right] -> form pair -> FApi.backward
val t_and_intro_s : bool -> form pair -> FApi.backward
val t_iff_intro_s : form pair -> FApi.backward

val t_or_intro  : ?reduce:bool -> side -> FApi.backward
val t_and_intro : ?reduce:bool -> FApi.backward
val t_iff_intro : ?reduce:bool -> FApi.backward

val t_left  : ?reduce:bool -> FApi.backward
val t_right : ?reduce:bool -> FApi.backward
val t_split : FApi.backward

(* -------------------------------------------------------------------- *)
val t_tuple_intro_s : form pair list -> FApi.backward
val t_tuple_intro   : ?reduce:bool -> FApi.backward

(* -------------------------------------------------------------------- *)
val t_elim : FApi.backward

(* -------------------------------------------------------------------- *)
val t_cut : form -> FApi.backward

(* -------------------------------------------------------------------- *)
val t_rewrite : proofterm -> EcMatching.ptnpos -> FApi.backward

(* -------------------------------------------------------------------- *)
val t_intros  : ident mloc list -> FApi.backward
val t_intro_i : ident -> FApi.backward
