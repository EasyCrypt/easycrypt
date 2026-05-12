(* -------------------------------------------------------------------- *)
open EcCoreGoal

(* -------------------------------------------------------------------- *)
(* Two-sided rules for the delayed-coupling logic (paper §4.1).         *)

(* Skip: closes a dcoupl goal whose bodies are empty and whose
   continuations match their delay contexts; produces one subgoal
   [forall m1 m2, phi m1 m2 => psi m1 m2].                             *)
val t_dc_skip : FApi.backward

(* Seq: splits each body at the given position [nl], [nr] and generates
   two subgoals around the intermediate predicate [theta]. The
   intermediate R-contexts default to [R_i; C_i] when [ts] is omitted;
   otherwise [ts] = (T_l, T_r) overrides them.                        *)
val t_dc_seq :
     nl:int
  -> nr:int
  -> ?ts:(EcAst.stmt * EcAst.stmt)
  -> EcAst.form
  -> FApi.backward

(* If: the body on each side must be a single [if] instruction. Three
   subgoals are produced (test equivalence, then-branch, else-branch).
   Side condition: [Write(R_i)] disjoint from [Fv(e_i)] (checked). *)
val t_dc_if : FApi.backward

(* While: the body on each side is a single [while] instruction. The
   caller must have pre-arranged the shape [S_i = R_i] and post
   [pre /\ not e1]. Two subgoals are produced (test equivalence, body
   preserves the invariant). Side condition: [Write(R_i)] disjoint
   from [Fv(e_i)] (checked). *)
val t_dc_while : inv:EcAst.ts_inv -> ?invr1:EcAst.stmt -> ?invr2:EcAst.stmt -> FApi.backward

(* Rnd: the body on each side is a single random assignment [x <$ d].
   The caller must have [S_i = R_i]. Side conditions: [Write(R_i)]
   disjoint from [{x_i} ∪ Fv(d_i)], and [x_i] not in [Read(R_i)].
   The user supplies a bijection [(f, f_inv)] as type-indexed builders;
   pass [None] to default to the identity (requires equal carrier
   types). One subgoal is produced with a transformed precondition.  *)
type dc_bij_builder = EcTypes.ty -> EcTypes.ty -> EcAst.ts_inv

val t_dc_rnd :
  (dc_bij_builder * dc_bij_builder) option -> FApi.backward

(* ---- One-sided (paper §4.2) variants ------------------------------ *)

(* Symmetry: swap left and right in a dcoupl goal. *)
val t_dc_sym : FApi.backward

(* One-sided If. *)
val t_dc_if_side : side:[`Left | `Right] -> FApi.backward

(* One-sided Assign (other-side body must be empty). *)
val t_dc_asgn_side : [`Left | `Right] -> FApi.backward

(* One-sided Rnd (other-side body must be empty; [S_i = R_i]). *)
val t_dc_rnd_side : side:[`Left | `Right] -> FApi.backward

(* One-sided While (other-side body empty; [S_i = R_i]; post = pre /\ ¬e). *)
val t_dc_while_side : side:[`Left | `Right] -> FApi.backward

(* Cond_L simplify direction: from goal whose [S_side] ends in a
   conditional sample [dcond d (fun v => e[v/x] = y)] (structurally
   and semantically matching [R_side]'s trailing sample and the body
   assignment), drop that trailing sample from [S_side]. *)
val t_dc_cond_l : FApi.backward

(* Cond_L intro direction: from goal with [S_side] matching [R_side]'s
   prefix (R minus the trailing sample), append
   [dcond d (fun v => e[v/x] = y)] as a new trailing sample of
   [S_side]. *)
val t_dc_cond_l_intro : FApi.backward

(* Dispatches Cond_L on chosen side (right uses symmetry internally). *)
val t_dc_cond_side : side:[`Left | `Right] -> FApi.backward

(* Dispatches Cond_L intro on chosen side. *)
val t_dc_cond_intro_side : side:[`Left | `Right] -> FApi.backward

(* Prod_L split: R_side ends in a product sample [(x,y) <$ (d1 `*` d2)];
   expand into [x <$ d1; y <$ d2].                                      *)
val t_dc_prod_split : side:[`Left | `Right] -> FApi.backward

(* Prod_L intro: R_side ends in two consecutive samples [x <$ d1; y <$ d2];
   combine into [(x, y) <$ (d1 `*` d2)]. Side condition: x not in Fv(d2). *)
val t_dc_prod_intro : side:[`Left | `Right] -> FApi.backward

(* Unfold an F-level dcoupl goal into an S-level one by inlining the two
   procedures' bodies. Mirrors [EcPhlFun.t_equivF_fun_def] for equiv. *)
val t_dc_fun_def : FApi.backward

(* Unroll_L / Unroll_R (paper §4.3): rewrite a body-only [while e do c]
   into [if e then (c; while e do c) else skip]. *)
val t_dc_unroll_side : side:[`Left | `Right] -> FApi.backward

(* Split_L / Split_R (paper §4.3): rewrite a body-only [while e do c]
   into [while e /\ e' do c; while e do c] given a user-supplied
   boolean expression [e']. *)
val t_dc_split_side :
     side:[`Left | `Right]
  -> EcTypes.expr
  -> FApi.backward
