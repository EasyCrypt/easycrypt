(* -------------------------------------------------------------------- *)
open EcParsetree
open EcCoreGoal.FApi
open EcAst

(* ==================================================================== *)
(* Rules (trusted)                                                      *)

type bdhoare_deno = {
  bdd_pre  : ss_inv;    (* P, in the memory &m of the judgement *)
  bdd_post : ss_inv;    (* Q, in the same memory *)
}

(* [t_bdhoare_deno { bdd_pre = P; bdd_post = Q }] — a probability bounded
   by a probabilistic judgement on the procedure, with [~] the goal's
   comparison:

     phoare [f : P ==> Q] ~ d
     P[&m := &n, arg := args]
     forall &m', E [=>] Q
     ------------------------------------------
     Pr[f(args) @ &n : E] [~] d

   where [Pr [~] d] is [Pr <= d] for [<=], [Pr = d] for [=] and
   [d <= Pr] for [>=]; in the third premise, [&m'] is the final memory of
   the event [E], [Q] is read in it, and [E [=>] Q] is [E => Q] for [<=],
   [Q => E] for [>=] and [E <=> Q] for [=]. Side conditions: the goal has
   one of the three shapes above; [P] and [Q] are in the same memory
   [&m], which does not occur free in the goal (otherwise fails).

   Node: [RBdHoareDeno { bdd_pre = P; bdd_post = Q }].
   Checker: "bdhoare-deno". *)
val t_bdhoare_deno : bdhoare_deno -> backward

(* ==================================================================== *)
(* Derived tactics                                                      *)

(* [t_bdhoare_deno_full r] — on [d = Pr[...]], [d] not a probability:
   first [EcLowGoal.t_symmetry], to [Pr[...] = d]; then [t_bdhoare_deno r].
   On any other goal, [t_bdhoare_deno r]. Visible goals: the premises of
   [t_bdhoare_deno]. Emits no node of its own. *)
val t_bdhoare_deno_full : bdhoare_deno -> backward

(* ==================================================================== *)
(* Elaboration                                                          *)

(* [byphoare pt] (resp. [byphoare (_ : P ==> Q)]) on [Pr[f(args) @ &n : E]
   ~ d] or [d ~ Pr[...]], [~] among [<=], [=]: the judgement
   [phoare [f : P ==> Q] ~ d] is the type of the proof term [pt] (resp.
   is cut, [P] and [Q] typed in the memory of the event, [true] and [E]
   by default). Applies [t_bdhoare_deno_full], and closes its first
   premise with [pt] (resp. leaves it as the first goal). *)
val process_bdhoare_deno : deno_ppterm -> backward
