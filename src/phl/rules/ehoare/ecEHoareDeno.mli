(* -------------------------------------------------------------------- *)
open EcParsetree
open EcCoreGoal.FApi
open EcAst

(* ==================================================================== *)
(* Rules (trusted)                                                      *)

type ehoare_deno = {
  ehd_pre  : ss_inv;    (* P, in the memory &m of the judgement *)
  ehd_post : ss_inv;    (* Q, in the same memory *)
}

(* [t_ehoare_deno { ehd_pre = P; ehd_post = Q }] — a probability bounded
   by an expectation judgement on the procedure:

     ehoare [f : P ==> Q]
     P[&m := &n, arg := args] <= d%xr
     forall &m, E%xr <= Q
     0%r <= d
     ---------------------------------
     Pr[f(args) @ &n : E] <= d

   where, in the third premise, [&m] is the final memory of [f] and [E]
   is read in it. Side conditions: the goal has the shape above; [P] and
   [Q] are in the same memory [&m], which does not occur free in the goal
   (otherwise fails).

   Node: [REHoareDeno { ehd_pre = P; ehd_post = Q }].
   Checker: "ehoare-deno". *)
val t_ehoare_deno : ehoare_deno -> backward

(* ==================================================================== *)
(* Elaboration                                                          *)

(* [byehoare pt] (resp. [byehoare (_ : P ==> Q)]) on
   [Pr[f(args) @ &n : E] <= d]: the judgement [ehoare [f : P ==> Q]] is
   the type of the proof term [pt] (resp. is cut, [P] and [Q] typed as
   [xreal] in the memory of the event, [d%xr] and [E%xr] by default).
   Applies [t_ehoare_deno], closes its first premise with [pt] (resp.
   leaves it as the first goal) and tries [EcLowGoal.t_trivial] on its
   last premise [0%r <= d] (left visible when not closed). *)
val process_ehoare_deno : deno_ppterm -> backward
