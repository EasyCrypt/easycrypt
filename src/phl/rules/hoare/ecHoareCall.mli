(* -------------------------------------------------------------------- *)
open EcParsetree
open EcCoreGoal
open EcCoreGoal.FApi
open EcAst
open EcEnv

(* ==================================================================== *)
(* Rules (trusted)                                                      *)

type hoare_call = {
  hcall_pre  : ss_inv;   (* precondition P of the procedure *)
  hcall_post : hs_inv;   (* postcondition Q | E_f of the procedure *)
}

(* [t_hoare_call { hcall_pre = P; hcall_post = Q | E_f }] — single call:

                    hoare [f : P ==> Q | E_f]
     ------------------------------------------------------------
     hoare [lv <@ f(a) : P[arg := a] /\ W /\ W_E ==> R | E]

     W   := forall result, forall (mod f),
              Q[res := result] => R[lv := result]
     W_E := forall (mod f), E_f => E   (exception per exception)

   where [mod f] are the variables written by [f], [E_f => E] are the
   conditions of [EcProofTyping.merge2_poe_list E E_f] (each exceptional
   postcondition of [E_f] implies the corresponding one of [E]), and
   [/\] is the asymmetric conjunction [&&], built with the simplifying
   constructors ([hoare_call_wp]). Side conditions: the statement is the
   single call [lv <@ f(a)], and the precondition is convertible to the
   one displayed (otherwise fails). Soundness: [P], [Q] and [E_f] are
   read in the memory of [f] in the premise and in the memory of the goal
   in the conclusion; they read no local variable other than [arg] /
   [res], as the typing of the specifications ensures.

   Node: [RHoareCall { hcall_pre = P; hcall_post = Q | E_f }].
   Checker: "hoare-call". *)
val t_hoare_call : hoare_call -> backward

(* [hoare_call_wp hyps m (P, Q | E_f) (lv, f, a) (R | E)] is the
   precondition of the conclusion of [t_hoare_call], in memory [m]. *)
val hoare_call_wp :
     LDecl.hyps
  -> memory
  -> form * exnpost
  -> lvalue option * EcPath.xpath * expr list
  -> exnpost
  -> form

(* ==================================================================== *)
(* Derived tactics                                                      *)

(* [t_hoare_call_last { hcall_pre = P; hcall_post = Q | E_f }] — on
   [hoare [c; lv <@ f(a) : P0 ==> R | E]], with [W0] the precondition of
   [t_hoare_call] for [R | E]:
   1. [EcHoareSeq.t_hoare_seq] before the call, with intermediate
      assertion [W0], giving
        (a) hoare [c : P0 ==> W0 | E]              — left open,
        (b) hoare [lv <@ f(a) : W0 ==> R | E];
   2. [t_hoare_call] on (b), giving
        (c) hoare [f : P ==> Q | E_f]              — left open.
   Visible goals: (c), then (a). Fails if the last instruction is not a
   call. Emits no node of its own. *)
val t_hoare_call_last : hoare_call -> backward

(* ==================================================================== *)
(* Elaboration                                                          *)

(* The cut of [call] on a [hoareS] goal, as [(spec, t)]: [spec] is the
   specification of the procedure [f] called last, [t] the tactic run on it
   once the cut is applied.
   - [call (_ : P ==> Q | E)] (no side): [P], [Q] and [E] typed in the
     memory of [f]; [spec] is [hoare [f : P ==> Q | E]], [t] the identity;
   - [call (: I)] (no side): [I] typed in an abstract memory (global
     variables only); [spec] is [hoare [f : I ==> I]], [t] is [proc I] (or
     [proc] for a concrete [f], see [EcPhlFun.t_fun]) followed by
     [trivial] on its first two goals;
   - [call (: bad, P, Q)]: fails (an equiv is expected). *)
val process_hoare_call_cut :
  oside -> call_info -> tcenv1 -> EcFol.form * backward
