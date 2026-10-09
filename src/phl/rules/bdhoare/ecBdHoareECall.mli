(* -------------------------------------------------------------------- *)
open EcParsetree
open EcCoreGoal
open EcCoreGoal.FApi
open EcAst

(* ==================================================================== *)
(* Rules (trusted)                                                      *)

(* None: [ecall] is derived from the [seq], [call], [exists] and
   consequence rules. *)

(* ==================================================================== *)
(* Derived tactics                                                      *)

(* [t_bdhoare_ecall_bwd (pt, C)] ([ecall]) — on
   [phoare [c; lv <@ f(a) : P ==> Q] = 1%r], [(pt, C)] being the
   contract: a proof term [pt] of [C = phoare [f : Pf ==> Qf] = 1%r],
   whose arguments may mention program variables [vs] of the goal's
   memory, abstracted as in [EcHoareECall] (fresh locals [ids], [X(ids)]
   for [X] with [vs] replaced by [ids]):
   1. [EcBdHoareSeq.t_bdhoare_seq_full] before the call, with
      [phi := W(vs)] ([W(ids)] being the weakest precondition of the call
      for [C(ids)], as for hoare), [R := true], [f1 = f2 := 1%r],
      [g1 = g2 := 0%r];
      its premises are, in order:
        (H)  hoare [c : P ==> W(vs)],
        (F1) phoare [c : P ==> true] = 1%r,
        (F2) phoare [lv <@ f(a) : W(vs) /\ true ==> Q] = 1%r,
        (G1) phoare [c : P ==> !true] = 0%r,
        (B)  the bound condition,
        (N)  the non-modification condition, when not closed;
   2. (H) is lifted (currently by
      [EcPhlConseq.t_hoareS_conseq_bdhoare]) to
      [phoare [c : P ==> W(vs)] = 1%r] — left open, so that further
      [ecall]s on it apply;
   3. (F2): the program variables [vs] are abstracted with
      [EcBdHoareExists.t_bdhoare_exists_intro] and
      [EcBdHoareExists.t_bdhoareS_exists_elim], then
      [EcBdHoareCall.t_bdhoare_call] with [C(ids)] (on an empty prefix):
      its specification premise is closed by [pt(ids)], its other
      premise by [EcPhlAuto.t_auto] (left open if it does not);
   4. the other premises by [EcPhlAuto.t_auto] (left open if it does
      not).
   Side conditions: the goal and the contract are [= 1%r] (otherwise
   fails, before acting). Visible goals: the lifted (H), then what 3.
   and 4. leave open. Emits no node of its own. The call rule keeps its
   composite statement ([EcBdHoareCall]): here on an empty prefix. *)
val t_bdhoare_ecall_bwd : proofterm * form -> backward

(* ==================================================================== *)
(* Elaboration                                                          *)

(* [ecall (c args)] on a [bdHoareS] goal: no side, no [->>]; the
   contract typed with the goal's memory, applied to as many holes as
   possible; it must be a specification of the procedure called last
   ([EcPlECall.check_contract_type], [hoare] or [phoare]). Applies
   [t_bdhoare_ecall_bwd]. *)
val process_bdhoare_ecall : pdirection -> oside -> pecall -> backward
