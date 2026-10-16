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

(* In both forms, [(pt, C)] is the contract: a proof term [pt] of
   [C = hoare [f : Pf ==> Qf]], the specification of the called procedure
   [f], whose arguments may mention program variables [vs] of the goal's
   memory. These are abstracted: [ids] are fresh locals for [vs], and
   [X(ids)] is [X] with [vs] replaced by [ids]. "Abstracting [vs]" below
   is, on a judgement [J [_ : P ==> _]]:
     - [EcHoareExists.t_hoare_exists_intro vs], to
       [J [_ : exists xs, xs = vs /\ P ==> _]],
     - [EcHoareExists.t_hoareS_exists_elim], to
       [forall xs, J [_ : xs = vs /\ P ==> _]],
     - and the introduction of [xs] as [ids].
   Neither form emits a node of its own. *)

(* [t_hoare_ecall_fwd (pt, C)] ([ecall ->>]) — on
   [hoare [lv <@ f(a); s : P ==> Q]], [C] with no exceptional
   postcondition:
   1. abstracting [vs], giving [hoare [lv <@ f(a); s : P1 ==> Q]],
      [P1 := ids = vs /\ P];
   2. [EcHoareSeq.t_hoare_seq] after the call, with intermediate
      assertion [S /\ F], where [S] is [Qf(ids)] with [res] replaced by
      [lv] (with its conjuncts mentioning [res] dropped when there is no
      [lv]), and [F] the conjunction of the top-level conjuncts of [P]
      that do not read the variables written by the call (the
      precondition is framed); giving
        (a) hoare [lv <@ f(a) : P1 ==> S /\ F],
        (b) hoare [s : S /\ F ==> Q];
   3. on (a): [EcHoareSplit.t_hoare_split], then
      [EcPhlConseq.t_conseqauto] (the frame rule
      [EcHoareFrame.t_hoareS_frame], its condition closed automatically)
      and [EcHoareTrue.t_hoare_true] close
      [hoare [lv <@ f(a) : P1 ==> F]];
   4. [EcHoareCall.t_hoare_call_last] with [C(ids)] on
      [hoare [lv <@ f(a) : P1 ==> S]], whose specification premise is
      closed by [pt(ids)], and the premise [hoare [skip : P1 ==> W]] (W
      the weakest precondition of the call) is reduced by
      [EcHoareSkip.t_hoare_skip] to
        (c) forall &m, P1 => W;
   5. [ids] generalized back in (c) and (b).
   Visible goals: [forall ids, (c)], then [forall ids, (b)]. *)
val t_hoare_ecall_fwd : proofterm * form -> backward

(* [t_hoare_ecall_bwd (pt, C)] ([ecall]) — on
   [hoare [c; lv <@ f(a) : P ==> Q | E]]:
   1. [EcHoareSeq.t_hoare_seq] before the call, with intermediate
      assertion [W(vs)], [W(ids)] being the weakest precondition of the
      call for [C(ids)] ([EcHoareCall.hoare_call_wp]); giving
        (a) hoare [c : P ==> W(vs) | E]                     — left open,
        (b) hoare [lv <@ f(a) : W(vs) ==> Q | E];
   2. on (b): abstracting [vs], then [EcHoareCall.t_hoare_call_last]
      with [C(ids)]: its specification premise is closed by [pt(ids)],
      the premise [hoare [skip : ids = vs /\ W(vs) ==> W(ids)]] by
      [EcPhlAuto.t_auto] (left open if it does not).
   Visible goals: (a), and the premise of 2. if not closed. *)
val t_hoare_ecall_bwd : proofterm * form -> backward

(* ==================================================================== *)
(* Elaboration                                                          *)

(* [ecall ->> (c args)] / [ecall (c args)] on a [hoareS] goal: no side;
   the contract typed with the goal's memory, applied to as many holes as
   possible; it must be a [hoare] specification of the procedure called
   first ([->>]) / last, with no exceptional postcondition for [->>]
   ([EcPlECall.check_contract_type]). Applies [t_hoare_ecall_fwd] /
   [t_hoare_ecall_bwd]. *)
val process_hoare_ecall : pdirection -> oside -> pecall -> backward
