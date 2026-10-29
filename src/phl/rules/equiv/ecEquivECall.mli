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

(* In both forms, [(pt, C)] is the contract, a proof term [pt] of the
   specification [C] of the called procedure(s), whose arguments may
   mention program variables [vs] of the goal's memories, abstracted by
   the caller ([EcPlECall.abstract_pvs]) as fresh locals [ids]; [pt] and
   [C] are already stated over [ids] ([X(vs)] below is [X] with [ids]
   replaced by [vs]). "Abstracting [vs]" is, on
   [equiv [_ ~ _ : P ==> _]]: [EcEquivExists.t_equiv_exists_intro vs],
   [EcEquivExists.t_equivS_exists_elim], and the introduction of [ids].
   Neither form emits a node of its own. *)

(* [t_equiv_ecall_onesided side (pt, C) (ids, vs) call] ([ecall{1}],
   [side = `Left]; symmetrically for [`Right]) — on
   [equiv [c; lv <@ f(a) ~ c' : P ==> Q]], with
   [C = phoare [f : Pf ==> Qf] = 1%r]:
   1. [EcEquivSeq.t_equiv_seq] before the call and at the end of [c'],
      with intermediate relation [W(vs)], [W] the weakest precondition of
      the one-sided call for [C] ([EcEquivCall.equiv_call_onesided_wp]);
      giving
        (a) equiv [c ~ c' : P ==> W(vs)]                    — left open,
        (b) equiv [lv <@ f(a) ~ skip : W(vs) ==> Q];
   2. on (b): abstracting [vs], then
      [EcEquivCall.t_equiv_call_onesided_last] with [C]: its
      specification premise is closed by [pt], the premise on the empty
      prefixes by [EcPhlAuto.t_auto] (left open if it does not).
   Fails at 2. when [C] is a [hoare] specification (the one-sided call
   rule takes a phoare one), as [call{1}] does. Visible goals: (a), and
   the premise of 2. if not closed. *)
val t_equiv_ecall_onesided :
     side
  -> proofterm * form
  -> (EcIdent.t * ty) list * form list
  -> EcPlECall.call
  -> backward

(* [t_equiv_ecall (pt, C) (ids, vs) (callL, callR)] ([ecall]) — on
   [equiv [c; lvL <@ fL(aL) ~ c'; lvR <@ fR(aR) : P ==> Q]], with
   [C = equiv [fL ~ fR : Pf ==> Qf]]:
   1. [EcEquivSeq.t_equiv_seq] before both calls, with intermediate
      relation [W(vs)], [W] the weakest precondition of the calls for [C]
      ([EcEquivCall.equiv_call_wp]); giving
        (a) equiv [c ~ c' : P ==> W(vs)]                    — left open,
        (b) equiv [lvL <@ fL(aL) ~ lvR <@ fR(aR) : W(vs) ==> Q];
   2. on (b): abstracting [vs], then [EcEquivCall.t_equiv_call_last]
      with [C]: its specification premise is closed by [pt], the premise
      on the empty prefixes by [EcPhlAuto.t_auto] (left open if it does
      not).
   Visible goals: (a), and the premise of 2. if not closed. *)
val t_equiv_ecall :
     proofterm * form
  -> (EcIdent.t * ty) list * form list
  -> EcPlECall.call * EcPlECall.call
  -> backward

(* ==================================================================== *)
(* Elaboration                                                          *)

(* [ecall (c args)] / [ecall{i} (c args)] on an [equivS] goal: no
   [->>]; the contract typed with the goal's memories, applied to as many
   holes as possible, its program variables abstracted
   ([EcPlECall.abstract_pvs]); it must be an [equiv] specification of the
   procedures called last ([hoare] or [phoare] for the procedure called
   last on side [i]; [EcPlECall.check_contract_type]). Applies
   [t_equiv_ecall] / [t_equiv_ecall_onesided]. *)
val process_equiv_ecall : pdirection -> oside -> pecall -> backward
