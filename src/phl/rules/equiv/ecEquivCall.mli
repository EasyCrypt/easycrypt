(* -------------------------------------------------------------------- *)
open EcParsetree
open EcCoreGoal
open EcCoreGoal.FApi
open EcAst
open EcEnv

(* ==================================================================== *)
(* Rules (trusted)                                                      *)

type equiv_call = {
  ecall_pre  : ts_inv;   (* precondition P of the procedures *)
  ecall_post : ts_inv;   (* postcondition Q of the procedures *)
}

(* [t_equiv_call { ecall_pre = P; ecall_post = Q }] — two-sided call:

                      equiv [fL ~ fR : P ==> Q]
     ------------------------------------------------------------------
     equiv [lvL <@ fL(aL) ~ lvR <@ fR(aR) : P[arg<1> := aL, arg<2> := aR] /\ W ==> R]

     W := forall resultL resultR, forall (mod fL)<1> (mod fR)<2>,
            Q[res<1> := resultL, res<2> := resultR] =>
            R[lvL<1> := resultL, lvR<2> := resultR]

   where [mod f] are the variables written by [f], and [/\] is the
   asymmetric conjunction [&&], built with the simplifying constructors
   ([equiv_call_wp]). Side conditions: both statements are single calls,
   and the precondition is convertible to the one displayed (otherwise
   fails). Soundness: [P] and [Q] read no local variable other than [arg]
   / [res], as the typing of the specifications ensures (they are read in
   the memories of [fL] / [fR] in the premise, of the goal in the
   conclusion).

   Node: [REquivCall { ecall_pre = P; ecall_post = Q }].
   Checker: "equiv-call". *)
val t_equiv_call : equiv_call -> backward

(* [equiv_call_wp hyps (ml, mr) (P, Q) ?mods callL callR R] is the
   precondition of the conclusion of [t_equiv_call] (with [mods]
   generalized too, on each side, in [W]). *)
val equiv_call_wp :
     LDecl.hyps
  -> memory * memory
  -> form * form
  -> ?mods:(EcPV.PV.t * EcPV.PV.t)
  -> lvalue option * EcPath.xpath * expr list
  -> lvalue option * EcPath.xpath * expr list
  -> form
  -> form

type equiv_call_onesided = {
  ecallos_side : side;     (* side of the call *)
  ecallos_pre  : ss_inv;   (* precondition P of the procedure *)
  ecallos_post : ss_inv;   (* postcondition Q of the procedure *)
}

(* [t_equiv_call_onesided { ecallos_side = `Left; ecallos_pre = P;
                            ecallos_post = Q }] — one-sided call:

                     phoare [f : P ==> Q] = 1%r
     -------------------------------------------------------------
     equiv [lv <@ f(a) ~ skip : P<1>[arg<1> := a] /\ W ==> R]

     W := forall result, forall (mod f)<1>,
            Q<1>[res<1> := result] => R[lv<1> := result]

   (symmetrically for [`Right]; [/\] is [&&], built with the simplifying
   constructors, [equiv_call_onesided_wp]). Side conditions: that side is
   a single call, the other one is empty, and the precondition is
   convertible to the one displayed (otherwise fails). Soundness: as for
   [t_equiv_call], [P] and [Q] read no local variable other than [arg] /
   [res].

   Node: [REquivCallOneSided { ecallos_side; ecallos_pre = P;
                               ecallos_post = Q }].
   Checker: "equiv-call-onesided". *)
val t_equiv_call_onesided : equiv_call_onesided -> backward

(* [equiv_call_onesided_wp hyps side (ml, mr) (P, Q) call R] is the
   precondition of the conclusion of [t_equiv_call_onesided]. *)
val equiv_call_onesided_wp :
     LDecl.hyps
  -> side
  -> memory * memory
  -> form * form
  -> lvalue option * EcPath.xpath * expr list
  -> form
  -> form

(* ==================================================================== *)
(* Derived tactics                                                      *)

(* [t_equiv_call_last { ecall_pre = P; ecall_post = Q }] — on
   [equiv [c; lvL <@ fL(aL) ~ c'; lvR <@ fR(aR) : P0 ==> R]], with [W0]
   the precondition of [t_equiv_call] for [R]:
   1. [EcEquivSeq.t_equiv_seq] before both calls, with intermediate
      relation [W0], giving
        (a) equiv [c ~ c' : P0 ==> W0]                           — left open,
        (b) equiv [lvL <@ fL(aL) ~ lvR <@ fR(aR) : W0 ==> R];
   2. [t_equiv_call] on (b), giving
        (c) equiv [fL ~ fR : P ==> Q]                            — left open.
   Visible goals: (c), then (a). Fails if a last instruction is not a
   call. Emits no node of its own. *)
val t_equiv_call_last : equiv_call -> backward

(* [t_equiv_call_onesided_last { ecallos_side = `Left; ecallos_pre = P;
                                 ecallos_post = Q }] — on
   [equiv [c; lv <@ f(a) ~ c' : P0 ==> R]] (symmetrically for [`Right]),
   with [W0] the precondition of [t_equiv_call_onesided] for [R]:
   1. [EcEquivSeq.t_equiv_seq] before the call on that side and at the end
      of the other one, with intermediate relation [W0], giving
        (a) equiv [c ~ c' : P0 ==> W0]                           — left open,
        (b) equiv [lv <@ f(a) ~ skip : W0 ==> R];
   2. [t_equiv_call_onesided] on (b), giving
        (c) phoare [f : P ==> Q] = 1%r                           — left open.
   Visible goals: (c), then (a). Fails if the last instruction on that side
   is not a call. Emits no node of its own. *)
val t_equiv_call_onesided_last : equiv_call_onesided -> backward

(* ==================================================================== *)
(* Elaboration                                                          *)

(* The cut of [call] on an [equivS] goal, as [(spec, t)]: [spec] is the
   specification of the procedure(s) called last, [t] the tactic run on it
   once the cut is applied.
   - [call (_ : P ==> Q)]: [P] and [Q] typed in the memories of [fL] and
     [fR]; [spec] is [equiv [fL ~ fR : P ==> Q]], [t] the identity;
   - [call{i} (_ : P ==> Q)]: [P] and [Q] typed in the memory of the
     procedure called last on side [i]; [spec] is
     [phoare [f : P ==> Q] = 1%r], [t] the identity;
   - [call (: I)] (no side): [I] typed in abstract memories (global
     variables only); [spec] is
     [equiv [fL ~ fR : ={arg} /\ I ==> ={res} /\ I]] (with [={glob A}] in
     both for procedures of an abstract [A]; for concrete procedures, the
     types of their arguments and results must coincide), [t] is [proc I]
     (or [proc] for concrete procedures, see [EcPhlFun.t_fun]) followed
     by [trivial] on its first two goals;
   - [call (: bad, P, Q)] (no side; abstract procedures): [spec] is
     [equiv [fL ~ fR : bad<2> ? Q : ={arg, glob A} /\ P ==>
                       bad<2> ? Q : ={res, glob A} /\ P]], [t] is the
     abstract upto rule ([EcPhlFun.t_equivF_abs_upto]) followed by
     [assumption] or [trivial] on its first three goals. *)
val process_equiv_call_cut :
  oside -> call_info -> tcenv1 -> EcFol.form * backward
