(* -------------------------------------------------------------------- *)
open EcParsetree
open EcCoreGoal.FApi
open EcAst

(* ==================================================================== *)
(* Rules (trusted)                                                      *)

(* In both rules, [P1, Q1] relate the left program and the intermediate one,
   [P2, Q2] the intermediate program and the right one. All four relations
   are stated over the goal's memories [(&1, &2)] (the intermediate memory
   being [&2] in [P1, Q1] and [&1] in [P2, Q2]); written below with [&2] for
   the intermediate memory and [&3] for the right one. *)

type equivS_trans = {
  est_mt    : EcMemory.memtype;   (* memory type of the intermediate program *)
  est_stmt  : stmt;               (* intermediate program c2 *)
  est_pre1  : ts_inv;             (* P1 *)
  est_post1 : ts_inv;             (* Q1 *)
  est_pre2  : ts_inv;             (* P2 *)
  est_post2 : ts_inv;             (* Q2 *)
}

(* [t_equivS_trans { est_mt = mt; est_stmt = c2;
                     est_pre1 = P1; est_post1 = Q1;
                     est_pre2 = P2; est_post2 = Q2 }] — transitivity:

     forall &1 &3, P => exists (fv P1<2> u fv P2<2>), P1 /\ P2
     forall &1 &2 &3, Q1 => Q2 => Q
     equiv [c1 ~ c2 : P1 ==> Q1]
     equiv [c2 ~ c3 : P2 ==> Q2]
     ---------------------------------------------------------  &2 : mt
                 equiv [c1 ~ c3 : P ==> Q]

   where [fv P1<2> u fv P2<2>] are the program variables and globals of the
   intermediate memory read by [P1] and [P2]: the existential over the
   intermediate memory is stated as one over (only) them.

   Side condition: the four relations are over the goal's memories
   (otherwise fails).

   Node: [REquivSTrans] (the record above: typed intermediate program and
   relations). Checker: "equivS-trans"; it recomputes [fv P1<2>],
   [fv P2<2>] from the goal's context. *)
val t_equivS_trans : equivS_trans -> backward

type equivF_trans = {
  eft_f     : EcPath.xpath;       (* intermediate procedure f2 *)
  eft_pre1  : ts_inv;             (* P1 *)
  eft_post1 : ts_inv;             (* Q1 *)
  eft_pre2  : ts_inv;             (* P2 *)
  eft_post2 : ts_inv;             (* Q2 *)
}

(* [t_equivF_trans { eft_f = f2; eft_pre1 = P1; eft_post1 = Q1;
                                 eft_pre2 = P2; eft_post2 = Q2 }] — same for
   procedures:

     forall &1 &3, P => exists (fv P1<2> u fv P2<2>), P1 /\ P2
     forall &1 &2 &3, Q1 => Q2 => Q
     equiv [f1 ~ f2 : P1 ==> Q1]
     equiv [f2 ~ f3 : P2 ==> Q2]
     ---------------------------------------------------------
                 equiv [f1 ~ f3 : P ==> Q]

   the memories being those of the procedures' pre- (resp. post-)
   conditions, [&2] ranging over the memories of [f2].

   Side condition: as for [t_equivS_trans].

   Node: [REquivFTrans] (the record above). Checker: "equivF-trans"; it
   recomputes the variables of the intermediate memory and the procedures'
   memories from the goal's context. *)
val t_equivF_trans : equivF_trans -> backward

(* ==================================================================== *)
(* Derived tactics                                                      *)

(* [t_equivS_trans_eq side c'] — replaces the program [c] of [side] by [c'],
   on the goal [equiv [c ~ c3 : P ==> Q]] (for [`Left]; symmetrically for
   [`Right]). Expands to [t_equivS_trans] with [c2 := c'] and
     P1 := ={X} /\ P|1     Q1 := ={Y}     P2 := P     Q2 := Q
   where [X] are the variables (of the replaced side) read by [c], [P] or
   [Q], [Y] those read by [Q], and [P|1] the conjuncts of [P] that only
   mention the replaced side's memory, giving
     (a) forall &1 &3, P => exists ..., P1 /\ P2  — closed: the existential
         is instantiated with the replaced side's values, then [done];
     (b) forall &1 &2 &3, Q1 => Q2 => Q            — closed by [done];
     (c) equiv [c ~ c' : ={X} /\ P|1 ==> ={Y}]     — left open;
     (d) equiv [c' ~ c3 : P ==> Q]                 — left open.

   Visible goals: (c) and (d). Emits no node of its own. *)
val t_equivS_trans_eq : side -> EcModules.stmt -> backward

(* ==================================================================== *)
(* Elaboration                                                          *)

(* On an [equivS] goal:
   - [transitivity{i} {c2} (P1 ==> Q1) (P2 ==> Q2)]: applies
     [t_equivS_trans], [c2] being typed in the memory of side [i], [P1, Q1]
     with the intermediate program on the right, [P2, Q2] with it on the
     left;
   - [transitivity*{i} {c2}]: applies [t_equivS_trans_eq];
   - [replace{i} pat by {c2} ...] / [replace*{i} pat by {c2}]: the same,
     the sub-statements named in the pattern [pat] (matched against the
     current program of side [i]) being usable in [c2]. [c2] is the whole
     new program of side [i] (no position is involved: the rule is applied
     to the complete statements).
   Fails on the procedure forms ([transitivity f ...]). *)
val process_equivS_trans : trans_info -> backward

(* On an [equivF] goal: [transitivity f2 (P1 ==> Q1) (P2 ==> Q2)] applies
   [t_equivF_trans]. Fails on [transitivity* f2] and on the statement
   forms. *)
val process_equivF_trans : trans_info -> backward
