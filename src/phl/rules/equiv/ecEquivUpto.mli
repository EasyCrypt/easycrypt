(* -------------------------------------------------------------------- *)
open EcCoreGoal.FApi

(* ==================================================================== *)
(* Rules (trusted)                                                      *)

(* [t_equiv_upto] — two procedures equal up to [bad] give the same
   probability to every event that excludes [bad]:

     --------------------------------------------------  f1 =upto bad= f2
     Pr[f1(a1) @ &m : E] = Pr[f2(a2) @ &m : E]

   Side conditions (checked in this order, otherwise fails):
   - the initial memories are the same, and [a1] and [a2] are convertible
     (full reduction);
   - the two events are alpha-equivalent, of the form [E' /\ !bad] or
     [!bad], [bad] a global variable read in the final memory;
   - [f1 =upto bad= f2], a syntactic check on the procedures (after
     normalization of their paths):
     * defined procedures: same parameters and local declarations (names
       and types, in order), same returned expression, and bodies
       either equal up to bad, or made of a common prefix (equal
       instructions, [bad] unconstrained) followed by [bad <- false] on
       both sides, the rest being equal up to bad;
     * two statements are equal up to bad when they are the same until
       both execute [bad <- true] at the same point, their instructions
       not assigning [bad] before, nested statements and called
       procedures being themselves equal up to bad; after that point,
       they are arbitrary, provided that they (and the procedures they
       call) assign [bad] nothing but [true];
     * abstract procedures: the same procedure of the same functor,
       [bad] not in its footprint, its oracles equal up to bad;
     * [raise] is not supported (fails).

   Node: [REquivUpto]. Checker: "equiv-upto". *)
val t_equiv_upto : backward

(* ==================================================================== *)
(* Elaboration                                                          *)

(* [byupto], on a statement on probabilities. The forms other than the
   first apply a lemma of the real theory ([eq_upto], [upto_le],
   [upto_abs], [upto_maxr]), whose instance of the rule is closed by
   [t_equiv_upto], and whose facts on probabilities are closed by
   [rewrite Pr mu_split bad] (resp. [mu_sub], [mu_ge0]) then [trivial]
   (what [trivial] leaves remains visible). Here [E'] is [E /\ !bad].
   - [Pr[f1 : E'] = Pr[f2 : E']]: [t_equiv_upto];
   - [Pr[f1 : E] - Pr[f2 : E] = Pr[f1 : E /\ bad] - Pr[f2 : E /\ bad]]:
     [eq_upto], splitting both probabilities on [bad];
   - [Pr[f1 : E] <= Pr[f2 : F] + Pr[f1 : G]], [G] being [bad] or
     [_ /\ bad]: [upto_le], splitting the first probability on [bad],
     and the inclusions [Pr[f1 : E /\ bad] <= Pr[f1 : G]] and
     [Pr[f2 : E'] <= Pr[f2 : F]];
   - [`|Pr[f1 : E] - Pr[f2 : E]| <= `|Pr[f1 : E /\ bad] - Pr[f2 : E /\ bad]|]:
     [upto_abs], splitting both probabilities on [bad];
   - [`|Pr[f1 : E] - Pr[f2 : E]| <= maxr Pr[f1 : G1] Pr[f2 : G2]], [G1]
     being [bad] or [_ /\ bad]: [upto_maxr], splitting both probabilities
     on [bad], with the positivity of [Pr[fi : E /\ bad]] and the
     inclusions [Pr[fi : E /\ bad] <= Pr[fi : Gi]].
   Fails on any other statement. *)
val process_upto : backward
