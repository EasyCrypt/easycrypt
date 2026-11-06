(* -------------------------------------------------------------------- *)
open EcCoreGoal.FApi

(* ==================================================================== *)
(* Rules (trusted)                                                      *)

(* [t_fol_extens] — enumeration of a bounded quantification over the
   integers ([extens] on a formula):

       Γ ⊢ p s    Γ ⊢ p (s+1)    ...    Γ ⊢ p (s+n-1)
     -------------------------------------------------  s, n integer
                 Γ ⊢ all p (iota_ s n)                    literals

   [p (s+i)] being [p] applied to the literal [s+i], head-reduced
   ([EcTypesafeFol.f_app]). Side conditions (otherwise fails): the goal
   is [all p l], [p] a predicate on [int] ("Wrong goal shape"), [l] is
   [iota_ s n] ("Unsupported List pattern"), [s] and [n] are integer
   literals ("Iota start should be constant", "Iota length should be
   constant").

   Node: [RFolExtens]. Checker: "fol-extens". *)
val t_fol_extens : backward

(* ==================================================================== *)
(* Derived tactics                                                      *)

(* [EcPhlBDep.t_extens None tt] — [extens : tt]: [t_fol_extens], then
   [tt] on each premise, in order, which must close it (otherwise fails
   with the error of [tt], or with "Failed to close goal: ..." and the
   first goal [tt] leaves). No visible goal. Emits no node of its own:
   the proofs of the premises are kept (and rechecked). *)
