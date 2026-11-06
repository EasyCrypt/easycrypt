(* -------------------------------------------------------------------- *)
open EcSymbols
open EcAst
open EcCoreGoal.FApi

(* ==================================================================== *)
(* Rules (trusted)                                                      *)

type hoare_extens_rule = {
  her_var : symbol;      (* the enumerated program variable, by name *)
}

type hoare_extens_node = {
  hen_var : variable;    (* the enumerated program variable, resolved in
                            the memory of the goal *)
}

(* [t_hoare_extens { her_var = x }] — enumeration of the values of a
   program variable ([extens [x]] on a hoare goal):

       hoare [c_0 : P_0 ==> Q_0]  ...  hoare [c_(2^k-1) : P_(2^k-1) ==> Q_(2^k-1)]
     ------------------------------------------------------------------------------
                               hoare [c : P ==> Q | E]

   where [x] is a local program variable of the memory [m] of the goal,
   of a type bound to a bitstring of size [k] with operator [of_int], and,
   for each [i], with [w_i = of_int i]: [P_i = P[x{m} := w_i]],
   [Q_i = Q[x{m} := w_i]], and [c_i] is [c] in which [x] is replaced by
   [w_i] in the right-hand side of every assignment (normalized), the
   left-hand sides being kept. Side conditions (otherwise fails): [E] is
   empty ("exceptions not supported"); [x] is a variable of [m] ("Failed
   to find var x in memory m"); its type is bound to a bitstring ("Failed
   to get size for type ...", "Failed to destructure var type", "No
   bindings found for type of var", "Only finite size bitstring
   supported"); [c] does not write [x] ("extens: the program writes the
   variable x": [Q] reads [x] in the final memory); [c] only contains
   assignments (raises [EcCoreFol.CannotTranslate]). The premises have
   no exceptional postcondition.

   Node: [RHoareExtens { hen_var = x (resolved) }] ([k] and [of_int] are
   read from the binding of its type). Checker: "hoare-extens". *)
val t_hoare_extens : hoare_extens_rule -> backward

(* ==================================================================== *)
(* Derived tactics                                                      *)

(* [EcPhlBDep.t_extens (Some x) tt] — [extens [x] : tt]: [t_hoare_extens
   { her_var = x }], then [tt] on each premise, in order, which must close
   it (otherwise fails with the error of [tt], or with "Failed to close
   goal: ..." and the first goal [tt] leaves). No visible goal. Emits no
   node of its own: the proofs of the premises are kept (and rechecked). *)
