(* Regression for `proof * [-tag]` failing to force untagged axioms.

   An exclusion-only bracket list (`proof * [-foo]`) means "force every axiom
   except those tagged `foo`", so the untagged axiom `A` must be FORCED into a
   proof obligation. `A` is unprovable, so the discharging tactic fails and
   the whole `clone` command must fail. Before the fix the untagged axiom was
   silently kept as an assumed axiom in the clone, so this clone was accepted
   (and `U.A` could be used to prove `false`). *)
require import AllCore.

theory T.
  axiom A : false.
end T.

fail clone T as U proof * [-foo] by done.

(* An include list (`proof * [foo]`) forces ONLY the axioms tagged `foo`:
   the untagged `A` is intentionally not forced and stays an axiom. *)
clone T as V proof * [foo] by done.
