require import Int.

(* The 'calc' and 'verbatim' handlers are bound in this directory's
   easycrypt.project (quote = name:path), not via the environment or a
   handlers/ subdirectory.  This checks that project-file bindings work. *)
op forty_two = {% calc 6 * 7 %}.

{% verbatim op answer : int = 42 %}.

lemma check : forty_two = answer by [].
