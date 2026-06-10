require import Int.

(* Two quotations appearing inline within a single sentence, each replacing
   only part of it.  The handler returns bare literals; everything else --
   operators, parentheses, the terminating '.' -- is ordinary EC source. *)
op mixed = {% calc 6 * 7 %} + ({% calc 2 + 3 %} * 10).

lemma check : mixed = 92 by [].
