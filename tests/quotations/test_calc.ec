require import Int.

(* The 'calc' quotation expands to a sentence FRAGMENT (the literal 42).
   The surrounding 'op forty_two = ... .' -- including the terminating '.' --
   is written here, not by the handler.  This shows a quotation used in the
   middle of a sentence. *)
op forty_two = {% calc 6 * 7 %}.

lemma check : forty_two = 42 by [].
