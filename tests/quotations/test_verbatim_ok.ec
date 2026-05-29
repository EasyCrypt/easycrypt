require import Int.

(* 'verbatim' copies the body through unchanged (one verbatim segment).
   The body is a sentence FRAGMENT -- the terminating '.' is written by the
   user, after %}, not inside the quotation. *)
{% verbatim op answer : int = 42 %}.

lemma check : answer = 42 by [].
