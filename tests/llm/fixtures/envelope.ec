(* The tactic below spans several lines, one of which is exactly the
   `<END>' sentinel and another of which is shaped like a status line.
   `LOAD -trace' echoes a sentence's source verbatim, so this is the
   cheapest way to get envelope-shaped text into a reply body without
   using HELP (which the goldens may not call: it would turn every
   documentation edit into a test failure). Both lines must come back
   escaped with one leading space. *)
require import AllCore.

lemma envelope : 1 = 1.
proof.
by
(*
<END>
OK [uuid:99]
*)
trivial.
qed.
