(* Not UTF-8: the comment below is Latin-1, and it sits *inside* the
   traced sentence, so `LOAD -trace' echoes its bytes back verbatim.
   The MCP front-end must repair them before they reach a JSON string;
   the REPL, whose frame is bytes, passes them through. Keep this file
   in Latin-1 -- re-encoding it to UTF-8 makes the test vacuous. *)
require import AllCore.

lemma latin1 : 1 = 1.
proof.
by
(* découpe en régions *)
trivial.
qed.
