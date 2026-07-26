(* -------------------------------------------------------------------- *)
(* Machine-profile JSON builders for the LLM REPL ([EcLlm]). Ported
   from the daemon-v1 line; see doc/ecllm-compat.md Appendix B and the
   UPSTREAM.md additions referenced per function. All payloads are
   JSON-encoded strings ready for the wire. *)

(* GOALS-JSON (additions 3 + 20 + 23 + 24): structured proof state of
   the currently active proof, or {"active":false}. *)
val goals_to_json : unit -> string

(* PARSE-JSON (additions 1 + 16): sentence-granular parse of a source
   buffer — classes, kinds, positions, first-token offsets, verbatim
   slices. *)
val parse_to_json : string -> string

(* ANALYZE-JSON (addition 14): stateless batch diagnostics of a source
   buffer against a fresh scope, with textual scope-tagging and
   synthetic-abort recovery on failing proof closers. *)
val analyze_to_json :
  checkmode:EcCommands.checkmode -> string -> string

(* The `ERROR-JSON:` reply line (addition 8). [exn] is classified
   (TypeError / ParseError / TacticFailure / Internal, with location);
   without it, a protocol-level Internal payload built from
   [fallback]. *)
val error_json_line : ?exn:exn -> fallback:string -> unit -> string
