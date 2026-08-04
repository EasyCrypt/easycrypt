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

(* LOAD-failure ERROR-JSON (field report B15): the generic
   per-exception payload plus the loader's own knowledge — the
   failing sentence's top-file parser location (used when the
   exception carries none) and a "load" object with how much of the
   top file remains loaded (complete sentences / last line), so
   clients can keep the stopped session and resume at the boundary. *)
val load_error_json :
  exn:exn ->
  fail_loc:EcLocation.t option ->
  loaded_sentences:int ->
  loaded_line:int ->
  unit -> string

(* Protocol-level ERROR-JSON with an explicit code (EXEC-JSON's
   MalformedExecJson / UnsupportedExecJson). *)
val protocol_error_json : code:string -> detail:string -> string
