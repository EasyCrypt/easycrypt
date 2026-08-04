type t =
  | Parse_error of { detail : string }
  | Type_error of { detail : string }
  | Tactic_failure of { detail : string }
  | Smt_timeout of { budget_ms : int }
  | Smt_counter_example of { detail : string }
  | Budget_exceeded of { kind : [ `Deadline | `Tokens ] }
  | Cancelled of { reason : string }
  | Stale_cas of { server_cas : string }
  | Unknown_sentence_id of { id : string }
  | Overlay_conflict of { names : string list }
  | Session_restarted of { reason : string }
  | Load_stopped of {
      (* A document LOAD stopped at a failing sentence (field report
         B15). [file]/[line]/[col] is the error's reported position —
         [file] may be a require'd file, not the loaded one.
         [loaded_sentences]/[loaded_line] say how much of the TOP
         file remains loaded (complete top-level sentences / last
         loaded line): the session state IS that prefix, so callers
         may keep the session and resume at the boundary. *)
      file : string;
      line : int;
      col : int;
      loaded_sentences : int;
      loaded_line : int;
      detail : string;
    }
  | Pool_exhausted of { kind : [ `Lsp | `Mcp | `Spec ] }
  | Protocol_mismatch of { detail : string }
  | Internal of { detail : string }

let code = function
  | Parse_error _ -> "parse_error"
  | Type_error _ -> "type_error"
  | Tactic_failure _ -> "tactic_failure"
  | Smt_timeout _ -> "smt_timeout"
  | Smt_counter_example _ -> "smt_counter_example"
  | Budget_exceeded _ -> "budget_exceeded"
  | Cancelled _ -> "cancelled"
  | Stale_cas _ -> "stale_cas"
  | Unknown_sentence_id _ -> "unknown_sentence_id"
  | Overlay_conflict _ -> "overlay_conflict"
  | Session_restarted _ -> "session_restarted"
  | Load_stopped _ -> "load_stopped"
  | Pool_exhausted _ -> "pool_exhausted"
  | Protocol_mismatch _ -> "protocol_mismatch"
  | Internal _ -> "internal"

let to_string = function
  | Parse_error { detail } -> Printf.sprintf "parse error: %s" detail
  | Type_error { detail } -> Printf.sprintf "type error: %s" detail
  | Tactic_failure { detail } -> Printf.sprintf "tactic failure: %s" detail
  | Smt_timeout { budget_ms } ->
      Printf.sprintf "SMT timeout after %dms" budget_ms
  | Smt_counter_example { detail } ->
      Printf.sprintf "SMT counter-example: %s" detail
  | Budget_exceeded { kind = `Deadline } -> "budget exceeded (deadline)"
  | Budget_exceeded { kind = `Tokens } -> "budget exceeded (tokens)"
  | Cancelled { reason } -> Printf.sprintf "cancelled: %s" reason
  | Stale_cas { server_cas } ->
      Printf.sprintf "stale CAS token; server is %s" server_cas
  | Unknown_sentence_id { id } -> Printf.sprintf "unknown sentence id: %s" id
  | Overlay_conflict { names } ->
      Printf.sprintf "overlay conflict: %s" (String.concat ", " names)
  | Session_restarted { reason } ->
      Printf.sprintf "session restarted: %s" reason
  | Load_stopped { file; line; col; loaded_sentences; loaded_line; detail } ->
      Printf.sprintf
        "load stopped at %s:%d:%d — %s (the loaded prefix — %d \
         sentences, through line %d — remains live)"
        (if file = "" then "?" else file)
        line col detail loaded_sentences loaded_line
  | Pool_exhausted { kind = `Lsp } -> "pool exhausted (lsp)"
  | Pool_exhausted { kind = `Mcp } -> "pool exhausted (mcp)"
  | Pool_exhausted { kind = `Spec } -> "pool exhausted (spec)"
  | Protocol_mismatch { detail } -> Printf.sprintf "protocol mismatch: %s" detail
  | Internal { detail } -> Printf.sprintf "internal: %s" detail
