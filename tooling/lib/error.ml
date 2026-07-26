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
  | Pool_exhausted { kind = `Lsp } -> "pool exhausted (lsp)"
  | Pool_exhausted { kind = `Mcp } -> "pool exhausted (mcp)"
  | Pool_exhausted { kind = `Spec } -> "pool exhausted (spec)"
  | Protocol_mismatch { detail } -> Printf.sprintf "protocol mismatch: %s" detail
  | Internal { detail } -> Printf.sprintf "internal: %s" detail
