(** Typed error taxonomy used across LSP + MCP surfaces. See
    [doc/tooling-protocol.md] § 6. *)

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

val to_string : t -> string
(** Human-readable rendering. *)

val code : t -> string
(** Stable machine-readable code (e.g. ["parse_error"]). *)
