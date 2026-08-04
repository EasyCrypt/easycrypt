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
  | Load_stopped of {
      (* A document LOAD stopped at a failing sentence (field report
         B15). [file]/[line]/[col] is the error's reported position —
         [file] may be a require'd file. [loaded_sentences]/
         [loaded_line]: how much of the TOP file remains loaded; the
         session state IS that prefix, so callers may keep the
         session and resume at the boundary. *)
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

val to_string : t -> string
(** Human-readable rendering. *)

val code : t -> string
(** Stable machine-readable code (e.g. ["parse_error"]). *)
