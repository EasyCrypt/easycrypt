(** Parse EC's `search` reply. Results come back as a sequence of
    `NOTICE:` frames; our session backend already splits those out as
    [exec_ok.notices]. This module groups them by the `(* qname *)`
    marker EC emits before each hit and extracts typed records.

    Used by the semantic-TUI's "apply lemma" picker and by MCP
    `search_lemma` (Phase 6) until addition 9 lands a structured
    search reply. *)

type hit = {
  qname     : string;
  (** Fully-qualified name, as EC's `(* ... *)` marker printed it. *)
  kind      : string;
  (** "lemma" / "operator" / "axiom" / etc. First word of the
      declaration body; empty string if the body didn't start with a
      recognizable keyword. *)
  short_name : string;
  (** Short name — second token of the declaration body, before the
      colon. Empty if not extractable. *)
  signature : string;
  (** Full declaration text joined into one string (multi-line
      signatures are joined with spaces). *)
}

(** [of_notices notices] returns one [hit] per `(* qname *)`-led
    group. Notice lines that don't belong to any group (e.g. stray
    diagnostic output) are dropped. *)
val of_notices : string list -> hit list
