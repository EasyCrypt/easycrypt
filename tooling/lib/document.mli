(** Documents: source text + its sentence split, keyed by content-
    addressed sentence ids. Phase 2 primitive consumed by the daemon's
    `didOpen`/`didChange` handling and by the differential oracle.

    A [t] is pure data — it owns no session state. Splitting is done
    through an Ec_llm_session (any working session will do, typically
    a pooled scratch). The sentence→uuid map that backs [revert_to]
    lives on the session that actually executed the sentences; a
    Document only describes the latest parse. *)

type sentence = {
  id      : Sentence_id.t;
  parsed  : Ec_llm_session.parsed_sentence;
}

type t = {
  uri       : string;
  version   : int;
  source    : string;
  sentences : sentence list;
}

val parse :
  Ec_llm_session.t ->
  uri:string ->
  version:int ->
  source:string ->
  (t, Error.t) result
(** Run the session's PARSE-JSON over [source] and build a [t]. [uri]
    is echoed back in the result; [version] defaults to 0. *)

type diff = {
  unchanged_prefix : sentence list;
  (** Leading run of sentences whose ids match (by content) between
      the old and new documents. The session driving the primary can
      reuse the uuids it has for these without re-exec. *)

  removed : sentence list;
  (** Sentences present in [old] after the prefix that no longer
      appear in [new_]. These need REVERT or overlay-drop handling. *)

  added : sentence list;
  (** Sentences present in [new_] after the prefix that weren't in
      [old]. These need fresh exec. *)
}

val diff : old:t -> new_:t -> diff
(** Compute a minimal diff. v0 uses a common-prefix split — matches
    the primary session's step-through model where any change at
    position [i] invalidates [i..] but preserves [0..i-1]. More
    sophisticated LCS-based diffs (to handle mid-document edits that
    leave suffixes intact) lands when we care about overlay-only
    edits; for the primary feed, prefix is what matters. *)
