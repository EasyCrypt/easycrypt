(** Buffer-level splice primitives shared by [Repl_core]'s
    `:insert` / `:edit` / `:delete` (and, later, LSP refactors and
    MCP LLM-authored edits). Post-addition-16 there is no
    leading-whitespace scan — PARSE-JSON's [start_offset] is already
    at the first real token of each sentence, so splice bounds come
    straight off the parse.

    These operations are pure w.r.t. the daemon session state:
    they only edit the document buffer and re-run PARSE-JSON against
    the new source. Advancing the primary session, rolling back on
    truncation, or updating cursor state belongs to the caller. *)

type error = Error.t

(** Insert content just before the executable sentence at
    [before_executable_index], or at end-of-file if the index is
    past the last executable. The new source is the old source with
    [content] spliced in, with newlines injected at the splice
    boundaries if needed to preserve line structure. *)
val insert_before :
  session:Ec_llm_session.t ->
  doc:Document.t ->
  before_executable_index:int ->
  content:string ->
  (Document.t, error) result

(** Replace [target]'s byte range with [content]. Target is given as
    a [Document.sentence] from the caller's current parse. *)
val replace :
  session:Ec_llm_session.t ->
  doc:Document.t ->
  target:Document.sentence ->
  content:string ->
  (Document.t, error) result

(** Remove [target]'s byte range, consuming the immediately-following
    newline if present so a blank line is not left behind. *)
val delete :
  session:Ec_llm_session.t ->
  doc:Document.t ->
  target:Document.sentence ->
  (Document.t, error) result
