(** Default registrations of LSP methods against an [Lsp_server.t].
    Each [register_*] function installs handlers for a related set
    of methods; surface plugins may override or augment.

    **PoC method coverage** ([doc/lsp-schema.md] §§ 2-4):
    - lifecycle: initialize / initialized / shutdown / exit.
    - textDocument: didOpen / didChange / didClose. Notifications
      cache the latest source per uri in [doc_sources] so proof
      methods can drive the primary session against in-memory
      content.
    - publishDiagnostics: server notification, driven by ANALYZE-JSON
      (addition 14, landed). Triggered on every didChange (debounced).
    - custom proof methods (real bodies driving the per-connection
      primary [Proof_state]; cache layer arrives Phase 5.0 without
      a wire change):
      - easycrypt/proof/execToPoint
      - easycrypt/proof/revertToPoint
      - easycrypt/proof/goals
      - easycrypt/proof/step (advance one)
      - easycrypt/proof/back (revert one)
      - easycrypt/proof/restart (tear down + respawn primary)
      - easycrypt/proof/tryTactic (parity Phase 3 — speculative
        one-shot, sugar over [Proof_speculation.try_tactic])
      - easycrypt/proof/suggestClosers (parity Phase 3 — sweep over
        [Proof_speculation.suggest_closers]).
    - emits [easycrypt/proof/stateChanged] notifications on every
      successful state mutation.
    - hover / documentSymbol / definition: gated on Phase 4
      (additions 2/9/10) — these stubs return 'unsupported' until
      then.

    **Status**: implemented (Phase 5-core / VSCode-first Stage 4). *)

(** Method namespace constant. Single point of change for atomic
    flips — see [doc/lsp-schema.md] § 1. *)
val proof_ns : string

val proof_method : string -> string
(** [proof_method "execToPoint"] = ["easycrypt/proof/execToPoint"]. *)

(** {2 Diagnostic helpers} *)

val publish_diagnostics :
  Lsp_server.t ->
  io:Lsp_io.t ->
  uri:string ->
  source:string ->
  analyze_session:Ec_llm_session.t ->
  unit
(** Run ANALYZE-JSON on [source] and publish the resulting LSP
    Diagnostics to the client. Daemon main wires this as the
    debouncer's [process] callback (which under per-project
    sessions resolves the analyze session via [Session_manager]
    based on the URI). *)

(** {2 Registration} *)

val register_lifecycle : Lsp_server.t -> unit

val register_text_document :
  Lsp_server.t ->
  io:Lsp_io.t ->
  manager:Session_manager.t ->
  sw:Eio.Switch.t ->
  debouncer:(string * string * int) Debouncer.t ->
  doc_sources:(string, string) Hashtbl.t ->
  unit
(** Registers didOpen / didChange / didClose. didChange triggers a
    debounced re-analysis that publishes diagnostics; didOpen /
    didChange also populate [doc_sources] (uri → latest source) so
    proof methods can read the in-memory document content. didChange
    additionally calls [Proof_state.reconcile] to retract the
    URI's project session if the divergence sits inside the locked
    region. UPSTREAM § 14: the [Session_manager] resolves URI →
    project_root → per-project [Proof_state.t] / analyze session. *)

val register_proof_methods :
  Lsp_server.t ->
  io:Lsp_io.t ->
  sw:Eio.Switch.t ->
  manager:Session_manager.t ->
  doc_sources:(string, string) Hashtbl.t ->
  unit
(** Registers easycrypt/proof/* methods backed by per-project
    [Proof_state]s resolved through [manager]. Each successful
    state-mutating call emits an [easycrypt/proof/stateChanged]
    notification carrying the new currentSentenceId. *)

val register_all :
  Lsp_server.t ->
  io:Lsp_io.t ->
  manager:Session_manager.t ->
  debouncer:(string * string * int) Debouncer.t ->
  sw:Eio.Switch.t ->
  doc_sources:(string, string) Hashtbl.t ->
  unit
(** Composition of all register_* above. Called once at server
    startup. *)
