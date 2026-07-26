# VSCODE_LSP.md — survey of upstream's `vscode` branch

Snapshot at `origin/vscode`; merge-base with `origin/main` is
`1b94156480` (current HEAD of main). Two commits on the branch:
`62cbd2d65 LSP` and `7603d8329 MCP`. ~3,500 lines added across 31
files.

Captured for future reference — the user wanted a record so next
session has context without re-surveying the branch. Not a critique;
a map.

## Shape

An LSP server + an MCP server, both shipped as **subcommands of the
main `ec` binary**: `ec lsp` and `ec mcp`. The full daemon lives
inside EC's source tree (`src/ecLsp.ml`, `src/ecMcp.ml`,
`src/ecProofCore.ml`) and compiles as part of the EC executable.
Alongside, a VSCode extension under `vscode/` that speaks LSP to the
binary.

This is **exactly the "merge daemon into `ec` as a subcommand"
architecture** we just debated. They committed to it.

## Worker architecture

No new worker protocol. The daemon spawns `ec cli -emacs` — the
existing emacs-compatible CLI — and reads its prompt:

```ocaml
let prompt_re = Pcre2.regexp "\\[([0-9]+)\\|([^\\]]+)\\]>"
```

Parses `[uuid|mode]>` prompts, buffers output lines between prompts,
returns accumulated text as the reply. No structured wire, no
framing frames, no `PARSE-JSON` / `GOALS-JSON` / `ERROR-JSON` /
`OK-JSON`. Just the raw emacs-mode text output.

One subprocess per document (tracked in a Hashtbl keyed by URI).
No pool, no scratch sessions, no speculation, no overlays. Crash
recovery would mean respawning the doc's session and replaying.

## EC-core changes

Minimal. `src/ecIo.ml` gains one helper:

```ocaml
val next_sentence_from : string -> int -> (string * int * int) option
```

Returns the next complete sentence starting at byte offset `start`
(via the parser's `FINAL` token as the sentence terminator). That's
it — the rest is daemon-side. No PARSE-JSON, no structured goals,
no tagged events. Sentence boundary detection is the only EC-core
addition they needed.

`src/ec.ml` dispatches `| `Lsp -> EcLsp.run (); exit 0` and the
same for MCP.

`src/ecOptions.ml` adds `lsp` and `mcp` subcommands.

## Daemon-core (`ecProofCore.ml`, 477 LoC)

Document state per URI:

```ocaml
type doc_state = {
  mutable text       : BatText.t;          (* current document *)
  mutable last_offset: int;                (* how far we've executed *)
  mutable history    : (int * int) list;   (* (uuid, offset) stack *)
  mutable session    : Easycrypt_cli.session option;
}
```

Operations:
- `did_open` / `did_change` / `did_close` (maintains the text buffer
  in `BatText.t` with position→offset conversion done client-side
  in the daemon via line/column scanning).
- `proof_next` — preview next sentence (peek, don't advance).
- `proof_step` — execute next sentence.
- `proof_jump_to` — execute up to a byte target.
- `proof_back` — `undo N.` via the emacs-mode REPL.
- `proof_restart` — tear down + respawn.
- `proof_goals` — send `goals.` or similar.
- `query` — send `print X.` / `locate X.` / `search X.`.

Error detection: a regex `\[error-\d+-\d+\]` applied to the CLI
output (EC's emacs mode emits these tags). Stripping of the
trailing goal output from the reply when querying.

All async via Lwt (`open Lwt.Syntax`, `Lwt_process` for
subprocess, `Lwt_io` for I/O). No Eio.

## LSP module (`ecLsp.ml`, 665 LoC)

JSON-RPC via ocaml-lsp's `Lsp.Io` functor. Custom method namespace:

| method | purpose |
|---|---|
| `easycrypt/proof/next` | preview next sentence |
| `easycrypt/proof/step` | execute next sentence |
| `easycrypt/proof/jumpTo` | execute up to offset |
| `easycrypt/proof/back` | undo one sentence |
| `easycrypt/proof/restart` | respawn session |
| `easycrypt/proof/goals` | return current goals (text) |
| `easycrypt/query/print` | `print X.` reply |
| `easycrypt/query/locate` | `locate X.` reply |
| `easycrypt/query/search` | `search X.` reply |

Plus standard `initialize` / `initialized` / `shutdown` / `exit` /
`textDocument/didOpen` / `didChange` / `didClose`.

No `publishDiagnostics`, no `hover`, no `documentSymbol`,
`definition`, `workspace/symbol`. No `proof/stateChanged`
notifications. Everything is request/response text.

Logging via `Logs` to `$EASYCRYPT_LSP_LOG` or stderr.

## MCP module (`ecMcp.ml`, 499 LoC)

Same `Lsp.Io` JSON-RPC framing (MCP sits on JSON-RPC), different
namespace. Twelve tools advertised via `tools/list`:

```
open_document, apply_changes, close_document,
proof_next, proof_step, proof_jump_to, proof_back,
proof_restart, proof_goals,
query_print, query_locate, query_search
```

Imperative tool names (noun_verb with underscores) rather than
noun-phrase. `apply_changes` is where document edits land (MCP
client maintains its own document text since it doesn't have a
`textDocument/didChange` notification stream).

## VSCode extension (`vscode/`, 1,020 LoC TypeScript)

- `package.json` declares the `easycrypt` language, the server
  binary (`easycrypt lsp`), commands bound to keybinds
  (`easycrypt.proof.step` etc.), status-bar items, and query
  commands.
- `extension.ts` starts the LSP client with
  `server.command = cfg.path; args = ['lsp']`.
- TextMate grammar in `syntaxes/easycrypt.tmLanguage.json` (101
  lines) for syntax highlighting.
- Status bar has "print current" / "locate current" / "query" that
  resolve to `easycrypt/query/*` methods against the word under
  the cursor.
- Commands registered: step, back, restart, jumpToCursor, goals,
  print, locate, search, statusBar, printCurrent, locateCurrent,
  restart-LSP.
- No tree view, no proof-state side pane, no overlay UI — pure
  command-driven.

## Dependency additions

EC's `dune-project` picks up `lsp`, `lwt`, `logs`, `fmt`, `pcre2`.
That's the deps cost of merging the daemon into EC — they paid it.
No Eio.

## Comparison with our architecture

Same problem, different trade-offs.

| axis | upstream `vscode` branch | our tooling branch |
|---|---|---|
| daemon location | subcommand of `ec` | standalone `ecd` binary |
| worker | `ec cli -emacs` (existing REPL) | `ec llm` (new REPL, additions 1-15) |
| wire to worker | emacs prompts (regex-parsed text) | tagged JSON envelopes (PARSE/GOALS/ERROR/OK-JSON) |
| sentence boundaries | `EcIo.next_sentence_from` (local) | `PARSE-JSON` meta-command |
| goal data | pp-text reply body | `GOALS-JSON` structured + pp-text fallback |
| error classification | regex on `[error-N-N]` | `ERROR-JSON.code` taxonomy |
| sessions | 1 per document | 1 primary per doc + scratch pool |
| scratch / speculation | none | `Speculation.capture/rollback` primitive |
| overlays | none | `OVERLAY_KIND` registry (planned Phase 3) |
| MCP tool names | imperative (`proof_step`) | noun-phrase (`exec_region`) |
| LSP method names | `easycrypt/proof/*` | `proof/*` (unnamespaced) |
| concurrency | Lwt | Eio |
| transcript / replay | none | structured JSON-per-line + `ecd replay` |
| daemon deps in EC | yes (lsp, lwt, logs, fmt, pcre2) | no — daemon isolated |
| VSCode integration | shipped | not started |
| Neovim integration | not attempted | Phase 7 plan |

## What this means for our plan

1. **The merge architecture is proven feasible.** Upstream is
   already running an EC-internal daemon. The deps concern (lsp,
   lwt, etc. inside EC) is settled as acceptable.

2. **Our value proposition sharpens.** Everything their daemon
   *can't* do — structured goals, typed errors, scratch sessions,
   speculation, overlays, replay — is where our architecture
   earns its keep. If we merge later, we'd be replacing their
   text-prompt-parsing with structured wire + speculation.

3. **LSP method namespace collision.** They registered
   `easycrypt/proof/*` and `easycrypt/query/*`. Our plan has
   `proof/*` unprefixed. If we ever ship both daemons and want a
   single VSCode extension to drive either, we need name
   reconciliation. Practical options:
   - Adopt `easycrypt/*` prefix (matches their convention, works
     with their VSCode extension).
   - Keep `proof/*` and ship a new VSCode extension configured
     for our server.
   - Serve both (our daemon responds to both namespaces).

4. **Their VSCode extension is usable as a starting point if we
   adopt their method names.** TypeScript, 1,020 LoC, MIT-
   licensable presumably. Would give us a VSCode client at a
   fraction of the cost of writing one ourselves — at the price
   of conforming to `easycrypt/proof/*` naming and their
   tool-kind request shapes.

5. **Their MCP tool-name convention is different.** `proof_step`
   vs our planned `exec_region`. If we eventually want to be a
   drop-in MCP server for the same Claude Code / agent clients
   they target, we should decide whether to match their names or
   carry both.

6. **No structured diagnostics in their LSP** — no
   `publishDiagnostics`, no typed errors, no hover, no
   `documentSymbol`. Their LSP is "command-dispatch" only. That's
   the ANALYZE-JSON gap we already flagged (addition 14) made
   concrete: they have the same missing feature because they don't
   have a structured error stream to emit.

7. **Sentence boundary via `EcIo.next_sentence_from`.** Simpler
   than our PARSE-JSON meta-command for the specific case of
   "advance one sentence." Could be used as a cheap alternative
   in the daemon's stepping logic — but we need PARSE-JSON
   anyway for the structured-edits and splitter work.

## Things worth reading later

- `src/ecLsp.ml` lines 1-80 — Lsp.Io functor setup. If we adopt
  ocaml-lsp we'd want roughly this shape.
- `src/ecLsp.ml` grep `easycrypt/` — full method catalog.
- `src/ecProofCore.ml` lines 195-250 — position-to-offset
  conversion logic. Clean, portable.
- `src/ecProofCore.ml` bottom half — the step/back/jump/restart
  handlers. Patterns worth matching.
- `src/ecMcp.ml` bottom half — tool dispatch table. 12 tools in
  ~300 lines of handler code.
- `vscode/src/extension.ts` — client wiring, status-bar items,
  command registrations, query handling.
- `MCP.md` — their user-facing MCP setup doc. Worth matching its
  UX spec.

## Actions taken (resolution log)

- ~~Add this branch to the "architectural points" discussion queue~~
  → **Resolved.** Merge architecture is the long-term direction
  (per `doc/tooling-poc-plan.md` § "Merged-binary architecture
  working notes"); Phase 10 reframed accordingly.
- ~~Consider adopting the `easycrypt/` prefix~~ → **Done.**
  `proof_ns = "easycrypt/proof"` constant in `lsp_methods.ml`;
  pinned in `doc/lsp-schema.md` § 1.
- ~~Consider consuming ocaml-lsp (`lsp` opam) for framing~~ →
  **Decided no.** Daemon library uses only `jsonrpc` for
  Packet/Request/Response/Error; we hand-encode LSP method
  payloads. Native Eio framing layer in `tooling/lib/lsp_io.ml`
  (no `Lsp.Io.Make` functor). The `lsp` package stays in the
  boundary allowlist for future conformance smokes that want
  typed `Lsp.Types.*` constructors.
- Keep diff-tool bookmarks handy for the re-review when upstream
  lands this on main. (Still open — future task.)
