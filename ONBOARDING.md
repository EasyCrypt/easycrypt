# ONBOARDING — tooling worktree (`llm-interactive` branch)

Procedure for fresh sessions. Stable across sessions; volatile state
lives in [STATUS.md](STATUS.md).

## Required reading (in order)

1. **Memory file (auto-loaded at session start):**
   `~/.claude/projects/-Users-gdel-Repos-easycrypt/memory/MEMORY.md`
   plus `project_tooling_workstream.md` — entry points, workflow
   gotchas, pinned decisions.
2. **`STATUS.md`** (repo root) — current phase snapshot, landed
   additions, test coverage, next-natural-moves, open issues.
   Updated each session; the source of truth for "where are we now".
3. **`HANDOFF-VSCODE-FIRST.md`** (repo root) — staged plan tracker
   (Stages 1-4 + Slice A-D + parity plan Phases 0-4). What's done,
   what's next, design decisions for the next-up work.
4. **`UPSTREAM.md`** (repo root) — authoritative status of every
   EC-core addition. Memory and STATUS.md are snapshots; this file is
   truth.
5. **`doc/tooling-poc-plan.md`** — phase sequencing (0a→10),
   cross-cutting commitments, "Shipping against upstream redesigns"
   four-tier wrapper strategy, Deferrals, Post-PoC anchors, Open
   architectural points, Risk register, Phase 5-parity plan.
6. **`doc/tooling-protocol.md`** — wire-level spec for the daemon ↔
   `ec llm` subprocess. Framing, addressing, CAS, error taxonomy,
   notifications, reconnect, directive enumeration, uuid invariant,
   pp-text inventory.
7. **`doc/lsp-schema.md`** — wire-level spec for the daemon ↔ LSP
   client surface. Methods, notifications, capability handshake.
8. **`doc/tooling-roadmap.md`** — feature ambitions, semantic edit
   mode S1→S3 arc, design commitments.
9. **`doc/commit-conventions.md`** — commit prefix grammar
   (`ec-core:` / `daemon:` / `nvim:` / `tui:` / `vscode:` / `docs:` /
   `build:` / `ci:` / `merge:` / `revert:`).
10. **`doc/tcb-discipline.md`** — TCB overapproximation heuristic;
    gates `ec-core:` commit testing requirements.
11. **`doc/golden-policy.md`** — three-tier golden assertion policy;
    when to use byte-strict vs structural vs substring goldens.
12. **`VSCODE_LSP.md`** (repo root) — survey of upstream's `vscode`
    branch (their LSP + MCP + VSCode extension). We adopted their
    `easycrypt/proof/*` namespace and ported the TextMate grammar.

Read STATUS + HANDOFF first; the rest revisit as relevant.

## Where the code lives

- **Tooling library:** `tooling/lib/` — every module has `.mli`.
  - Session: `ec_llm_session.ml` (subprocess backend), `session.mli`.
  - Document model: `document.ml`, `sentence_id.ml`, `workspace.ml`.
  - Edit primitives: `edit_ops.ml`, `speculation.ml`.
  - Wire helpers: `goal_view.ml`, `fuzzy_filter.ml`, `search_result.ml`.
  - REPL command core: `repl_core.ml` (used by both `ecd repl` and
    `ecd tui`).
  - Proof workflow: `proof_state.{ml,mli}` — per-LSP-connection
    primary session driver (Slice A). All mutations serialized via
    `Eio.Mutex`. Backs the `easycrypt/proof/*` LSP methods.
  - LSP machinery: `lsp_io.{ml,mli}` (Eio-native Content-Length
    framing), `lsp_server.{ml,mli}` (inbound packet loop, request
    fibers, write_mutex), `lsp_methods.{ml,mli}` (default handler
    registrations + auto-reconcile).
  - Daemon-side substrate: `log.{ml,mli}`, `crash_handler.{ml,mli}`,
    `request_registry.{ml,mli}`, `debouncer.{ml,mli}` (serialized
    process loop — see commit `7a6318d03`),
    `configuration.{ml,mli}`, `daemon_discovery.{ml,mli}`.
  - Other substrate: `transcript.ml`, `replay.ml`, `correlation.ml`,
    `error.ml`, `publish.ml`, `stub_publish.ml`, `pool.ml`,
    `overlay.ml`, `plugin.ml`, `surface_ctx.ml`.
- **Daemon binary:** `tooling/daemon/` — `main.ml` (subcommands:
  `drive`, `repl`, `tui`, `replay`, `daemon` [+ `--stdio`]),
  `repl.ml`, `tui.ml`, `semantic_tui.ml`.
- **VSCode extension:** `vscode/` (TypeScript). `package.json`,
  `src/extension.ts` (~400 LoC; spawns `ecd daemon --stdio`,
  locked-region tinting, goal-pane WebviewPanel, step/back/exec/
  revert/goals/restart commands). Build: `cd vscode && npm install
  && npm run compile`. Repo-root `.vscode/launch.json` lets F5
  open an Extension Host.
- **Smoke tests:** `tooling/smoke/` — 18 stanzas. See
  [STATUS.md](STATUS.md) test-coverage table. Run via `dune test`.
- **EC-core changes:** `src/ec.ml`, `src/ecCommands.ml`, `src/ecIo.ml`,
  plus `src/ecExecJson.ml`. Every change tracked in `UPSTREAM.md`.

## Running things

- **Tests:** `dune test` (or `dune build @runtest`). Runs the full
  smoke suite green. 18 test stanzas; see [STATUS.md](STATUS.md)
  for what each covers.
- **Diagnostic:** `dune exec tooling/smoke/run_search_debug.exe -- <pat>`.
  Not a regression test; raw EC search output for ad-hoc inspection.
- **REPL:** `dune exec ecd -- repl <file.ec>`.
- **TUI:** `dune exec ecd -- tui <file.ec>`.
- **Replay a transcript:** `dune exec ecd -- replay <transcript.jsonl>`.
- **Drive a file end-to-end:** `dune exec ecd -- drive <file.ec>`.
- **Long-running LSP daemon (Unix socket):**
  `dune exec ecd -- daemon [--label NAME]`.
- **One-shot LSP daemon over stdio** (used by VSCode-style editor
  extensions): `dune exec ecd -- daemon --stdio`.
- **VSCode extension demo:** open the repo root in VSCode (with
  the nix devshell active so `node`/`npm` are on PATH), `cd vscode
  && npm install && npm run compile`, then F5 (uses
  `.vscode/launch.json`). Set `easycrypt-tooling.ec.path` if your
  EC binary isn't named `easycrypt` (e.g. `ec.native`).

## Workflow gotchas

- Nix flake evaluates from the git tree. New or modified files are
  invisible to `nix build` / `nix develop` unless `git add`ed
  (content, not just intent-to-add). Stage before running Nix.
- `dune build` from the direnv-loaded shell works for already-resolved
  deps. After adding a new opam dep to `tooling/tooling.opam`
  (generated from the root `dune-project`), re-enter via
  `nix develop .#withDevTools --command dune build ...` to refresh
  the opam-nix scope.
- Commit-msg hook at `scripts/hooks/commit-msg` is opt-in; install
  with `ln -s ../../scripts/hooks/commit-msg .git/hooks/commit-msg`.
- Boundary lint at `scripts/boundary-lint.sh` enforces `tooling/**`
  dune `(libraries ...)` are allowlisted in
  `tooling/.boundary-allowlist`.

## Commits convention

- One component per commit, per `doc/commit-conventions.md`.
- Every `ec-core:` commit corresponds to an `UPSTREAM.md` entry (or
  an Exceptions row).
- Always include the trailer
  `Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>`.
- Don't skip hooks (`--no-verify`) unless the user explicitly asks.
- Don't commit unless the user asks.

## User's working style

(Memory carries these too. Listed here for first-session continuity.)

- Ask short clarifying questions rather than guessing — especially
  for scope, ec-core touches, or destructive actions.
- TUI must reach parity with REPL — every `ecd tui` capability is
  reachable via `ecd repl` too. Preserves scripted-test coverage.
- Draft tests before implementation when practical.
- Leaf terms stay pp-text inside structured envelopes (post-PoC
  deferral of full-AST JSON). Every new EC→JSON endpoint adds a row
  to the protocol doc's § 2.4 pp-text inventory in the same PR.
- Ask before writing parser code against EC pretty-printed output —
  even though we've done it a few times with approval.
