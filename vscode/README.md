# EasyCrypt (tooling daemon) — VSCode extension

Proof-General-style VSCode client for the
[EasyCrypt tooling daemon](../). Connects to `ecd daemon --stdio`
over LSP; locked-region tinting, side-by-side goal pane, real-time
diagnostics, step / back / exec-to-cursor / revert-to-cursor commands.

## Status

Slices A-D landed: real proof methods backed by the daemon's
per-connection `Proof_state`. Pre-Phase-5.0, `provenance` is always
`fresh` and `cas` is zero — the wire shape is pinned per
[`doc/lsp-schema.md`](../doc/lsp-schema.md), so the cache substrate
will fill these in without a wire bump.

What works today:

- Language registration: `.ec` / `.eca` files, syntax highlighting
  via upstream's TextMate grammar (copied verbatim).
- `textDocument/publishDiagnostics` round-trip — daemon dispatches
  `ANALYZE-JSON` on every didChange (debounced); errors render in the
  Problems panel with scope-tagging metadata in `data.scope`.
- **Locked-region tint** (Slice B): subtle green background from
  `(0,0)` to the daemon's `currentEndPosition` — refreshes
  reactively on every `easycrypt/proof/stateChanged`.
- **Goal pane WebviewPanel** (Slice C): side-by-side panel rendering
  the GOALS-JSON envelope. Auto-refreshes on stateChanged.
- **Auto-reconcile on edit** (Slice D): editing inside the locked
  region retracts the primary session; the locked region shrinks
  immediately.

## Commands

| Command                                | Default keybinding        |
|----------------------------------------|---------------------------|
| EasyCrypt: Step Forward                | Ctrl/Cmd+Alt+N            |
| EasyCrypt: Step Backward               | Ctrl/Cmd+Alt+P            |
| EasyCrypt: Execute To Cursor           | Ctrl/Cmd+Alt+Enter        |
| EasyCrypt: Revert To Cursor            | Ctrl/Cmd+Alt+Backspace    |
| EasyCrypt: Show Goals at Cursor        | Ctrl/Cmd+Alt+G            |
| EasyCrypt: Restart Proof Session       | (no default)              |
| EasyCrypt: Restart Language Server     | (no default)              |

Step / back drop OS keyboard-repeat presses while one is in flight
(per-uri in-flight guard) — so holding the key won't queue dozens
of requests at the daemon.

## Settings

| Setting | Default | Notes |
|---|---|---|
| `easycrypt-tooling.daemon.path` | `ecd` | Path to the `ecd` binary; resolved on PATH or absolute |
| `easycrypt-tooling.daemon.args` | `["daemon", "--stdio"]` | Args passed to `ecd` |
| `easycrypt-tooling.ec.path` | (empty) | Path to the EasyCrypt binary (e.g. `easycrypt`, `ec.native`, or absolute). Empty falls through `$EC_LLM_BIN` → in-tree `_build` → `easycrypt` on PATH. When set, extension passes `--bin <path>` to ecd |
| `easycrypt-tooling.trace.server` | `off` | LSP trace level: `off` / `messages` / `verbose` |

## Build & test (manual)

```sh
# In the nix devshell (so node + npm are available):
cd vscode
npm install
npm run compile
```

Then F5 from the **repo root** in VSCode (uses the repo-root
`.vscode/launch.json` which compiles + launches an Extension Host
with `extensionDevelopmentPath=${workspaceFolder}/vscode`).

Inside the Extension Host: open any `.ec` file, watch the Problems
panel for diagnostics, hit `Cmd/Ctrl+Alt+G` for the goal pane,
step with `Cmd/Ctrl+Alt+N`. The Output channel "EasyCrypt (tooling
daemon)" carries daemon stderr (set `easycrypt-tooling.trace.server`
to `messages` or `verbose` to also see LSP traffic).

## Architecture

Pure UX layer over the daemon. All proof-workflow logic lives
daemon-side in `tooling/lib/proof_state.ml` (and, after the parity
plan Phase 0 lift, `tooling/lib/proof_speculation.ml`). The
extension just dispatches LSP requests + renders responses /
notifications.

See [HANDOFF-VSCODE-FIRST.md](../HANDOFF-VSCODE-FIRST.md) for the
plan tracker and design decisions.
