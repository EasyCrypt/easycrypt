# EasyCrypt VSCode extension — beta-1

> **Status: this is a rolling beta.** Expect bugs. Feedback is
> tracked out-of-band — message Gustavo directly with
> reproductions + the output of the `EasyCrypt: Report a bug`
> command (see [Reporting bugs](#reporting-bugs) below). New
> builds get pushed to you directly when ready; there's no
> auto-update yet.

This is the user-facing entry point for the EasyCrypt VSCode
extension. For implementation context + design notes, read
[STATUS.md](STATUS.md) and [HANDOFF-VSCODE-FIRST.md](HANDOFF-VSCODE-FIRST.md).

## Install

### Pick a `.vsix` variant

1. **`easycrypt-tooling-bundled-<platform>.vsix`** (recommended
   for first-time users): includes pre-built `ec` + `ecd`
   binaries for your platform, with the **Circuits** EC-core
   features merged in (see [Circuits features](#circuits-features)
   below). Just install and open an `.ec` file. Available for
   `darwin-arm64`, `darwin-x64`, `linux-x64`.
2. **`easycrypt-tooling-slim.vsix`**: no bundled binaries —
   you'll point the extension at your own EC install. Use this
   if you have a custom EC build or are working on EC's source.

### Install steps

1. Download the appropriate `.vsix` from the link Gustavo sent.
2. Open VSCode → Extensions panel → `…` menu → "Install from
   VSIX…" → select the file.
3. Reload VSCode when prompted.
4. (Slim variant only) Open settings, search "easycrypt-tooling",
   set:
   - `easycrypt-tooling.ec.path`: absolute path OR executable
     name (searched in `$PATH`) for the EC binary. E.g.
     `easycrypt`, `ec.native`, or `/path/to/ec`.
   - `easycrypt-tooling.daemon.path`: same for the daemon
     (`ecd` or absolute path).
5. Open any `.ec` file. The goal pane should auto-open after a
   few seconds.

### Environment variables (override settings)

- `EC_BIN`: same as `easycrypt-tooling.ec.path` setting.
- `ECD_BIN`: same as `easycrypt-tooling.daemon.path` setting.

Resolution order: env var → workspace setting → user setting →
PATH search → bundled fallback (if shipped).

## First proof — quick walkthrough

1. Create `hello.ec`:
   ```easycrypt
   require import AllCore.

   lemma triv : 1 + 1 = 2.
   proof.
     trivial.
   qed.
   ```
2. Open it. The **goal pane** auto-opens beside the editor.
3. Step through with `Cmd/Ctrl+Alt+N` (Step Forward); the green
   "locked region" tint shows what's been processed.
4. After `proof.`, you'll see the goal `1 + 1 = 2`.
5. Step past `trivial.` — goal closes.
6. Step past `qed.` — proof complete.

`Cmd/Ctrl+Alt+B` steps back. `Cmd/Ctrl+Alt+Enter` executes to
cursor. `Cmd/Ctrl+Alt+G` toggles the goal pane.

## Keybind cheat sheet

### Default keybinds

| Action | Default |
|---|---|
| Step forward | `Cmd/Ctrl+Alt+N` |
| Step back | `Cmd/Ctrl+Alt+B` |
| Execute to cursor | `Cmd/Ctrl+Alt+Enter` |
| Revert to cursor | `Cmd/Ctrl+Alt+Shift+Enter` |
| Show goals | `Cmd/Ctrl+Alt+G` |
| Restart proof state | `Cmd/Ctrl+Alt+R` |
| Cycle displayed subgoal next/prev | `Cmd/Ctrl+Alt+]` / `Cmd/Ctrl+Alt+[` |
| Move builder | `Cmd/Ctrl+Alt+M` |
| Rewrite builder (5-slot) | `Cmd/Ctrl+Alt+W` |
| Apply lemma picker | `Cmd/Ctrl+Alt+L` |
| Tactic builder launcher (any tactic) | `Cmd/Ctrl+Alt+T` |
| Print symbol | `Cmd/Ctrl+Alt+;` |
| Print symbol under cursor | `Cmd/Ctrl+Alt+Shift+;` |
| Search symbols | `Cmd/Ctrl+Alt+/` |
| Try a tactic (preview only) | `Cmd/Ctrl+Alt+T` (then "free text") |

All commands also reachable via the Command Palette (`Cmd/Ctrl+Shift+P`)
under the **EasyCrypt** category, and remappable via
`File → Preferences → Keyboard Shortcuts`.

### PG-style preset (opt-in)

If you're transitioning from Proof General in Emacs, set:

```json
"easycrypt-tooling.keybindings.preset": "pg"
```

This swaps in PG-emacs-style chords (where they translate
sensibly to VSCode's modifier conventions). Per-command list:
TBD.

### Mouse line selection (in proofs over inlined programs)

When you have a hoare / phoare / equiv goal active in the goal
pane:
- **Click a program row** to select it (highlighted).
- **Shift+click another row** to extend to a range (must be on
  the same side + same nesting level).
- **Right-click** to open the context menu:
  - "Rewrite at line N" — opens the 5-slot rewrite builder
    targeting that line.
  - "Change at line N" / "Change range N..M" — opens the proc
    change popup (replace the selected range with new
    instructions, optionally binding fresh local vars).

## Settings reference

| Setting | Default | Description |
|---|---|---|
| `easycrypt-tooling.ec.path` | (auto) | EC binary — abs path or PATH-searched name |
| `easycrypt-tooling.daemon.path` | (auto) | Daemon binary |
| `easycrypt-tooling.stdlibPath` | (auto) | EC theories/ stdlib location (rare; auto-detect first) |
| `easycrypt-tooling.preview.timeoutMs` | 3000 | Tactic-preview timeout (ms); cancel + clear preview after this |
| `easycrypt-tooling.session.maxActive` | 4 | Max active proof sessions per LSP connection |
| `easycrypt-tooling.session.idleTimeoutMs` | 120000 | Idle eviction timeout (ms); 0 to disable |
| `easycrypt-tooling.session.disableEviction` | false | Master toggle: never auto-evict sessions |
| `easycrypt-tooling.keybindings.preset` | "default" | "default" or "pg" |
| `easycrypt-tooling.display.prettify` | true | Render `Pr` as ℙ, `<$` as ←$, etc. |
| `easycrypt-tooling.display.equivAlignment` | "aligned" | "aligned" or "independent" — equiv side-by-side numbering |

Multi-project workspaces work natively: each `easycrypt.project`
file's directory is a "project root"; the daemon spawns a
separate EC subprocess per project (auto-discovered by walking
up from each file's directory).

## Circuits features

The bundled `.vsix` carries the EC-core delta from the
`bdep_ecCircuitsRefactor` branch, layered on top of `main`. This
gives you, in a single install:

- **`cr_binding`** declarations — Circuits' constraint-rewriting
  bindings; new `Gcrbinding` global form, dispatched through
  `process_crbind`.
- **`Pcircuit` PHL tactics** — `bdep solve` / `bdep simplify` for
  bit-level Hoare reasoning.
- **`/~` rewrite-rule rigid flag** — opt-in rigid matching on
  delta-rewrites (`rewrite /~ <pattern>`).
- **`bdhoare`-aware code transforms** — `kill`, `alias`, `set`,
  `set_match`, `cfold` accept BDHoare goals (Circuits' `~bdhoare`
  flag wired through).
- **BWZ SMT solver path** — Circuits' `lospecs` dispatch for the
  `bdep` workflow.

Slim `.vsix` users on stock `main` EC won't see these.

## Known limitations (rolling beta)

- **BWZ SMT cancellation** (bundled `.vsix` only): SMT calls
  going through the BWZ path don't honor cancel signals — once
  you launch one, you wait for it to finish (~16s max under
  EC's iterate retries). Why3-routed SMT (`smt()`, `/#`) cancels
  normally. Workaround: avoid mid-`bdep` cancels.
- **`bind` × Jasmin × undo** (bundled): rolling back through a
  `bind op` declaration that involves Jasmin types (`W8.t`,
  `W16.t`, etc.) and then re-executing forward can fail with
  `the symbol <op> already exists`. The cr_binding undo path
  works correctly for stock EC types (verified with bool /
  QFABV); only the Jasmin theory tree hits it. Workaround:
  restart the EC subprocess (Cmd+Alt+R) instead of stepping back
  past a `bind op` line. Tracked upstream in EC.
- **Looping rewrites with `!` modifier on certain lemmas** can
  hang the editor for a few seconds before the preview-cancel
  timeout fires. If it locks longer, use the Cancel button in
  the goal pane.
- **Slow SMT calls** (`/#`, `smt()`, `move => /#` etc.) can
  similarly hang briefly until cancel kicks in.
- **`proc rewrite`'s slot UI** lets you set reverse / repeat /
  occurrence / pattern but EC's tactic only supports forward
  in this beta — non-forward slots will preview-fail. The next
  ec-core update enables them.
- **Match-arm proc rewrite/change** works (after the recent
  `MatchByPos` walker addition), but match-arm row labeling in
  the goal pane shows just the bound variables (constructor
  name not yet surfaced — UPSTREAM #24 known gap).
- **Extension reload required** after editing
  `easycrypt-tooling.*` settings — VSCode doesn't auto-reload
  the language client on settings change.
- **No automatic update** — when a new `.vsix` is ready,
  Gustavo will send it directly. Re-install via Extensions panel
  → install from VSIX.

Full known-issues list lives in [STATUS.md § Known
bugs](STATUS.md#known-bugs--deferred-investigations).

## Reporting bugs

Issue tracking is **out-of-band** during the beta. Direct message
Gustavo with:

1. The reproduction (smallest `.ec` file that triggers the bug).
2. Expected behavior + actual behavior.
3. The output of the **`EasyCrypt: Report a bug`** command
   (Command Palette). This bundles the daemon log, extension
   state, and recent activity into a tarball — open it, copy
   the contents into your message.

Critical bugs (data loss, daemon crash, anything blocking work):
include `[urgent]` in the subject.

## Updating

When a new build is ready:
1. Gustavo sends you the new `.vsix`.
2. Extensions panel → uninstall the old version.
3. Install from VSIX with the new file.
4. Reload VSCode.

A "check for updates" command pointing at a hosted release page
is planned for after the marketplace publication; for the
private beta, the manual loop is fine.

---

Welcome to the beta. Happy proving.
