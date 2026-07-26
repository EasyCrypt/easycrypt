# Commit conventions

**Purpose.** The tooling project lives in the EasyCrypt monorepo during
the PoC and will split afterwards into at least one new repo (daemon)
plus an upstream PR set (EC-core additions). Commit prefixes label which
component a change belongs to so the split is mechanical — `git
filter-repo`, cherry-pick, or grep-over-log, all trivial — and so
reviewing history stays fast.

## Prefix grammar

```
<prefix>: <short summary>
```

- Prefix is lowercase, ends with `:`, no scope parentheses.
- Short summary is imperative mood, capital-letter start, no trailing `.`
  (matches existing EC style).
- One component per commit. If a change spans components, split it.

## Prefixes

| Prefix         | Owns                                                             | Destination at split             |
| -------------- | ---------------------------------------------------------------- | -------------------------------- |
| `ec-core:`     | `src/`, `theories/`, `etc/`, `3rdparty/`, `assets/`, `examples/`, `scripts/`, root `dune`/`dune-project`/`Makefile` (EC parts), `doc/llm/` | Upstream EC PR set               |
| `ec-core-critical:` | Subset of the `ec-core:` file set: soundness-touching root-cause fixes inside the EC kernel surface (TCB seeds + immediate-kernel modules per `doc/tcb-discipline.md` — `EcEnv`, `EcTyping`, `EcCoreGoal`, `EcLowGoal`, `EcReduction`, `EcMatching`, `EcCoreFol`, prover bridge, kernel tactics). Distinguished by impact: changes here can admit unsound proofs or reject sound ones. | Upstream EC PR set (carefully)   |
| `daemon:`      | `tooling/daemon/**`                                              | Tooling repo                     |
| `nvim:`        | `tooling/nvim/**`                                                | Neovim plugin repo               |
| `vscode:`      | `vscode/**` (TypeScript extension client)                        | VSCode extension repo            |
| `tui:`         | `tooling/tui/**`                                                 | Tooling repo (or its own)        |
| `tree-sitter:` | `tooling/tree-sitter/**` (when it exists)                        | Tree-sitter grammar repo         |
| `docs:`        | Shared / project-level docs: `doc/tooling-*.md`, `UPSTREAM.md`, `README.md` additions that span components | Tooling repo                     |
| `build:`       | `flake.nix`, `flake.lock`, Nix-level infra, root build glue that spans components | Split per content, case-by-case  |
| `ci:`          | `.github/workflows/**`, CI helpers                               | Split per content, case-by-case  |
| `merge:`       | Merge commits only                                               | Stays with the enclosing history |

## Rules

1. **One component per commit.** A mixed change (e.g., new EC hook +
   daemon wiring) is two commits: `ec-core: ...` then `daemon: ...`.
2. **`ec-core:` commits must match `UPSTREAM.md`.** Every `ec-core:`
   commit corresponds to an entry under "Additions" or "Exceptions" in
   `UPSTREAM.md`. If a commit touches EC core for a reason not in
   `UPSTREAM.md`, either add the entry in the same commit or record it
   in the Exceptions section.
3. **When unsure**, file location wins: anything under `tooling/` is
   not `ec-core:`; anything outside `tooling/` and `doc/tooling-*` is
   not `daemon:`.
4. **Merge commits**: `merge:` followed by a short summary of what was
   merged and why. Resolution-only merges get `merge: <branch-a> into
   <branch-b>`.
5. **Revert**: `revert: <prefix>: <original summary>` — the revert
   itself inherits the reverted commit's component.
6. **Doc-update discipline.** Any commit that changes wire shape,
   addition status, phase status, or other normative content touches
   the relevant doc(s) in the same commit. Docs and code stay in
   sync atomically — no "doc PR follows" pattern. Specifically:
   - Wire / protocol changes: `doc/tooling-protocol.md`,
     `doc/lsp-schema.md`, `doc/mcp-schema.md`.
   - EC-core addition status changes: `UPSTREAM.md`.
   - Phase status / sequencing / scope changes:
     `doc/tooling-poc-plan.md`, `STATUS.md`.
   - Catalog / pattern changes (e.g., recovery patterns,
     overlay registry entries when those exist):
     `doc/lax-recovery-catalog.md` and equivalents.
   Commit reviewer rejects PRs that change normative content
   without the matching doc update. Light-touch enforcement; trust
   the convention.
7. **`ec-core-critical:` discipline.** Soundness-touching changes
   require explicit pre- AND post-approval from the maintainer
   (no autonomous execution, even in auto mode). Each commit:
   - **Pre-approval**: written proposal before any code is
     written — code path, semantic shift, soundness argument,
     files, expected LoC, test plan including TCB-strict gates.
     Maintainer's explicit "go" required.
   - **Root-cause focus, no scope creep**. No "while I'm here"
     refactors / cleanups / renames. Scope locked at pre-approval.
   - **Soundness preservation argument**. Explicit text: "this
     does NOT admit a previously-rejected proof, does NOT reject
     a previously-accepted one." Behavioral parity is the default;
     only the failure mode improves.
   - **Detailed inline documentation** at the change site
     explaining the mechanism being repaired and why this fix is
     correct. UPSTREAM.md entry linked to the addition status.
   - **Post-approval**: maintainer reviews diff + tests +
     soundness argument + concrete repro before commit.
     Maintainer's explicit "commit" required.
   - **TCB-strict tests**: differential oracle + replay corpus +
     grammar corpus must be re-run and reported, per
     `doc/tcb-discipline.md` § "TCB code".
   - **Reversal plan**: commit message notes expected lifetime
     (dissolves into redesign? supersedes a Tier-2 wrapper?).
   Other prefixes (`daemon:`, `vscode:`, non-critical `ec-core:`,
   etc.) keep their existing workflow.

## Enforcement

- **Now**: convention + trust. A ready-to-install `commit-msg` hook
  lives at `scripts/hooks/commit-msg`; install manually
  (`ln -s ../../scripts/hooks/commit-msg .git/hooks/commit-msg` or
  equivalent). The hook is not installed automatically.
- **Later**: CI check on PR commit messages. Lands when we enable
  branch-protection on the tooling split.

## Examples

Good:
- `daemon: Scaffold tooling/daemon with Eio and Cmdliner`
- `ec-core: Preserve newlines across <BEGIN>/<DONE>`
- `docs: Add UPSTREAM.md inventory`
- `ci: Add boundary lint workflow`
- `merge: origin/main into llm-interactive`

Bad:
- `feat: add thing` — no component prefix.
- `daemon: add thing. Fix EC bug.` — mixed components.
- `ec-core: tweak parser` — no UPSTREAM.md entry, no Exceptions log.
- `Add X` — no prefix.
