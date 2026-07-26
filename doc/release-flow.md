# Release-bundle merge flow

How to produce a bundled `.vsix` that combines `llm-interactive`
(our daemon + vscode work) with `bdep_ecCircuitsRefactor`
(Circuits' EC-core features). Pinned 2026-04-29 during the first
end-to-end attempt.

## Constraints

- `llm-interactive` and `bdep_ecCircuitsRefactor` stay clean —
  the release-merge happens on a throwaway branch.
- We never push branches; only `.vsix` artifacts are shared with
  users.
- `bdep_ecCircuitsRefactor` is the user's local copy of the
  upstream branch (not pushed). The local copy can be modified
  freely (e.g., reverts of inherited `origin/vscode` content).
- `git rerere` + `rerere.autoUpdate` are globally enabled (set
  this once with `git config --global rerere.enabled true &&
  git config --global rerere.autoUpdate true`). Per-cycle
  release-merges replay prior conflict resolutions.

## Per-release workflow

```
# 1. Sync local main with origin/main.
git fetch origin main:main

# 2. Sync llm-interactive with main (no-op if main is already an
#    ancestor; otherwise merge it in).
git checkout llm-interactive
git merge --ff-only main || git merge --no-ff main

# 3. Refresh the cleaned Circuits worktree. Strip any
#    vscode-merge content (Circuits inherits from origin/vscode
#    which collides with our daemon-based extension; we always
#    want llm-interactive's vscode/ in the release).
git worktree remove /tmp/ec-circuits-clean --force 2>/dev/null
git worktree add /tmp/ec-circuits-clean bdep_ecCircuitsRefactor
( cd /tmp/ec-circuits-clean
  for sha in $(git log --first-parent --pretty=format:'%H %s' \
                 main..HEAD | grep -i 'merge.*vscode' | awk '{print $1}'); do
    git revert -m 1 --no-edit "$sha"
  done
)

# 4. Generate the Circuits delta patch (no vscode/).
( cd /tmp/ec-circuits-clean
  BASE=$(git merge-base main HEAD)
  # Bypass any global diff.external (e.g., difftastic) so the
  # output is a real unified-diff patch.
  git -c diff.external= --no-pager diff --binary --no-color \
    --unified=3 "$BASE..HEAD" -- ':!vscode' \
    > /tmp/circuits-clean.patch
)

# 5. Set up the release worktree from llm-interactive.
git worktree remove ~/Repos/ec-tooling-release --force 2>/dev/null
git branch -D release/beta-1-N 2>/dev/null
git worktree add -b release/beta-1-N \
  ~/Repos/ec-tooling-release llm-interactive

# 6. Apply the patch. Plain `patch -p1` is more predictable than
#    `git apply --3way` here (the global merge-driver attribute
#    `* merge=mergiraf` interferes with git's three-way merge).
( cd ~/Repos/ec-tooling-release
  patch -p1 --no-backup-if-mismatch < /tmp/circuits-clean.patch \
    > /tmp/patch.log
  find . -name '*.rej' | sort  # the surface to resolve
)
```

After this point, conflict resolution is per-file work. The
release-bundle pipeline relies on `rerere` to replay the
resolutions on subsequent cycles.

## What conflicts and how (first-cycle reference)

After the patch apply against the `llm-interactive + main`
base, expect ~26 `.rej` files. Roughly:

- **Spurious afbb-ecall-derived rejects** (~15 files):
  `src/ecAst.mli`, `src/ecEnv.mli`, `src/ecHiTacticals.ml`,
  `src/ecMatching.{ml,mli}`, `src/ecPV.{ml,mli}`,
  `src/ecParsetree.ml`, `src/ecProofTerm.{ml,mli}`,
  `src/phl/ecPhlCall.{ml,mli}`, `src/phl/ecPhlEager.ml`,
  `src/phl/ecPhlExists.{ml,mli}`. **Drop the `.rej` files** —
  Circuits' `b6c6e268a` ≡ main's `afbb8b766` (forward-ecall +
  framed-pre PR), already merged into main, so the patch is
  re-applying a refactor llm-interactive already has.

- **`src/ecEnv.ml`** — take Circuits' wholesale (carries
  crbindings, the `module Theory` relocation past `module
  Circuit`, and afbb's LDecl `push_active_all` change).
  llm-interactive doesn't touch ecEnv.ml so no loss.

- **Wholesale-take-Circuits files** (llm-interactive untouched):
  `src/phl/ecPhlCodeTx.ml`, `src/phl/ecPhlRewrite.{ml,mli}`,
  `tests/procchange.ec`. **But**: ecPhlCodeTx.ml uses
  `~bdhoare:true` arg in 5 calls to `t_code_transform` — strip
  that arg for main's signature.

- **Surgical**: `src/ecCommands.ml` — add one-line `Gcrbinding
  bind -> 'Fct (...)` dispatch entry after the `GdumpWhy3`
  line. `dune` — add `libs` to top-level `(dirs ...)` and add
  an `(env ...)` block disabling warnings 9/23/27/32/58/67/69
  for libs/lospecs (warnings on Circuits' code that doesn't
  match main's strict OCaml 5.x flags).

- **Duplicate-symbol cleanup** (caused by patch + already-merged
  afbb): in `src/ecParser.mly` delete the duplicate
  `direction:` rule; in `src/ecParsetree.ml` delete the
  duplicate `type pecall` / `type pdirection` block AND the
  duplicate `Prwprgm` constructor inside `type phltactic`.

- **Type-name renames**: `src/ecParsetree.ml`'s
  `Psim of crushmode option * sim_info` → `psim_info`.

- **Adapted-to-current-shape**: parser `RWDelta` production now
  emits `(false, rwopt, fp)` to match main's parsetree
  `RWDelta of bool * rwoptions * pformula`. The Circuits-only
  `rigid` flag is opted out (would require record-shape update).
  ecHiGoal.ml's `RWDelta (rwopt, p)` pattern needs to become
  `RWDelta (_rigid, rwopt, p)`.

- **Add Pcircuit case** to `src/ecHiTacticals.ml`'s phl tactic
  dispatch:
  ```
  | Pcircuit `Solve     -> EcPhlBDep.t_bdep_solve
  | Pcircuit `Simplify  -> EcPhlBDep.t_bdep_simplify
  ```

- **flake.nix / flake.lock**: keep llm-interactive's flake (has
  nodejs + tooling deps; load-bearing). For Circuits' nix
  delta, generate a 3-way zdiff3 marker file:
  ```
  cd ~/Repos/ec-tooling-release
  cp /tmp/flake-ours.nix flake.nix.merge
  git merge-file --zdiff3 \
    -L 'ours (llm-interactive)' \
    -L 'base (merge-base)' \
    -L 'theirs (bdep_ecCircuitsRefactor)' \
    flake.nix.merge /tmp/flake-base.nix /tmp/flake-theirs.nix
  ```
  Then hand-merge: bring in Circuits' `conf-zlib`, `conf-git`,
  `alt-ergo`, `frama-c` opam-scope overrides + the cvc5/z3
  version bumps. Keep our nodejs_20 / multi-package
  (easycrypt + tooling) layout. After: `nix flake lock --update-input`
  to refresh `flake.lock`.

- **Skipped Circuits-only feature**: the rewrite-rule `rigid`
  flag (`/~`). Pure additive feature in Circuits' parser +
  process_delta + parsetree record. Not load-bearing for the
  release-bundle's purpose; documented as a follow-up.

After all rejects resolve, expect a few iterative build errors
(duplicate symbols, signature drift, missing dispatch cases) —
each a small targeted fix.

## Build + package

```
cd ~/Repos/ec-tooling-release
make                        # = dune build --profile=dev
EC_LLM_BIN=$(pwd)/ec.native dune build @runtest
( cd vscode && npm install && npm run compile )

# Bundled .vsix (darwin-arm64)
( cd vscode && vsce package --target darwin-arm64 \
    --out easycrypt-tooling-bundled-darwin-arm64.vsix )
```

linux-x86_64: build on the user's linux box; vsce package with
matching `--target linux-x64`. (Defer to follow-up cycle.)

## Tag the release commit

```
git tag release/beta-1-N HEAD
```

Tag-only (no push). The artifact is the `.vsix`; the tag is for
local reproducibility.
