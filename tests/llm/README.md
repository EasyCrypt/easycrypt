# `easycrypt llm` golden-output tests

Byte-identity regression harness for the LLM REPL (`src/ecLlm.ml`).
Each scenario is a small script of REPL commands fed to
`ec.exe llm -eval`; its raw stdout and its process exit status are
compared against recorded goldens.

## Layout

| Path | Contents |
|------|----------|
| `fixtures/*` | tiny EasyCrypt files the scripts `LOAD` (plus one non-`.ec` file, for the unknown-extension error, and one deliberately Latin-1 file used by `../mcp`) |
| `fixtures/sub/*` | a second directory, so a scenario can check that one `LOAD`'s include path does not survive into the next |
| `scripts/*.script` | the newline-separated commands passed to `-eval` |
| `expected/*.out` | recorded stdout, one file per script |
| `../../scripts/testing/llm-golden` | the runner |

## Running

From the repository root:

```
make test-llm                      # build + run every scenario
scripts/testing/llm-golden         # run every scenario
scripts/testing/llm-golden tree-nested commit-nested
scripts/testing/llm-golden --bin /path/to/ec.exe
```

The runner defaults to `_build/default/src/ec.exe`, resolved relative
to the repository root. It prints `PASS`/`FAIL` per scenario, a unified
diff for each mismatch, and exits nonzero if anything failed. That is
the CI invocation.

## Re-recording

```
scripts/testing/llm-golden --record            # all scenarios
scripts/testing/llm-golden --record load-goals # one scenario
```

`--record` overwrites `expected/*.out` with the current binary's
output instead of diffing. It still checks the declared exit status
and reports a mismatch, so a stale `# exit:` line cannot go unnoticed.

Re-record only deliberately: these goldens are the gate for refactors
of `src/ecLlm.ml`, and every diff must be reviewed by hand.

## Expected exit status

Each `.script` declares its expected process exit status on its first
line:

```
# exit: 1
```

Lines starting with `#` are comment lines: the runner strips **all** of
them before handing the script to `-eval`, so they can also be used for
prose. The first `# exit: N` line wins; a script without one fails.

`ec.exe llm -eval` exits 1 if any command produced an `ERROR` reply and
0 otherwise, so scenarios that deliberately exercise error paths
declare `# exit: 1`. That holds however the run ends: `error-exit`
falls off the end of the script, `error-exit-quit` ends on `QUIT` and
`error-exit-phrase` on an `exit.` phrase, and all three declare
`# exit: 1`.

## Determinism rules

The goldens are compared byte for byte, so scenarios must not leak
anything machine- or environment-dependent:

* **Relative paths only.** The runner `cd`s into `tests/llm` before
  invoking the binary, and scripts must refer to fixtures as
  `LOAD "fixtures/foo.ec"`. `LOAD` echoes the filename verbatim in its
  `[loaded:...]` reply tag, so an absolute path would bake the
  developer's home directory into the golden.
* **No SMT.** Fixtures and scripts must never use `smt()`, `smt(...)`
  or `/#`. Proofs close with `trivial`, `done`, `reflexivity` or
  `split`. SMT would make the goldens depend on which provers are
  installed, and on their timing.
* **stdout only.** stderr is discarded; only stdout is compared.
* **No `HELP`.** `HELP` echoes `doc/llm/CLAUDE.md`, which would make
  every documentation edit a test failure. `envelope-escape` covers the
  one property `HELP` would otherwise be needed for — see below.
* Fixtures require `AllCore` only.

## Body escaping

The reply frame is a status line, a body, and a lone `<END>`, and the
body is whatever the engine produced: it can perfectly well hold a line
that is itself envelope-shaped, which would close the frame early.
`doc/llm/CLAUDE.md` does exactly that, so `HELP` used to desynchronize
its own reader.

Call a line *envelope-shaped* when, after dropping any leading spaces,
it is exactly `<END>` or starts with `OK [uuid:`, `ERROR [uuid:` or
`READY [uuid:`. The REPL writes every envelope-shaped **body** line
with one extra leading space; a client drops one leading space from
each envelope-shaped body line it reads, and touches nothing else.
Since leading spaces are part of the test, escaping is idempotent in
the right way — an already-escaped line escapes again — so the rule is
exactly reversible. Status lines are not bodies and are never escaped.

`scripts/envelope-escape.script` pins this. It loads
`fixtures/envelope.ec` with `-trace`, which echoes the traced
sentence's source verbatim; that sentence hides a bare `<END>` and a
bare `OK [uuid:99]` in a comment. The MCP front-end needs no such rule:
its frame is a JSON string.

## Adding a scenario

1. Add `scripts/NAME.script` starting with `# exit: N`.
2. Add any new fixture under `fixtures/`.
3. `scripts/testing/llm-golden --record NAME`.
4. Read `expected/NAME.out` and check it is what you meant to freeze.
