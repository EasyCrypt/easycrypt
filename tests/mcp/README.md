# `easycrypt mcp` golden-output tests

Byte-identity regression harness for the MCP server (`src/ecMcp.ml`).
Each scenario is a newline-delimited script of JSON-RPC messages fed to
`ec.exe mcp` on stdin; the raw protocol stream it writes on stdout, and
its process exit status, are compared against recorded goldens.

This is the sibling of `../llm`, which does the same for the REPL. The
two front-ends share `src/ecLlmCore.ml`, so most behaviour changes show
up in both sets of goldens — that is the point.

## Layout

| Path | Contents |
|------|----------|
| `scripts/*.script` | the JSON-RPC messages piped into the server |
| `expected/*.out` | recorded stdout, one file per script |
| `../llm/fixtures/*` | the EasyCrypt files the scripts load (shared with the REPL harness, never duplicated) |
| `../../scripts/testing/mcp-golden` | the runner |

## Running

From the repository root:

```
make test-mcp                      # build + run every scenario
scripts/testing/mcp-golden         # run every scenario
scripts/testing/mcp-golden happy-path protocol-errors
scripts/testing/mcp-golden --bin /path/to/ec.exe
```

The runner defaults to `_build/default/src/ec.exe`, resolved relative
to the repository root. It prints `PASS`/`FAIL` per scenario, a unified
diff for each mismatch, and exits nonzero if anything failed. That is
the CI invocation.

## Re-recording

```
scripts/testing/mcp-golden --record             # all scenarios
scripts/testing/mcp-golden --record tools-list  # one scenario
```

`--record` overwrites `expected/*.out` with the current binary's
output instead of diffing. It still checks the declared exit status.

Re-record only deliberately, and read the diff: these goldens are the
gate for changes to the protocol layer.

## Scenarios

| Scenario | What it pins |
|----------|--------------|
| `initialize` | the lifecycle handshake, the `initialized` notification, `ping` |
| `version-negotiation` | an unsupported revision falls back to the latest we speak; a supported one is echoed |
| `tools-list` | the whole tool table: names, descriptions, input/output schemas, annotations |
| `happy-path` | a session end to end: load, step, goals, tree, focus, commit |
| `prover-error` | EasyCrypt-level failures as `isError` results carrying the goal state |
| `try-revert` | `ec_try` rolling back a phrase that had already advanced the proof |
| `protocol-errors` | `-32700`, `-32600`, `-32601` and the `-32602` family |
| `revert` | `ec_revert` by uuid and by checkpoint name |
| `load-missing` | a missing file and an unknown extension: `isError`, *not* `-32602` |
| `notifications` | notifications, known and unknown, draw no reply |
| `exit` | `exit.` answers "session terminated", then the process stops |
| `eof` | end of input is a clean shutdown, exit 0 |

## Expected exit status

Each `.script` declares its expected process exit status on its first
line:

```
# exit: 0
```

Lines starting with `#` are comment lines: the runner strips **all** of
them before piping the script into the server, so they can also be used
for prose. The first `# exit: N` line wins; a script without one fails.

`easycrypt mcp` exits 0 on end of input and 0 after an `exit.` phrase;
EasyCrypt-level failures are `isError` results, not exit statuses, so
every scenario here declares `# exit: 0`. The field is kept all the
same, so that a future exit path cannot change silently.

## Determinism rules

The goldens are compared byte for byte, so scenarios must not leak
anything machine- or environment-dependent:

* **Relative paths only.** The runner `cd`s into `tests/mcp` before
  invoking the binary, and scripts refer to fixtures as
  `"../llm/fixtures/simple.ec"`. Error messages echo the path
  verbatim, so an absolute one would bake the developer's home
  directory into the golden.
* **One normalization, and only one.** `serverInfo.version` is a
  git-describe string; the runner rewrites it to `VERSION` with `sed`
  before diffing. Nothing else is touched — if a second unstable field
  ever appears, that is a bug in the server, not a reason to normalize
  more.
* **No SMT.** As in `../llm`: proofs close with `trivial`, `done` or
  `split`, never with `smt`, whose availability and timing vary by
  machine.
* **stdout only.** stderr carries the engine's diagnostics (the server
  points the process's stdout at stderr and keeps a private descriptor
  for the protocol); it is discarded.
* Fixtures require `AllCore` only.

## Reading a golden

The stream is the protocol: one JSON message per line, unindented,
exactly as a client sees it. `tools-list.out` is therefore a single
very long line, and `diff` will show it whole. To read one by hand:

```
python3 -m json.tool < <(head -n 1 tests/mcp/expected/tools-list.out)
```

## Adding a scenario

1. Add `scripts/NAME.script` starting with `# exit: N`.
2. Reuse a fixture from `../llm/fixtures/`; add a new one there (not
   here) if none fits.
3. `scripts/testing/mcp-golden --record NAME`.
4. Read `expected/NAME.out` and check it is what you meant to freeze.
