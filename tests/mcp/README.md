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
| `../../scripts/testing/mcp-parity` | the REPL/MCP parity checker (see below) |

## Running

From the repository root:

```
make test-mcp                      # build + run every scenario
scripts/testing/mcp-golden         # run every scenario
scripts/testing/mcp-golden happy-path protocol-errors
scripts/testing/mcp-golden --bin /path/to/ec.exe
scripts/testing/mcp-parity -v          # the parity check, alone
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

## Parity

`make test-mcp` runs `scripts/testing/mcp-parity` after the goldens.
Where the goldens freeze *what* the MCP server answers, the parity
check pins *why the two front-ends can be trusted to agree*: they are
two wire layers over one core, so the same operation must produce the
same answer on both.

It plays one representative operation per tool family — load, step,
goals, tree, focus, undo, checkpoint, step again, revert, search,
commit, and a failing phrase — in that order, against two sessions
started from the same directory (`tests/llm`, so both name the fixture
identically and no path difference can leak into a reply): a REPL
session driven with `llm -eval`, and an MCP session driven with a
JSON-RPC script. For each step it asserts two things.

**The uuid matches.** The REPL's `[uuid:N]` envelope tag against the
MCP result's `structuredContent.uuid`.

**The payload matches.** The REPL's reply body — everything it prints
between the `OK`/`ERROR` line and `<END>` — against the MCP result's
`content[0].text`, *up to one trailing newline*. That slack is the
whole of the licensed difference: the REPL terminates a body that lacks
a newline so that `<END>` starts a line of its own, and MCP, having no
sentinel, does not. The checker appends that newline and then demands
byte equality.

The comparison is derived from the two envelopes rather than pattern
matched out of them: the REPL wire is a sequence of blocks opened by a
status line and closed by a lone `<END>`, and the MCP wire is one JSON
object per line. Both are parsed structurally, so the checker cannot
be fooled by a body that happens to contain something envelope-shaped.

Two asymmetries are structural, and the check deliberately does not
span them:

* **Envelope tags.** The REPL's `[loaded:file:N]` and `[focus: 1/N]`
  annotations ride on the status line, not in the body; MCP's envelope
  is `structuredContent`, which by the plan's result shape carries
  `uuid` and `changed` only. So an MCP client does not see them at all.
  That is a gap worth closing one day — the natural home is a
  `structuredContent` field — but it is not a parity violation: no body
  differs.
* **Notices on failures.** The REPL has never rendered the engine's
  notice buffer on an `ERROR` reply; the MCP failure result does
  include it. The two therefore agree only when the failing operation
  emitted no notices, which is the case for the failing phrase the
  check plays. Should a future step want a noisy failure, this is the
  invariant to weaken — knowingly, and here.

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
