# LLM-oriented tooling for `easycrypt llm`

This directory contains two example clients for the interactive REPL
exposed by `easycrypt llm` (see `doc/llm/CLAUDE.md` for the wire
protocol). They are layered: each can be useful independently, depending
on how your driver (human, script, or LLM agent) is structured.

| Layer | File | Use when |
|-------|------|----------|
| Python binding | `ec_llm.py` | Writing a Python program that drives one EasyCrypt REPL. |
| Fifo daemon | `daemon.py` + `ec_send.sh` | Driving one persistent REPL from *many* short-lived shell invocations — notably LLM agents that issue one bash tool call per tactic. |

## Why a fifo daemon?

`easycrypt llm` is a stateful, long-running process. Python programs can
keep its stdin/stdout pipe open across commands, but many LLM-agent
front-ends (Claude Code, Codex CLI, etc.) only expose the shell via
one-shot command execution. Without a persistent intermediary, every
tactic would require re-LOADing the file prefix — minutes wasted per
step on a large project.

The daemon opens `easycrypt llm` once, listens on a named pipe for JSON
requests, and writes JSON responses to a second named pipe. The
companion `ec_send.sh` is the shell-side client: it takes a single JSON
request, forwards it through the pipes, and prints the structured
response. Combined, they let an agent drive a persistent REPL with one
bash call per step.

## Python binding (Layer 1)

```python
from ec_llm import ECLLM

with ECLLM(cwd="/path/to/project", extra_args=["-p", "Z3"]) as ec:
    ok, resp = ec.load("proofs/myfile.ec", 42, nosmt=True)
    print(ec.goals())
    ok, resp = ec.tactic("smt().")
    print(resp)
```

Everything in the `easycrypt llm` protocol is exposed as a method:
`load`, `checkpoint`, `revert`, `undo`, `goals`, `goals_all`, `tactic`,
`tactic_multiline`, `search`, `quiet`, `close`. Status parsing tracks
the running uuid in `ec.uuid`.

CLI mode provides a quick "LOAD and report" check:

```
python3 ec_llm.py proofs/myfile.ec 42 --cwd /path/to/project --nosmt
```

## Fifo daemon (Layer 2)

Start the daemon once (most easily in the background):

```
# Create the fifos if needed and start the daemon
mkfifo /tmp/ec_in /tmp/ec_out 2>/dev/null || true
python3 scripts/llm/daemon.py \
    --cwd /path/to/project \
    --prover Z3 --timeout 5 &
```

Drive it with `ec_send.sh`:

```
./ec_send.sh '{"op":"load","arg":"proofs/myfile.ec","arg2":"42","nosmt":true}'
./ec_send.sh '{"op":"goals"}'
./ec_send.sh '{"op":"tactic","arg":"smt()."}'
./ec_send.sh '{"op":"checkpoint","arg":"before_split"}'
./ec_send.sh '{"op":"tactic","arg":"split."}'
./ec_send.sh '{"op":"revert","arg":"before_split"}'
```

For payloads with shell-hostile content (EC escapes like `/\\`),
write the JSON to a file and use `--file`:

```
cat > /tmp/req.json <<'EOF'
{"op":"tactic","arg":"rewrite /wpoly_srng !allP => H j Hj; smt(hint)."}
EOF
./ec_send.sh --file /tmp/req.json
```

## Operational tips

- **Per-session setup.** Create fifos once per session. The daemon keeps
  them; don't delete them while it's running.
- **Recovering from a dead daemon.** If the EasyCrypt process crashes
  (stack overflow, OOM on SMT), `ec_send.sh` will hang. Kill the daemon
  process, recreate the fifos (`rm -f /tmp/ec_in /tmp/ec_out; mkfifo
  /tmp/ec_in /tmp/ec_out`), and restart.
- **Fast SMT feedback.** Pass `--timeout 1 --prover Z3` to the daemon
  during exploration; fragile SMT calls surface immediately. Raise the
  timeout when codifying a final proof.
- **Parallel sessions.** To run multiple daemons side-by-side, give each
  a distinct pair of fifo paths and set `EC_IN_FIFO` / `EC_OUT_FIFO`
  for the `ec_send.sh` caller.
- **Logging.** Exceptions inside the daemon are written to `/tmp/ec_daemon.log`
  (or `--log`). Check there first if a request seems silently dropped.

## Security note

The daemon trusts whatever shows up on its input fifo — it forwards the
`arg` payload straight to EasyCrypt as tactic text. Don't expose the
fifos on a shared filesystem, and don't run the daemon as a privileged
user.
