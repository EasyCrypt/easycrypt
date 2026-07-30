# QUICKSTART — EasyCrypt proofs over MCP

You are an agent in a fresh session. This file gets you from zero
to doing EasyCrypt proofs through the `ecd mcp` server.

**You are a USER of these tools, not their developer.** The
EasyCrypt tooling in this worktree is maintained by a separate
workstream. Do not build, modify, or "fix" anything under
`/Users/gdel/Repos/ec-llm-next` (or its sibling worktrees). If the
stack seems broken or stale, report what you saw to the user and
stop — repairs are handled elsewhere. Your job is proving things
in the USER'S files.

## 1. Where things are

- Tooling home (read-only for you):
  `/Users/gdel/Repos/ec-llm-next` — pre-built `ec.native` and
  `ecd.native` live at its root.
- Your workspace: wherever the user's `.ec` files are — that is
  what you open, edit, and prove.

## 2. Are the tools available?

Check your tool list for tools named `open_file`, `goals`,
`exec`, `check_script` (server `easycrypt` / `ecd-mcp`). If they
are there, skip to step 4.

## 3. Registration (only if the tools are absent)

Run this **from the project directory you are working in** (e.g.
your proofs repo) — NOT from `ec-llm-next`. `claude mcp add`
registers to the current project's local scope by default, so
registering from the tooling repo makes the server invisible to
your actual session:

```bash
claude mcp add easycrypt \
  --env EC_LLM_BIN=/Users/gdel/Repos/ec-llm-next/ec.native \
  -- /Users/gdel/Repos/ec-llm-next/ecd.native mcp
```

(Add `--scope user` to make it available in every project instead
of just this one.)

MCP servers load at session start — after registering, **tell the
user to restart the session** so the tools appear. If registration
or the first `open_file` fails (missing binary, handshake error,
unknown command), report the exact error to the user and stop; do
not attempt to rebuild anything.

## 4. Read the operating manual

**Read
[/Users/gdel/Repos/ec-llm-next/doc/mcp-agent-guide.md](doc/mcp-agent-guide.md)
before driving the tools.** It is the contract: the mental model
(sessions, document-as-truth, uuid, `stale`, edit-mode locks), all
24 tools grouped by workflow, the standard playbooks (single
lemma, parallel dispatch, big-file refactoring), and the v1
limits.

The 30-second digest you must not violate:

- The `.ec` **file is the only truth**; session work is
  exploration until `replace_proof` (or your own verified splice)
  lands it.
- `mode=proof` + `lemmas=[...]` to work on proofs (parallelizes;
  claims are locks). `mode=statement` (default) to change
  declarations (exclusive per file).
- `stale: true` on any reply → `resync_file` before trusting or
  writing anything.
- Iterate with the state-neutral tools (`try_tactic`,
  `check_script`, `check_skeleton`); write once, verified. Probe
  with `try_tactic`, NEVER with `exec` — exec commits, and a
  committed probe poisons every later `check_script`. Read
  `check_script`'s `entry` field: it says which goal the
  candidate actually ran against.
- No cancellation yet: keep exploration cheap (`nosmt` prefixes,
  small candidates, `smt_timeout: 1` while probing).
- Repeating a long formula across calls? `define {name, text}`
  once, then `$name` everywhere — replies echo `src_expanded`.
- After a statement edit: plain `resync_file` = the fastest
  whole-file re-verification (`tail_executed` + `admitted` in one
  call, before any compile). Broken big file: `analyze_file
  {view: "triage"}` = first error per declaration.

## 5. Two-minute validation proof

Before touching the user's files, verify the stack end-to-end:

1. Write `/tmp/mcp-hello/hello.ec`:
   ```
   require import AllCore.
   lemma hello : 1 + 1 = 2.
   proof.
   admit.
   qed.
   ```
2. `open_file {path: "/tmp/mcp-hello/hello.ec", mode: "proof",
   lemmas: ["hello"], nosmt: true}` → expect `claims` carrying
   `hello`'s region.
3. `resync_file {upto_line: 3}` → positioned after `proof.`, one
   open goal `1 + 1 = 2`.
4. `check_script {script: "trivial.\nqed."}` → `ok: true`,
   `closes: true`, state restored.
5. `replace_proof {lemma: "hello", script:
   "proof.\ntrivial.\nqed."}` → `ok: true`, `file_written: true`.
6. Read the file — the `admit` is gone. That round trip is the
   whole system working.

Then proceed to the user's actual files with the same pattern. If
any step fails, report it verbatim and stop.

## 6. Proof-writing house rules

- Avoid the `progress` tactic (unstable across runs); prefer
  explicit alternatives.
- Never leave an `admit` in anything you hand back without
  flagging it loudly — and you cannot miss one: every executing
  reply carries an `admitted` array (the goal each admit
  discharged, captured before it ran, with a hash), and
  `admitted_goals {lemma?}` audits a whole file's admit debt in
  one call.
- When committing in the USER'S repos, follow that repo's
  conventions; **no AI co-author trailers** on commits.
- Respect the locks: a refusal naming another session is
  coordination, not an obstacle — close your own sessions when
  done (`close_session`), claim disjoint lemmas, route
  declaration changes through a statement-mode session.

## 7. Troubleshooting

| Symptom | Action |
|---|---|
| MCP tools absent | step 3 (from YOUR project dir, not the tooling repo), then ask the user to restart the session |
| `ecd: unknown command 'mcp'` | stale tooling binary — report to the user and stop; the tooling workstream rebuilds it |
| `open_file` fails to spawn / handshake error | report the error to the user; the tooling workstream fixes it — do not rebuild |
| every reply `stale: true` | the file changed on disk — `resync_file` |
| session confused / mid-proof wedge | `resync_file` (session ≡ file), or re-`open_file` the label |
| tool refused with another session named | lock system working — coordinate, don't work around it |
| a proof step hangs | a slow `smt()` with no cancel yet — wait it out, then keep candidates smaller / use `nosmt` prefixes |
