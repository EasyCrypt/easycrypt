# Golden Test Policy

How we author golden tests so they're meaningful, low-maintenance,
and resilient to incidental EC churn — without losing signal when
something real breaks.

## Context

EC and the daemon ship from the same commit (closed-loop monorepo
during PoC; merged binary post-PoC). There's no version-skew
between server and client to defend against. What remains as a real
concern is **environment determinism** — different machines,
different SMT solver versions, different OCaml stdlib hash
randomization, different locales — all of which can shift bytes
without anyone meaning to change behavior.

This policy keeps goldens informative when intentional changes happen
and resilient when environmental noise happens.

## Three tiers of golden assertion

### Tier 1 — Verbatim byte-strict (always)

Use for: **wire-shape goldens.** The format that should never
change without a `[proto:N]` bump.

Examples:
- LSP `Content-Length:` header line format.
- Reply header line format (`OK [uuid:N]`, `ERROR [uuid:N]`).
- Frame tokens (`<END>`, `<BEGIN>`, `<DONE>`, `<PARSE-BEGIN>`,
  `<PARSE-DONE>`, `<ANALYZE-BEGIN>`, `<ANALYZE-DONE>`).
- JSON envelope key names (`OK-JSON:`, `ERROR-JSON:`, top-level
  `sentences`, `diagnostics` keys).
- Tag line formats (`[restarted]`, `[loaded:foo:N]`, `[uuid:N]`,
  `[proto:N]`).

If a Tier-1 golden fails, it's a wire-shape change — investigate
seriously, possibly bump protocol version. **Failure is the alarm
we want.**

### Tier 2 — Structural (default for most goldens)

Use for: **JSON envelope content.** Parse the JSON, assert keys are
present and have the expected types / classifications, ignore
pretty-printed text bodies.

Examples:
- ANALYZE-JSON: assert `sentences` is a non-empty array; each
  sentence has `class`, `kind`, `start_offset`, `end_offset`;
  diagnostics array contains a `TypeError`-coded entry at the
  expected `sentence_index`. **Don't assert on `detail` text.**
- GOALS-JSON: assert `active`, `subgoal_count`, `subgoals` array
  with the expected number of hypotheses per kind; **don't assert
  on `pp` strings**.
- ERROR-JSON: assert `code` and `phase` fields; `detail` ignored.
- EXEC-JSON OK-JSON: assert `kind`, `command_kind`, `command_name`;
  payload-specific structural checks per command.

If a Tier-2 golden fails, the JSON structure changed — usually a
real change. Pretty-printer drift doesn't trip Tier-2 goldens.

### Tier 3 — Substring (where pp-text matters)

Use for: **pretty-printed strings where presence of specific
content matters but exact form doesn't.**

Examples:
- "Hover response contains the lemma's name" → substring match on
  the qualified name.
- "Error detail mentions the failing identifier" → substring match
  on the identifier.
- "Goals output contains the expected hypothesis kind label" →
  substring match.

If a Tier-3 golden fails, the substring isn't there — usually
indicates a meaningful change in what's being communicated.

## Excluded — never write a golden against this

- **`EcPrinting.pp_form` output verbatim.** Pretty-printer can
  evolve (parenthesization, infix preferences, notation
  conventions). Substring or structural only.
- **SMT solver responses verbatim.** Different solver versions
  produce different model-text or different proof-search timing
  output. Don't byte-compare.
- **Stack traces / OCaml exception text.** Compiler / stdlib
  changes shift these.
- **Timestamps, UUIDs, random IDs, file paths in user environment.**
  Replace with placeholders before comparison.

## Dev workflow on intentional change

When code changes intentionally, goldens may need to update:

1. Run `dune test` (or `dune build @runtest`).
2. If a golden fails:
   - Examine the diff.
   - If the change is intentional: regenerate the golden and commit
     in the same PR as the code change. Same diff shows code +
     golden together; reviewer evaluates both.
   - If the change is unexpected: that's a regression. Fix the
     code, don't regenerate the golden.
3. **Commit-message tag**: when regenerating goldens intentionally,
   add `[goldens-regenerated]` somewhere in the commit message. This
   makes it scannable in `git log` for "what golden updates have we
   done."

For dune-managed goldens, the `dune promote` flow auto-updates from
`*.expected` → in-tree golden. Use it. Always review the diff
before promoting.

## Conformance vs smoke

- **Smoke tests** (under `tooling/smoke/`): standalone executables /
  test stanzas. Most goldens live here.
- **Conformance tests** (future, under `tooling/conformance/`):
  scripted LSP/MCP clients driving the daemon over the wire.
  Established in Stage 1 of the VSCode-first plan; populated as
  Phase 5/6 surfaces ship.

Both follow this golden policy. Tier-1 / Tier-2 / Tier-3 split
applies uniformly.

## Pretty-printer changes — how they show up

A meaningful policy stress-test: what happens when EC's
pretty-printer changes?

- **Tier-1 goldens**: unaffected (don't include pp output).
- **Tier-2 goldens**: unaffected if assertions are on JSON keys/types
  (don't include pp text). Affected if some Tier-2 golden was
  authored against pp text incorrectly — fix to remove pp
  dependency.
- **Tier-3 goldens**: may break if substring is brittle (e.g.,
  asserts on whitespace inside pp output). Fix substring
  assertion to be tolerant.

This is the right behavior: pretty-printer changes flow through
substring assertions where they matter (substring match might need
update); structural goldens stay green.

## What about the diff oracle?

`run_diff_oracle` compares (sid, GOALS-JSON) pairs cold-load vs
revert-then-re-feed. Currently asserts byte-identical pairs. This is
**Tier-1-equivalent for the determinism property** (cold and revert
should produce the same bytes given the same EC) — not Tier-2
structural.

This is intentional and load-bearing: the diff oracle is testing
that EC's behavior is deterministic across paths, not testing for
any particular content. Byte-strict comparison is the right tool;
deterministic behavior is the property under test.

If the diff oracle starts producing spurious mismatches due to
non-determinism in EC (hash randomization, etc.), the fix is to
de-randomize or normalize, not to loosen the comparison.

## Re-validation and acceptance

Apply this policy to existing goldens in stages:

1. **Pre-Phase-5-core**: audit existing smokes (`tooling/smoke/`).
   For each golden, classify Tier 1/2/3. Loosen any verbatim-pp
   comparisons to structural or substring.
2. **During Phase 5-core**: new goldens authored to this policy
   from the start.
3. **Conformance suite**: established under this policy from day
   one.

## Net effect

- Routine smokes are version-tolerant — pretty-printer drift,
  solver-version drift don't break them.
- Wire-shape stability is enforced via Tier-1 byte-strict goldens —
  changes need explicit attention.
- Real behavioral changes surface as Tier-2 or Tier-3 mismatches
  that point at the actual change.
- Dev workflow stays smooth: regenerate-on-mismatch with explicit
  review in same PR.
