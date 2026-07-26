// Pure helpers for codepos addressing + tactic-source synthesis.
// Lives in its own module so it can be unit-tested in isolation
// (vscode import would otherwise pull the whole VSCode runtime).
//
// Mirrors EC's EcMatching.Position.codepos types (see UPSTREAM § 20
// reproduction notes + src/ecMatching.mli for the OCaml side).
//   codepos = (path, cpos1)
//   path    = list of (cpos1, branch_select)
//   brsel   = `Cond of bool | `Match of symbol
//
// Webview side encodes Codepos via JSON.stringify into HTML
// data-codepos attributes; the goalsPanel onDidReceiveMessage
// handler decodes back into MsgCodepos and feeds these helpers.

export type CodeposBrSel =
  | { kind: 'cond'; value: boolean }
  // Match-arm by constructor name. EC syntax: `#<ctor>.`
  // Used when STMT-JSON's pattern_pp surfaces the constructor
  // (it currently doesn't — UPSTREAM #24 known gap; the walker
  // emits `match-by-pos` instead, see below).
  | { kind: 'match'; ctor: string }
  // Match-arm by branch index (origin/main extension to
  // EcMatching.codepos_brsel — the `MatchByPos of int` variant).
  // EC syntax: `#<i>.` (where i is the 1-based branch index).
  // Lets the walker address match arms without needing the
  // constructor name — closes the addressing gap above.
  | { kind: 'match-by-pos'; idx: number };

export interface CodeposPathStep {
  cpos1: number;
  brsel: CodeposBrSel;
}

export interface Codepos {
  path: CodeposPathStep[];
  cpos1: number;
}

export type ProgSide = 'left' | 'right' | 'none';

// `{1}` for left, `{2}` for right, '' for non-relational
// (hoare/phoare/ehoare).
export function ecSideSuffix(side: ProgSide): string {
  switch (side) {
    case 'left':  return '{1}';
    case 'right': return '{2}';
    case 'none':  return '';
  }
}

// Render a single codepos1 — bare integer (always emit ByPos N
// without offset; ByMatch / offsets are EC-hand-written-only forms
// not exposed by mouse selection).
export function ecCpos1Source(cpos1: number): string {
  return cpos1.toString();
}

// Render a path step's branch selector. EC syntax:
//   Cond true       → "."           (then-branch / while-body)
//   Cond false      → "?"           (else-branch)
//   Match ctor      → "#<ctor>."    (match arm by ctor name)
//   MatchByPos idx  → "#<idx>."     (match arm by 1-based branch index)
export function ecBrSelSource(brsel: CodeposBrSel): string {
  if (brsel.kind === 'cond') return brsel.value ? '.' : '?';
  if (brsel.kind === 'match') return '#' + brsel.ctor + '.';
  return '#' + brsel.idx.toString() + '.';
}

// Render the full codepos as EC source.
//   {path:[], cpos1:3}                                    → "3"
//   {path:[{cpos1:2, cond true}], cpos1:1}                → "2 . 1"
//   {path:[{2, cond true}, {1, cond false}], cpos1:3}     → "2 . 1 ? 3"
export function ecCodeposSource(cp: Codepos): string {
  const parts: string[] = [];
  for (const step of cp.path) {
    parts.push(ecCpos1Source(step.cpos1));
    parts.push(ecBrSelSource(step.brsel));
  }
  parts.push(ecCpos1Source(cp.cpos1));
  return parts.join(' ');
}

// Render a closed range from `cp.cpos1` to `cpos1End` sharing the
// same path. EC syntax:
//   no path:  `[cps .. cpe]`
//   with path:  `<path-steps> : [cps .. cpe]`  (COLON separates
//                                              path from range)
export function ecCodeposRangeSource(cp: Codepos, cpos1End: number): string {
  const start = cp.cpos1;
  const end = cpos1End;
  const range = `[${start} .. ${end}]`;
  if (cp.path.length === 0) return range;
  const pathParts: string[] = [];
  for (const step of cp.path) {
    pathParts.push(ecCpos1Source(step.cpos1));
    pathParts.push(ecBrSelSource(step.brsel));
  }
  return `${pathParts.join(' ')} : ${range}`;
}

// Synthesize `proc rewrite` source.
//   pterm: full pterm string the user typed (e.g., `lemma_foo` or
//          `(lemma_bar a b)`); EMPTY string => emit `/=` simplify.
export function procRewriteSource(
  side: ProgSide, cp: Codepos, pterm: string,
): string {
  const sideStr = ecSideSuffix(side);
  const sideSep = sideStr === '' ? '' : ' ';
  const cpStr = ecCodeposSource(cp);
  const trimmed = pterm.trim();
  if (trimmed === '') {
    return `proc rewrite${sideStr}${sideSep === '' ? ' ' : sideSep}${cpStr} /=.`;
  }
  return `proc rewrite${sideStr}${sideSep === '' ? ' ' : sideSep}${cpStr} ${trimmed}.`;
}

// One var binding row in proc change.
//   names: comma-separated list of identifiers sharing the same type.
//   ty:    EC type expression as a string (e.g., "int", "bool", "real").
export interface ProcChangeBinding {
  names: string[];
  ty: string;
}

// Synthesize `proc change` source.
//
// Grammar (per src/ecParser.mly:3269):
//   PROC CHANGE side? <pos_or_range> COLON [bindings]? brace(stmt)
//
// SINGLE colon between position and bindings/stmts — bindings are
// optional and slot in BEFORE the brace block, no second colon
// after them. Examples accepted by EC:
//   proc change [1 .. 2] : { x <- 0; }.
//   proc change [1 .. 2] : [t: int] { t <- 0; x <- t + 1; }.
//   proc change{1} 2 . : [a, b: int] { a <- 0; b <- 1; }.
//
// Args:
//   range:    cpos1End may equal cp.cpos1 (single-line) or differ
//             (multi-line range). Both cases use the bracketed range
//             form `[cps .. cpe]`.
//   bindings: list of ProcChangeBinding; rendered as
//             `[x: int, y, z: bool]`. Empty list => no bindings.
//   stmts:    replacement instructions (one per element). Trailing `;`
//             is added if not present; empty entries dropped.
export function procChangeSource(
  side: ProgSide,
  cp: Codepos, cpos1End: number,
  bindings: ProcChangeBinding[],
  stmts: string[],
): string {
  const sideStr = ecSideSuffix(side);
  const sideSep = sideStr === '' ? '' : ' ';
  const rangeStr = ecCodeposRangeSource(cp, cpos1End);
  // Bindings encoding (per src/ecParser.mly's ptybinding1 grammar):
  //   pty_varty:  bdident+ COLON type_exp     (names SPACE-separated)
  //   ptybinding1: LPAREN plist1(pty_varty, COMMA) RPAREN
  //
  // To support multiple shared-type groups uniformly, ALWAYS wrap
  // in parens — even a single binding renders as `[(x y: int)]`.
  // (EC accepts the bare `[x: int]` form too, but mixing un-parened
  // with comma'd groups requires the paren form anyway, so we just
  // emit it consistently.)
  //
  // UI passes names as already-split string lists (the popup's
  // "var-names" input is comma-separated for UX, but split on
  // input). We join with SPACES here per the pty_varty grammar.
  const bindStr = bindings.length === 0
    ? ''
    : '[(' + bindings.map(b => b.names.join(' ') + ': ' + b.ty).join(', ') + ')] ';
  const stmtStr = stmts
    .map(s => s.trim())
    .filter(s => s !== '')
    .map(s => s.endsWith(';') ? s : s + ';')
    .join(' ');
  return `proc change${sideStr}${sideSep === '' ? ' ' : sideSep}${rangeStr} : ${bindStr}{ ${stmtStr} }.`;
}

// ---- rewrite-builder slot model ------------------------------------
//
// One `rwarg1` (per src/ecParser.mly:2420) is:
//
//   side · repeat · occurrence · match · lemma
//
// where:
//   side       : '-' (reverse) or empty (forward)
//   repeat     : '!' (all-occurrences-fixpoint) or empty
//   occurrence : '{i j ...}' (inclusive) | '{- i j ...}' (exclusive) |
//                '{+}' (all explicit) | empty
//   match      : '[<pat>]' | '[<x> in <pat>]' | empty
//   lemma      : pterm (typically a qname; can be a parenthesized
//                application, e.g. '(eq_sym L)'; '_' wildcards
//                handled at the apply-builder layer, not here)
//
// The rewrite builder maintains a single in-flight `RewriteSlots`
// state; each slot is independently editable via title-bar buttons
// or sentinels. On commit, [rewriteAssembleArg] joins the populated
// slots in grammar order to produce one `rwarg1` token. Multiple
// such tokens chain space-separated as `rewrite t1 t2 … tN.` —
// matches the existing cumulative-builder pattern.

export interface RewriteSlots {
  // Side: 'forward' (default, no '-') or 'reverse' ('-').
  side: 'forward' | 'reverse';
  // Repeat ('!'): apply the rewrite as many times as possible.
  // EC accepts repeat counts (e.g., '3!'), but v1 surfaces only
  // the bare on/off toggle; repeat-count is left as a future
  // extension if the user requests it.
  repeat: boolean;
  // Occurrence selector. Already wrapped in '{ ... }' if non-empty.
  // Empty string means no occurrence filter (default = all).
  occurrence: string;
  // Match pattern. Already wrapped in '[ ... ]' if non-empty.
  // Empty string means no pattern filter.
  match_: string;
  // Lemma (or pterm). Empty string means slot not yet populated.
  lemma: string;
}

export const emptyRewriteSlots = (): RewriteSlots => ({
  side: 'forward',
  repeat: false,
  occurrence: '',
  match_: '',
  lemma: '',
});

// Assemble the in-flight slots into a single `rwarg1` token. Slots
// in declaration order from the parser; empty slots dropped. Joined
// with spaces. Lemma may be empty (caller decides whether to call
// this with an unfinished arg — useful for live preview that shows
// modifiers even before a lemma is picked, though such a token
// wouldn't be a valid `rwarg1` on its own).
export function rewriteAssembleArg(s: RewriteSlots): string {
  const parts: string[] = [];
  if (s.side === 'reverse') parts.push('-');
  if (s.repeat) parts.push('!');
  if (s.occurrence !== '') parts.push(s.occurrence);
  if (s.match_ !== '')     parts.push(s.match_);
  if (s.lemma !== '')      parts.push(s.lemma);
  return parts.join(' ');
}

// Format an occurrence-spec string from the user's space-separated
// indices. The InputBox prompt convention:
//   "1 3"     → "{1 3}"            (inclusive)
//   "-1 -3"   → "{- 1 3}"          (exclusive)
//   "" / "+"  → ""                 (default = all; clear the slot)
// Mixed signs (e.g., "1 -3") are rejected by EC's parser; the
// helper passes them through and lets the parser surface the err.
export function rewriteOccurrenceFromInput(input: string): string {
  const trimmed = input.trim();
  if (trimmed === '' || trimmed === '+') return '';
  // All-negative → exclusive form. Strip the '-'s.
  const tokens = trimmed.split(/\s+/);
  const allNegative = tokens.every(t => /^-\d+$/.test(t));
  if (allNegative) {
    const nums = tokens.map(t => t.slice(1));
    return '{- ' + nums.join(' ') + '}';
  }
  return '{' + tokens.join(' ') + '}';
}

// Format a match-spec string from raw pattern + optional binder.
//   binder = ''           → "[<pat>]"
//   binder = 'x'          → "[x in <pat>]"
//   pat = '' (any binder) → ""  (clear the slot)
export function rewriteMatchFromInput(binder: string, pat: string): string {
  const p = pat.trim();
  if (p === '') return '';
  const b = binder.trim();
  if (b === '') return '[' + p + ']';
  return '[' + b + ' in ' + p + ']';
}

// Status-row summary of the in-flight arg, for display in the
// InputBox prompt above the typing field. Compact, grammar-order.
//   "(empty)"            — no slots populated
//   "-! {2} [x in f x] L" — fully populated
export function rewriteSlotsSummary(s: RewriteSlots): string {
  const t = rewriteAssembleArg(s);
  return t === '' ? '(empty)' : t;
}

// Coarse classification of a tryTactic err string for the proc
// change popup's validity badge.
//   parse-err: tokenizer / parser refused
//   scope-err: identifier lookup failed (unbound / unknown)
//   sem-err:   well-formed but tactic refused (e.g., behavioral
//              mismatch from the equivalence subgoal)
//   ok:        outcome === 'ok' from tryTactic
// Substring match — EC error strings vary; refine as we see real
// outputs.
export type ChangeProbeStatus = 'parse-err' | 'scope-err' | 'sem-err' | 'ok';
export function classifyChangeProbe(
  outcome: 'ok' | 'err' | undefined, errText: string | undefined,
): ChangeProbeStatus {
  if (outcome === 'ok') return 'ok';
  const e = (errText ?? '').toLowerCase();
  if (e.includes('parse error') || e.includes('parsing error') ||
      e.includes('syntax error')) return 'parse-err';
  if (e.includes('unknown') || e.includes('unbound') ||
      e.includes('not in scope') || e.includes('cannot find')) return 'scope-err';
  return 'sem-err';
}
