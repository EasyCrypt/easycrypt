// Self-contained tests for the codepos / tactic-source helpers.
// Runnable via `node out/codepos.test.js` after `npm run compile`.
// No vscode imports — exits 0 on pass, 1 on failure.

import {
  Codepos,
  ecBrSelSource,
  ecCodeposRangeSource,
  ecCodeposSource,
  ecCpos1Source,
  ecSideSuffix,
  procChangeSource,
  procRewriteSource,
  classifyChangeProbe,
  emptyRewriteSlots,
  rewriteAssembleArg,
  rewriteOccurrenceFromInput,
  rewriteMatchFromInput,
  rewriteSlotsSummary,
} from './codepos';

let failures = 0;
function assert(name: string, cond: boolean, detail?: string): void {
  if (cond) {
    console.log(`  ok  ${name}`);
  } else {
    failures++;
    console.error(`  FAIL ${name}${detail ? ' — ' + detail : ''}`);
  }
}
function eq<T>(name: string, got: T, want: T): void {
  assert(name, got === want, `got=${JSON.stringify(got)} want=${JSON.stringify(want)}`);
}

console.log('== codepos / tactic-source synthesizer tests ==');

// --- ecSideSuffix
eq('side left  -> {1}', ecSideSuffix('left'),  '{1}');
eq('side right -> {2}', ecSideSuffix('right'), '{2}');
eq('side none  -> ""',  ecSideSuffix('none'),  '');

// --- ecCpos1Source / ecBrSelSource
eq('cpos1 1   -> "1"',     ecCpos1Source(1), '1');
eq('cpos1 42  -> "42"',    ecCpos1Source(42), '42');
eq('brsel cond true  -> "."',     ecBrSelSource({ kind: 'cond', value: true }),  '.');
eq('brsel cond false -> "?"',     ecBrSelSource({ kind: 'cond', value: false }), '?');
eq('brsel match Some -> "#Some."', ecBrSelSource({ kind: 'match', ctor: 'Some' }), '#Some.');
eq('brsel match-by-pos 1 -> "#1."', ecBrSelSource({ kind: 'match-by-pos', idx: 1 }), '#1.');
eq('brsel match-by-pos 3 -> "#3."', ecBrSelSource({ kind: 'match-by-pos', idx: 3 }), '#3.');

// --- ecCodeposSource
eq(
  'codepos top-level: {path:[], cpos1:3} -> "3"',
  ecCodeposSource({ path: [], cpos1: 3 }),
  '3',
);
eq(
  'codepos one-step then: 2 . 1 -> "2 . 1"',
  ecCodeposSource({
    path: [{ cpos1: 2, brsel: { kind: 'cond', value: true } }],
    cpos1: 1,
  }),
  '2 . 1',
);
eq(
  'codepos one-step else: 5 ? 2 -> "5 ? 2"',
  ecCodeposSource({
    path: [{ cpos1: 5, brsel: { kind: 'cond', value: false } }],
    cpos1: 2,
  }),
  '5 ? 2',
);
eq(
  'codepos two-step nested: 2 . 1 ? 3',
  ecCodeposSource({
    path: [
      { cpos1: 2, brsel: { kind: 'cond', value: true } },
      { cpos1: 1, brsel: { kind: 'cond', value: false } },
    ],
    cpos1: 3,
  }),
  '2 . 1 ? 3',
);
eq(
  'codepos match: 4 #Some. 1',
  ecCodeposSource({
    path: [{ cpos1: 4, brsel: { kind: 'match', ctor: 'Some' } }],
    cpos1: 1,
  }),
  '4 #Some. 1',
);

// --- ecCodeposRangeSource
eq(
  'range no-path: cps=1 cpe=3 -> "[1 .. 3]"',
  ecCodeposRangeSource({ path: [], cpos1: 1 }, 3),
  '[1 .. 3]',
);
eq(
  'range w/ path: 2 . : [1 .. 3]',
  ecCodeposRangeSource({
    path: [{ cpos1: 2, brsel: { kind: 'cond', value: true } }],
    cpos1: 1,
  }, 3),
  '2 . : [1 .. 3]',
);
eq(
  'range single-line via same start/end: [2 .. 2]',
  ecCodeposRangeSource({ path: [], cpos1: 2 }, 2),
  '[2 .. 2]',
);

// --- procRewriteSource
eq(
  'proc rewrite no-side w/ pterm',
  procRewriteSource('none', { path: [], cpos1: 3 }, 'lemma_foo'),
  'proc rewrite 3 lemma_foo.',
);
eq(
  'proc rewrite left side w/ pterm',
  procRewriteSource('left', { path: [], cpos1: 3 }, 'lemma_foo'),
  'proc rewrite{1} 3 lemma_foo.',
);
eq(
  'proc rewrite right side w/ pterm',
  procRewriteSource('right', { path: [], cpos1: 3 }, 'lemma_foo'),
  'proc rewrite{2} 3 lemma_foo.',
);
eq(
  'proc rewrite empty pterm => /= simplify',
  procRewriteSource('none', { path: [], cpos1: 3 }, ''),
  'proc rewrite 3 /=.',
);
eq(
  'proc rewrite nested codepos',
  procRewriteSource('left',
    { path: [{ cpos1: 2, brsel: { kind: 'cond', value: true } }], cpos1: 1 },
    'lemma_bar'),
  'proc rewrite{1} 2 . 1 lemma_bar.',
);
eq(
  'proc rewrite parenthesized pterm',
  procRewriteSource('none', { path: [], cpos1: 4 }, '(lemma a b)'),
  'proc rewrite 4 (lemma a b).',
);

// --- procChangeSource
eq(
  'proc change single-line no-bindings',
  procChangeSource('none', { path: [], cpos1: 2 }, 2, [], ['x <- 0']),
  'proc change [2 .. 2] : { x <- 0; }.',
);
eq(
  'proc change range no-bindings',
  procChangeSource('left', { path: [], cpos1: 1 }, 3, [],
    ['x <- 0', 'y <- 1', 'z <- x + y']),
  'proc change{1} [1 .. 3] : { x <- 0; y <- 1; z <- x + y; }.',
);
eq(
  'proc change w/ single var binding',
  procChangeSource('none', { path: [], cpos1: 2 }, 4,
    [{ names: ['x'], ty: 'int' }],
    ['x <- 0', 'r := r + x']),
  'proc change [2 .. 4] : [(x: int)] { x <- 0; r := r + x; }.',
);
eq(
  'proc change w/ multi-name binding (shared type, names space-sep)',
  procChangeSource('none', { path: [], cpos1: 1 }, 2,
    [{ names: ['x', 'y'], ty: 'int' }],
    ['x <- 0', 'y <- 1']),
  'proc change [1 .. 2] : [(x y: int)] { x <- 0; y <- 1; }.',
);
eq(
  'proc change w/ multiple bindings (comma-sep groups in parens)',
  procChangeSource('right', { path: [], cpos1: 1 }, 2,
    [{ names: ['x'], ty: 'int' }, { names: ['b'], ty: 'bool' }],
    ['x <- 0']),
  'proc change{2} [1 .. 2] : [(x: int, b: bool)] { x <- 0; }.',
);
eq(
  'proc change inside nested then-branch',
  procChangeSource('left',
    { path: [{ cpos1: 2, brsel: { kind: 'cond', value: true } }], cpos1: 1 },
    3, [], ['skip']),
  'proc change{1} 2 . : [1 .. 3] : { skip; }.',
);
eq(
  'proc change drops empty stmts',
  procChangeSource('none', { path: [], cpos1: 1 }, 2, [],
    ['x <- 0', '', '  ', 'y <- 1']),
  'proc change [1 .. 2] : { x <- 0; y <- 1; }.',
);
eq(
  'proc change preserves trailing ; if user added one',
  procChangeSource('none', { path: [], cpos1: 1 }, 2, [],
    ['x <- 0;', 'y <- 1;']),
  'proc change [1 .. 2] : { x <- 0; y <- 1; }.',
);

// --- classifyChangeProbe
eq('classify ok',
  classifyChangeProbe('ok', undefined), 'ok');
eq('classify parse err (substring "parse error")',
  classifyChangeProbe('err', 'parse error: unexpected token'), 'parse-err');
eq('classify parse err (substring "syntax error")',
  classifyChangeProbe('err', 'syntax error at line 1'), 'parse-err');
eq('classify scope err (substring "unknown")',
  classifyChangeProbe('err', 'unknown identifier: foo'), 'scope-err');
eq('classify scope err (substring "unbound")',
  classifyChangeProbe('err', 'unbound name x'), 'scope-err');
eq('classify scope err (substring "not in scope")',
  classifyChangeProbe('err', 'variable y is not in scope'), 'scope-err');
eq('classify sem-err (anything else)',
  classifyChangeProbe('err', 'cannot prove equivalence'), 'sem-err');
eq('classify sem-err (no err text)',
  classifyChangeProbe('err', undefined), 'sem-err');
eq('classify ok via outcome ignores err text',
  classifyChangeProbe('ok', 'should be ignored'), 'ok');

// --- Idempotence check: synthesize then re-check shape
{
  const cp: Codepos = {
    path: [
      { cpos1: 2, brsel: { kind: 'cond', value: true } },
      { cpos1: 5, brsel: { kind: 'match', ctor: 'Cons' } },
    ],
    cpos1: 7,
  };
  const got = ecCodeposSource(cp);
  eq('idempotent compound source', got, '2 . 5 #Cons. 7');
}

// --- rewrite-builder slot model
{
  const empty = emptyRewriteSlots();
  eq('empty slots assemble to ""', rewriteAssembleArg(empty), '');
  eq('empty slots summary', rewriteSlotsSummary(empty), '(empty)');

  eq('lemma only', rewriteAssembleArg({ ...empty, lemma: 'foo' }), 'foo');
  eq('reverse + lemma', rewriteAssembleArg({ ...empty, side: 'reverse', lemma: 'foo' }), '- foo');
  eq('repeat + lemma', rewriteAssembleArg({ ...empty, repeat: true, lemma: 'foo' }), '! foo');
  eq('reverse + repeat + lemma',
    rewriteAssembleArg({ ...empty, side: 'reverse', repeat: true, lemma: 'foo' }),
    '- ! foo');
  eq('occ + lemma',
    rewriteAssembleArg({ ...empty, occurrence: '{2}', lemma: 'foo' }),
    '{2} foo');
  eq('match + lemma',
    rewriteAssembleArg({ ...empty, match_: '[x in f x]', lemma: 'foo' }),
    '[x in f x] foo');
  eq('all slots populated (grammar order)',
    rewriteAssembleArg({
      side: 'reverse', repeat: true,
      occurrence: '{2}', match_: '[x in f x]', lemma: 'foo',
    }),
    '- ! {2} [x in f x] foo');

  // occurrence formatter
  eq('occ "" -> empty',          rewriteOccurrenceFromInput(''),       '');
  eq('occ "+" -> empty (= all)', rewriteOccurrenceFromInput('+'),      '');
  eq('occ "1" -> {1}',           rewriteOccurrenceFromInput('1'),      '{1}');
  eq('occ "1 3" -> {1 3}',       rewriteOccurrenceFromInput('1 3'),    '{1 3}');
  eq('occ "  2   4  " trim',     rewriteOccurrenceFromInput('  2   4  '), '{2 4}');
  eq('occ "-1" -> {- 1}',        rewriteOccurrenceFromInput('-1'),     '{- 1}');
  eq('occ "-1 -3" -> {- 1 3}',   rewriteOccurrenceFromInput('-1 -3'),  '{- 1 3}');
  eq('occ mixed signs passthrough (parser rejects)',
    rewriteOccurrenceFromInput('1 -3'), '{1 -3}');

  // match formatter
  eq('match no binder',
    rewriteMatchFromInput('', 'f x y'), '[f x y]');
  eq('match with binder',
    rewriteMatchFromInput('x', 'f x y'), '[x in f x y]');
  eq('match empty pat -> empty',
    rewriteMatchFromInput('', ''), '');
  eq('match with binder but empty pat -> empty',
    rewriteMatchFromInput('x', ''), '');

  // summary nuances
  eq('summary lemma-only', rewriteSlotsSummary({ ...empty, lemma: 'foo' }), 'foo');
  eq('summary modifiers-only no lemma',
    rewriteSlotsSummary({ ...empty, side: 'reverse', occurrence: '{2}' }),
    '- {2}');
}

console.log(failures === 0 ? '\nALL PASS' : `\n${failures} FAILURES`);
process.exit(failures === 0 ? 0 : 1);
