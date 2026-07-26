// EC-source syntax highlighter via vscode-textmate + vscode-oniguruma.
//
// Architecture (per design discussion / B.2 of program-printing v0):
// extension-side tokenize using the EXISTING easycrypt.tmLanguage.json
// grammar. Webview receives pre-classified `<span class="ts-...">` HTML
// — no JS / WASM in the webview. WASM loaded ONCE per extension
// activation; tokenize is fast (~ms) per render.
//
// Future swap path: replace the [tokenize] body with a Treesitter
// walk (or LSP semantic-tokens fetch) — same `tokenize(source) →
// TokenLine[]` interface, no caller changes.

import * as path from 'path';
import * as fs from 'fs';
import * as vscode from 'vscode';
import * as oniguruma from 'vscode-oniguruma';
import * as textmate from 'vscode-textmate';

export interface Token {
  startCol: number;          // 0-based, into the source line
  endCol:   number;
  text:     string;
  cssClass: string;          // already-mapped class for HTML output
}

export interface TokenLine {
  tokens: Token[];
}

let registry: textmate.Registry | undefined;
let grammarCache: textmate.IGrammar | undefined;
let onigurumaInitialized = false;

// Map TM scope (innermost first, but we read outermost → most-specific)
// to a CSS class. Uses a small set of well-known scopes; falls back to
// no class (renders as default text color) when scope is unknown.
//
// CSS classes are defined in the webview style block (added in
// extension.ts's render styles). Each class binds to a VSCode token
// color CSS variable so coloring follows the active editor theme.
function scopeToClass(scopes: string[]): string | undefined {
  // Walk from MOST-SPECIFIC (last in array) to LEAST-SPECIFIC. Take
  // the first match.
  for (let i = scopes.length - 1; i >= 0; i--) {
    const s = scopes[i];
    if (s.startsWith('keyword.control'))      return 'ts-kw-control';
    if (s.startsWith('keyword.operator'))     return 'ts-kw-operator';
    if (s.startsWith('keyword'))              return 'ts-kw';
    if (s.startsWith('storage.type'))         return 'ts-type';
    if (s.startsWith('storage'))              return 'ts-storage';
    if (s.startsWith('entity.name.function')) return 'ts-fn-name';
    if (s.startsWith('entity.name.type'))     return 'ts-type-name';
    if (s.startsWith('entity.name'))          return 'ts-name';
    if (s.startsWith('variable'))             return 'ts-var';
    if (s.startsWith('constant.numeric'))     return 'ts-num';
    if (s.startsWith('constant.language'))    return 'ts-const';
    if (s.startsWith('constant'))             return 'ts-const';
    if (s.startsWith('string'))               return 'ts-string';
    if (s.startsWith('comment'))              return 'ts-comment';
    if (s.startsWith('punctuation'))          return 'ts-punct';
    if (s.startsWith('support.function'))     return 'ts-fn-name';
    if (s.startsWith('support.type'))         return 'ts-type-name';
  }
  return undefined;
}

// One-time initialization. Loads the WASM regex engine + the easycrypt
// TM grammar. Returns a Promise that's the same for every call after
// the first (cached). Must be awaited before tokenize().
async function ensureRegistry(extensionPath: string): Promise<textmate.Registry> {
  if (registry) return registry;
  if (!onigurumaInitialized) {
    const wasmPath = path.join(
      extensionPath, 'node_modules', 'vscode-oniguruma', 'release', 'onig.wasm',
    );
    const wasm = fs.readFileSync(wasmPath);
    await oniguruma.loadWASM(wasm.buffer);
    onigurumaInitialized = true;
  }
  registry = new textmate.Registry({
    onigLib: Promise.resolve({
      createOnigScanner: (patterns: string[]) => new oniguruma.OnigScanner(patterns),
      createOnigString: (s: string) => new oniguruma.OnigString(s),
    }),
    loadGrammar: async (scopeName: string) => {
      if (scopeName !== 'source.easycrypt') return null;
      const grammarPath = path.join(
        extensionPath, 'syntaxes', 'easycrypt.tmLanguage.json',
      );
      const raw = fs.readFileSync(grammarPath, 'utf-8');
      return textmate.parseRawGrammar(raw, grammarPath);
    },
  });
  return registry;
}

async function ensureGrammar(extensionPath: string): Promise<textmate.IGrammar | null> {
  if (grammarCache) return grammarCache;
  const reg = await ensureRegistry(extensionPath);
  const g = await reg.loadGrammar('source.easycrypt');
  if (g) grammarCache = g;
  return g;
}

let warmupStarted = false;

// Kick off async load on extension activation so tokenize() at first
// render doesn't block. Safe to call multiple times.
export function warmup(extensionPath: string): void {
  if (warmupStarted) return;
  warmupStarted = true;
  void ensureGrammar(extensionPath).catch((err) => {
    console.error('EasyCrypt: tokenizer warmup failed:', err);
  });
}

// Multi-character operator sequences the EC TM grammar splits into
// multiple tokens (e.g., `<$` arrives as separate `<` + `$` tokens).
// The post-tokenize merger walks adjacent tokens, joins those whose
// concatenated text matches a known sequence, and rewrites them as
// a single token (carrying the FIRST token's css class). This lets
// the prettify table catch them via single-token lookup.
const MULTI_CHAR_SEQUENCES: string[] = [
  '<$',     // EC random-sample assignment
  '<-',     // assignment / arrow contexts
  '<@',     // procedure-call assignment
  '<<-',    // (variants — defensive)
  '~=',
];

function mergeAdjacentSequences(tokens: Token[]): Token[] {
  const out: Token[] = [];
  let i = 0;
  while (i < tokens.length) {
    let merged = false;
    // Try longest first — match against MULTI_CHAR_SEQUENCES in
    // descending length order so e.g. `<<-` wins over `<-`.
    const candidates = MULTI_CHAR_SEQUENCES
      .filter((s) => s.length >= 2)
      .sort((a, b) => b.length - a.length);
    for (const seq of candidates) {
      // Walk forward consuming tokens whose accumulated text
      // matches the sequence prefix.
      let acc = '';
      let j = i;
      while (j < tokens.length && acc.length < seq.length) {
        // Skip empty tokens defensively (shouldn't happen).
        if (tokens[j].text === '') { j++; continue; }
        acc += tokens[j].text;
        j++;
        if (acc === seq) break;
        if (!seq.startsWith(acc)) break;
      }
      if (acc === seq) {
        out.push({
          startCol: tokens[i].startCol,
          endCol:   tokens[j - 1].endCol,
          text:     seq,
          // Use the FIRST token's css class as the merged class —
          // arbitrary but deterministic. Tokenized text becomes the
          // merged sequence; prettify table catches `<$` etc.
          cssClass: tokens[i].cssClass,
        });
        i = j;
        merged = true;
        break;
      }
    }
    if (!merged) {
      out.push(tokens[i]);
      i++;
    }
  }
  return out;
}

// Tokenize an EC source string. Returns one TokenLine per line of input.
// Falls back to a single un-classified token per line if the grammar
// isn't loaded yet (defensive — shouldn't happen post-warmup).
export async function tokenize(
  extensionPath: string, source: string,
): Promise<TokenLine[]> {
  const grammar = await ensureGrammar(extensionPath);
  const lines = source.split('\n');
  if (!grammar) {
    // Grammar load failed — return un-classified single-token lines.
    return lines.map((l) => ({
      tokens: [{ startCol: 0, endCol: l.length, text: l, cssClass: '' }],
    }));
  }
  let ruleStack = textmate.INITIAL;
  const out: TokenLine[] = [];
  for (const line of lines) {
    const r = grammar.tokenizeLine(line, ruleStack);
    const rawTokens: Token[] = r.tokens.map((t) => ({
      startCol: t.startIndex,
      endCol:   t.endIndex,
      text:     line.substring(t.startIndex, t.endIndex),
      cssClass: scopeToClass(t.scopes) ?? '',
    }));
    out.push({ tokens: mergeAdjacentSequences(rawTokens) });
    ruleStack = r.ruleStack;
  }
  return out;
}

// Prettification table — applied to token text after tokenization,
// before HTML emission. Entries are exact-text replacements per token.
// Multi-character operators are tokenized as single units by the TM
// grammar (e.g. `=>` is one token), so single-token replacement
// handles them.
const PRETTIFY_BUILTINS: Record<string, string> = {
  'forall': '∀',
  'exists': '∃',
  '=>':     '⇒',
  '<=>':    '⇔',
  '<=':     '≤',
  '>=':     '≥',
  '<>':     '≠',
  '/\\':    '∧',
  '\\/':    '∨',
  '&&':     '∧',
  '||':     '∨',
  '~':      '¬',
  // Probability + program-logic glyphs (UPSTREAM #23 follow-up):
  'Pr':     'ℙ',
  'true':   '⊤',
  'false':  '⊥',
  'fun':    'λ',
  '<$':     '←$',
};

// Look up a token's prettified display. User-configurable additions
// from `easycrypt-tooling.display.prettify.replacements` merge with
// the builtins (user overrides win on collision). Read fresh from
// the config each time — cheap, settings change applies immediately.
// Fully token-shaped (TM emits `=>` as one token; user overrides must
// also match a single TM token to take effect).
function prettifyToken(text: string): string {
  const userTable = vscode.workspace
    .getConfiguration('easycrypt-tooling.display.prettify')
    .get<Record<string, string>>('replacements', {});
  if (userTable[text] !== undefined) return userTable[text];
  return PRETTIFY_BUILTINS[text] ?? text;
}

// Exposed for the extension's non-tokenizer-path prettify call site
// (formula leaves outside program contexts), so they share the table.
export function prettifyTokenInline(text: string): string {
  return prettifyToken(text);
}

// HTML-escape (duplicated from extension.ts — keeps tokenizer module
// self-contained). Same impl.
function escapeHtml(s: string): string {
  return s
    .replace(/&/g, '&amp;')
    .replace(/</g, '&lt;')
    .replace(/>/g, '&gt;')
    .replace(/"/g, '&quot;')
    .replace(/'/g, '&#39;');
}

// Render token lines as a single HTML string. Each token wrapped in
// `<span class="ts-...">`; lines joined by `\n` (caller's `<pre>` /
// `white-space: pre-wrap` preserves them). Prettification optional.
export function tokensToHtml(
  lines: TokenLine[], opts: { prettify: boolean },
): string {
  return lines
    .map((line) =>
      line.tokens
        .map((t) => {
          const display = opts.prettify ? prettifyToken(t.text) : t.text;
          if (t.cssClass === '') return escapeHtml(display);
          return `<span class="${t.cssClass}">${escapeHtml(display)}</span>`;
        })
        .join(''),
    )
    .join('\n');
}

// One-shot helper: tokenize + render with current settings. Returns a
// promise that resolves to the highlighted HTML.
export async function highlightSource(
  extensionPath: string, source: string,
): Promise<string> {
  const lines = await tokenize(extensionPath, source);
  const prettify = vscode.workspace
    .getConfiguration('easycrypt-tooling.display')
    .get<boolean>('prettify', true);
  return tokensToHtml(lines, { prettify });
}

// Variant that returns per-line HTML strings (one entry per source
// line). Caller composes into a table / grid for line-numbered
// rendering. Same prettify + token-class behavior as highlightSource.
export async function highlightSourceLines(
  extensionPath: string, source: string,
): Promise<string[]> {
  const lines = await tokenize(extensionPath, source);
  const prettify = vscode.workspace
    .getConfiguration('easycrypt-tooling.display')
    .get<boolean>('prettify', true);
  return lines.map((line) =>
    line.tokens
      .map((t) => {
        const display = prettify ? prettifyToken(t.text) : t.text;
        if (t.cssClass === '') return escapeHtml(display);
        return `<span class="${t.cssClass}">${escapeHtml(display)}</span>`;
      })
      .join(''),
  );
}

// Synchronous fallback: returns un-classified HTML (just escaped text)
// when called BEFORE the grammar is loaded. Renderers that can't await
// (deep in a sync render path) use this as the immediate output and
// schedule an async re-render once the grammar is ready.
export function highlightSourceFallback(
  source: string, opts: { prettify: boolean },
): string {
  // Pre-tokenize trivially: split on whitespace boundaries, keep text
  // verbatim. No coloring, but prettify still applies on whole-token
  // matches.
  return source
    .split(/(\s+)/)
    .map((chunk) => {
      if (/^\s+$/.test(chunk)) return chunk;
      const display = opts.prettify ? prettifyToken(chunk) : chunk;
      return escapeHtml(display);
    })
    .join('');
}
