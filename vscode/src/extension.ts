// EasyCrypt tooling daemon — VSCode client (Slice C).
//
// Spawns `ecd daemon --stdio` and connects via vscode-languageclient.
// Standard LSP flow gives us textDocumentSync + publishDiagnostics for
// free; custom commands wrap the daemon's `easycrypt/proof/*` methods.
//
// - Slice B: locked-region decoration driven by stateChanged.
// - Slice C: dedicated goal-pane WebviewPanel — replaces the prior
//   Output-channel JSON dump. Refreshes reactively on stateChanged
//   (debounced). Show Goals (Cmd/Ctrl+Alt+G) opens or focuses it.

import * as vscode from 'vscode';
import * as cp from 'child_process';
import * as path from 'path';
import * as tokenizer from './tokenizer';
import { quickBundleBinary } from './quickBundle';  // QUICK-BUNDLE: see quickBundle.ts

// Module-level handle for the extension's installation root. Set in
// activate(); needed by tokenizer.* (loads grammar + WASM relative
// to extension path). Empty string before activate (no rendering
// fires until then; defensive default).
let extensionPath: string = '';
import {
  LanguageClient,
  LanguageClientOptions,
  NotificationType,
  ServerOptions,
  Trace,
} from 'vscode-languageclient/node';

interface Position {
  line: number;
  character: number;
}

interface StateChangedParams {
  uri: string;
  sessionLabel: string;
  currentSentenceId: string | null;
  currentEndPosition: Position | null;
  cas: string;
  seq: number;
  origin: { kind: string; correlationId: string };
}

const stateChangedNotif =
  new NotificationType<StateChangedParams>('easycrypt/proof/stateChanged');

let client: LanguageClient | undefined;
let processedDecoration: vscode.TextEditorDecorationType | undefined;
let queuedDecoration: vscode.TextEditorDecorationType | undefined;

// Per-uri locked-region state, mirrored from stateChanged notifications.
// `currentEndPosition` is the LSP position immediately after the end
// of the most-recently-executed sentence. `null` means nothing has
// been executed (or the document was never opened).
const lockedEnd = new Map<string, Position | null>();
// Per-uri "queued" target — where the user has asked the daemon to
// move the locked tip to, but the daemon hasn't reported back yet.
// Painted in a distinct PG-style amber tint so the user sees the
// pending region. Cleared on the next stateChanged (which updates
// lockedEnd) or on request error.
const queuedEnd = new Map<string, Position | null>();
let lastSeq = 0;

function config() {
  return vscode.workspace.getConfiguration('easycrypt-tooling');
}

// Binary discovery chain (highest → lowest preference):
//   1. ECD_BIN / EC_BIN environment variables (set on the
//      VSCode-host process) — used by power users / CI / devshells
//      that pin a specific binary.
//   2. Workspace setting easycrypt-tooling.daemon.path /
//      easycrypt-tooling.ec.path — absolute path or
//      PATH-searched executable name.
//   3. QUICK-BUNDLE fallback (bundled .vsix only) — bundled binary
//      in <extension>/bin/<platform>/. Quarantined behind
//      quickBundleBinary() in src/quickBundle.ts; only fires when
//      neither env nor setting is set AND the bundled binary
//      exists. To be replaced by the proper resolver chain
//      (HANDOFF § G).
//   4. Default 'ecd' / unset for ec.path → the daemon falls back to
//      its own discovery (EC_LLM_BIN, in-tree _build, then
//      'easycrypt' on PATH).
// Returns the user-set value of [key] (any scope) or '' if the
// user hasn't set it (i.e. only the schema default would apply).
// Distinguishing user-set from schema-default is what lets the
// QUICK-BUNDLE fallback fire on a fresh install: config().get()
// returns the schema default, which is indistinguishable from
// "user explicitly set it to that string".
function userSetSetting(key: string): string {
  const ins = config().inspect<string>(key);
  if (!ins) return '';
  const v = ins.workspaceFolderValue ?? ins.workspaceValue ?? ins.globalValue;
  return (v ?? '').trim();
}

function pickDaemonBinary(): string {
  const fromEnv = process.env.ECD_BIN;
  if (fromEnv && fromEnv.trim() !== '') return fromEnv;
  const fromSetting = userSetSetting('daemon.path');
  if (fromSetting !== '') return fromSetting;
  // QUICK-BUNDLE
  const bundled = quickBundleBinary('ecd', extensionPath);
  if (bundled) return bundled;
  return 'ecd';
}

function pickEcBinary(): string {
  const fromEnv = process.env.EC_BIN;
  if (fromEnv && fromEnv.trim() !== '') return fromEnv;
  const fromSetting = userSetSetting('ec.path');
  if (fromSetting !== '') return fromSetting;
  // QUICK-BUNDLE
  const bundled = quickBundleBinary('ec', extensionPath);
  if (bundled) return bundled;
  return '';
}

function buildServerOptions(): ServerOptions {
  const cmd = pickDaemonBinary();
  const args = [...config().get<string[]>('daemon.args', ['daemon', '--stdio'])];
  const ecPath = pickEcBinary();
  if (ecPath !== '') {
    args.push('--bin', ecPath);
  }
  // Don't set `transport: TransportKind.stdio` — it's the default for
  // Executable, and setting it explicitly causes vscode-languageclient
  // to append a second `--stdio` to args, which Cmdliner rejects with
  // "option '--stdio' cannot be repeated".
  return { command: cmd, args };
}

function buildClientOptions(): LanguageClientOptions {
  return {
    documentSelector: [
      { scheme: 'file', language: 'easycrypt' },
      { scheme: 'untitled', language: 'easycrypt' },
    ],
    initializationOptions: {
      proof: {
        clientVersion: '0.0.2',
        supportsRecoveryStrategy: ['halt', 'best_effort_admit'],
        supportsCachePolicy: ['lax', 'strict'],
        supportsLongRunningProgress: true,
        supportsExecutingRangeNotification: true,
      },
    },
  };
}

function ensureProcessedDecoration(): vscode.TextEditorDecorationType {
  if (!processedDecoration) {
    processedDecoration = vscode.window.createTextEditorDecorationType({
      backgroundColor: 'rgba(120, 200, 120, 0.10)',
      isWholeLine: false,
      overviewRulerLane: vscode.OverviewRulerLane.Left,
      overviewRulerColor: 'rgba(120, 200, 120, 0.50)',
    });
  }
  return processedDecoration;
}

function ensureQueuedDecoration(): vscode.TextEditorDecorationType {
  if (!queuedDecoration) {
    queuedDecoration = vscode.window.createTextEditorDecorationType({
      backgroundColor: 'rgba(220, 160, 60, 0.18)',
      isWholeLine: false,
      overviewRulerLane: vscode.OverviewRulerLane.Left,
      overviewRulerColor: 'rgba(220, 160, 60, 0.55)',
    });
  }
  return queuedDecoration;
}

// Compare two LSP-style positions. <0 if a < b.
function comparePositions(a: Position, b: Position): number {
  if (a.line !== b.line) return a.line - b.line;
  return a.character - b.character;
}

// Refresh the processed + queued decorations on every visible editor
// for the given uri. Call this on stateChanged, request kickoff/done,
// and on activeTextEditor changes.
function refreshDecorations(uri: string): void {
  const locked = lockedEnd.get(uri) ?? null;
  const queued = queuedEnd.get(uri) ?? null;
  const lockedDeco = ensureProcessedDecoration();
  const queuedDeco = ensureQueuedDecoration();
  for (const editor of vscode.window.visibleTextEditors) {
    if (editor.document.uri.toString() !== uri) continue;
    // Locked region: (0,0) → locked.
    if (locked === null) {
      editor.setDecorations(lockedDeco, []);
    } else {
      editor.setDecorations(lockedDeco, [
        new vscode.Range(
          new vscode.Position(0, 0),
          new vscode.Position(locked.line, locked.character),
        ),
      ]);
    }
    // Queued region: shown when an exec/revert is in flight to a
    // different position than the current locked tip.
    if (queued === null) {
      editor.setDecorations(queuedDeco, []);
      continue;
    }
    const start = locked ?? { line: 0, character: 0 };
    if (comparePositions(start, queued) === 0) {
      // Already there — nothing to render.
      editor.setDecorations(queuedDeco, []);
    } else if (comparePositions(start, queued) < 0) {
      // Forward exec: queued region from current locked end to target.
      editor.setDecorations(queuedDeco, [
        new vscode.Range(
          new vscode.Position(start.line, start.character),
          new vscode.Position(queued.line, queued.character),
        ),
      ]);
    } else {
      // Backward revert: queued region from target back to current
      // locked end (which will shrink to target after stateChanged).
      editor.setDecorations(queuedDeco, [
        new vscode.Range(
          new vscode.Position(queued.line, queued.character),
          new vscode.Position(start.line, start.character),
        ),
      ]);
    }
  }
}

function setQueued(uri: string, target: Position | null): void {
  queuedEnd.set(uri, target);
  refreshDecorations(uri);
}

function clearQueued(uri: string): void {
  if (queuedEnd.delete(uri)) {
    refreshDecorations(uri);
  }
}

function refreshAllVisible(): void {
  for (const editor of vscode.window.visibleTextEditors) {
    if (editor.document.languageId !== 'easycrypt') continue;
    refreshDecorations(editor.document.uri.toString());
  }
}

async function startClient(): Promise<void> {
  if (client) {
    return;
  }
  const serverOptions = buildServerOptions();
  const clientOptions = buildClientOptions();
  client = new LanguageClient(
    'easycryptTooling',
    'EasyCrypt (tooling daemon)',
    serverOptions,
    clientOptions,
  );
  const traceLevel = config().get<string>('trace.server', 'off');
  if (traceLevel !== 'off') {
    await client.setTrace(traceLevel === 'verbose' ? Trace.Verbose : Trace.Messages);
  }
  await client.start();
  // Subscribe to stateChanged notifications (server → client).
  // Out-of-order arrivals are dropped via the seq counter — the
  // daemon emits monotonically and TCP/pipes preserve order, but the
  // guard makes the client robust to any client-side reordering.
  client.onNotification(stateChangedNotif, (params) => {
    if (params.seq <= lastSeq) return;
    lastSeq = params.seq;
    lockedEnd.set(params.uri, params.currentEndPosition);
    // State-mutating change — clear any user-pinned subgoal index
    // so the goal pane refreshes to EC's focused goal. (didChange
    // also emits stateChanged via auto-reconcile; we treat that the
    // same way: any state shift returns the pane to EC focus.)
    goalsCursor.delete(params.uri);
    // Any leftover speculative preview is invalidated by a real
    // state advance / revert.
    goalsPreview.delete(params.uri);
    // PG-style: the daemon emits one stateChanged per sentence
    // during multi-sentence execs (execToPoint, step count=N), so
    // the locked tint advances incrementally while the request is
    // still in flight. We DO NOT clear the queued tint here — the
    // request initiator (handleGotoCursor / step / back) clears it
    // when the response returns. Auto-clearing here would shrink
    // the amber prematurely after the first sentence completes.
    refreshDecorations(params.uri);
    // Auto-refresh the goal pane if it's open and either showing this
    // uri or hasn't been pinned to one yet.
    if (goalsPanel && (goalsForUri === undefined || goalsForUri === params.uri)) {
      scheduleGoalsRefresh(params.uri);
    }
  });
}

async function stopClient(): Promise<void> {
  if (!client) {
    return;
  }
  const c = client;
  client = undefined;
  await c.stop();
}

async function withClient<T>(fn: (c: LanguageClient) => Promise<T>): Promise<T | undefined> {
  if (!client) {
    await startClient();
  }
  if (!client) {
    vscode.window.showErrorMessage('EasyCrypt: daemon failed to start.');
    return undefined;
  }
  try {
    return await fn(client);
  } catch (err) {
    vscode.window.showErrorMessage(`EasyCrypt: ${err instanceof Error ? err.message : String(err)}`);
    return undefined;
  }
}

// ---- Preview log channels ------------------------------------------
//
// Per-builder Output channels for full tactic-preview errors. The
// InputBox's [validationMessage] is truncated to first line + ~120
// chars; the (detail) button on the InputBox opens the relevant
// channel for the full text.
//
// Channels: rewrite / apply / move / closer-sweep / one shared
// "(all)" aggregator that mirrors every entry tagged with its
// source. Selectable via [easycrypt.proof.previewLog.show] (a
// QuickPick over channel names).

// Channel name is the schema id (or 'closer' for the closer sweep).
// New schemas / call sites can pick any string — the channel is
// created lazily on first write.
export type PreviewLogKind = string;

const PREVIEW_LOG_ALL_TITLE = 'EasyCrypt: tactic preview (all)';

const previewLogChannels = new Map<PreviewLogKind, vscode.OutputChannel>();
let previewLogAllChannel: vscode.OutputChannel | undefined;

function getPreviewLogChannel(kind: PreviewLogKind): vscode.OutputChannel {
  let c = previewLogChannels.get(kind);
  if (!c) {
    c = vscode.window.createOutputChannel(
      `EasyCrypt: tactic preview — ${kind}`,
    );
    previewLogChannels.set(kind, c);
  }
  return c;
}

function getPreviewLogAllChannel(): vscode.OutputChannel {
  if (!previewLogAllChannel) {
    previewLogAllChannel =
      vscode.window.createOutputChannel(PREVIEW_LOG_ALL_TITLE);
  }
  return previewLogAllChannel;
}

// Append [body] to the per-kind channel and (with a [kind] tag) to
// the shared aggregator. [source] is the cumulative tactic source
// that triggered the error — included as a header for context.
export function logPreviewError(
  kind: PreviewLogKind,
  source: string,
  body: string,
): void {
  const ts = new Date().toISOString();
  const header = `[${ts}] source: ${source}`;
  const block = `${header}\n${body}\n`;
  getPreviewLogChannel(kind).appendLine(block);
  getPreviewLogAllChannel().appendLine(`[${kind}] ${block}`);
}

// QuickPick over the open channels (per-kind + "all"). Picking
// reveals + focuses the channel. Empty list still offers "all".
async function handleShowPreviewLog(): Promise<void> {
  const items: { label: string; channel: vscode.OutputChannel }[] = [];
  if (previewLogAllChannel) {
    items.push({ label: PREVIEW_LOG_ALL_TITLE, channel: previewLogAllChannel });
  }
  for (const [, c] of previewLogChannels) {
    items.push({ label: c.name, channel: c });
  }
  if (items.length === 0) {
    vscode.window.showInformationMessage(
      'EasyCrypt: no preview logs yet (no tactic-preview errors recorded this session).',
    );
    return;
  }
  const pick = await vscode.window.showQuickPick(
    items.map(i => i.label),
    {
      title: 'EasyCrypt: open preview log',
      placeHolder: 'Select a channel to surface (Esc to dismiss)',
    },
  );
  if (!pick) return;
  const found = items.find(i => i.label === pick);
  if (found) found.channel.show(/* preserveFocus */ false);
}

// Truncate a (possibly multi-line) error to first-line + ~maxChars
// for the InputBox's [validationMessage]. The full text always goes
// to the Output channel (caller writes that). Returns the displayed
// short form + a flag indicating truncation occurred.
const VALIDATION_MAX_CHARS = 120;

function truncateForValidation(msg: string): { short: string; truncated: boolean } {
  const firstLine = msg.split(/\r?\n/, 1)[0] ?? '';
  if (msg === firstLine && firstLine.length <= VALIDATION_MAX_CHARS) {
    return { short: msg, truncated: false };
  }
  const cut = firstLine.length > VALIDATION_MAX_CHARS
    ? firstLine.slice(0, VALIDATION_MAX_CHARS - 1) + '…'
    : firstLine;
  return { short: cut, truncated: true };
}

// Truncate a committed-token list to roughly [maxChars] for the
// InputBox [title] (line 1). On overflow, drops the middle and
// shows "…+N more". The caller is responsible for writing the
// full list to Output / popping a "show all" reveal.
function summarizeCommittedTokens(tokens: string[], maxChars: number): {
  short: string;
  truncated: boolean;
} {
  if (tokens.length === 0) return { short: '(none yet)', truncated: false };
  const joined = tokens.join('   ');
  if (joined.length <= maxChars) return { short: joined, truncated: false };
  // Show the first few that fit, then "…+M more".
  let used = 0;
  let kept = 0;
  const sep = '   ';
  for (let i = 0; i < tokens.length; i++) {
    const next = used + (i === 0 ? 0 : sep.length) + tokens[i].length;
    if (next > maxChars - 12) break;  // reserve room for "…+M more"
    used = next;
    kept = i + 1;
  }
  if (kept === 0) kept = 1;  // always show at least one
  const head = tokens.slice(0, kept).join(sep);
  const more = tokens.length - kept;
  return { short: `${head}   …+${more} more`, truncated: true };
}

function activeEcEditor(): vscode.TextEditor | undefined {
  const editor = vscode.window.activeTextEditor;
  if (!editor || editor.document.languageId !== 'easycrypt') {
    vscode.window.showWarningMessage('EasyCrypt: no .ec editor active.');
    return undefined;
  }
  return editor;
}

// ---- Goal pane webview ----------------------------------------------

interface Hypothesis {
  name: string;
  kind: string;
  pp: string;
}

// Conclusion tree (UPSTREAM #23 + #24). Node kinds:
// - 'pp':       opaque pp text leaf
// - 'judgment': structured PHL judgment with labeled per-kind children
// - 'stmt':     structured statement-list (UPSTREAM #24) — used in
//               the stmt / stmt_left / stmt_right / transferred_*
//               positions of judgment children. Each list element is
//               a recursive StmtNode.
// v1+ extends with propositional connectives + quantifiers; v_full
// adds structured terms inside leaf positions.
type ConclusionNode =
  | { kind: 'pp'; text: string }
  | { kind: 'judgment'; judgment_kind: JudgmentKind } & JudgmentFields
  | { kind: 'stmt'; body: StmtNode[] };

type JudgmentKind = 'hoare' | 'phoare' | 'ehoare' | 'equiv' | 'eager';

// Per-instruction structured node (UPSTREAM #24). Mirrors EC's
// stmt_node OCaml variant. Block constructs carry recursive
// children; loc currently always null (EC's IR drops parsetree
// positions during typecheck — future amendment populates).
interface StmtLoc {
  start_line: number;
  start_col:  number;
  end_line:   number;
  end_col:    number;
}

type StmtNode =
  | { kind: 'asgn';     pp: string; loc: StmtLoc | null }
  | { kind: 'rnd';      pp: string; loc: StmtLoc | null }
  | { kind: 'call';     pp: string; loc: StmtLoc | null }
  | { kind: 'raise';    pp: string; loc: StmtLoc | null }
  | { kind: 'abstract'; pp: string; loc: StmtLoc | null }
  | { kind: 'if';       cond_pp: string;
                        then_body: StmtNode[];
                        else_body: StmtNode[];
                        loc: StmtLoc | null }
  | { kind: 'while';    cond_pp: string;
                        body: StmtNode[];
                        loc: StmtLoc | null }
  | { kind: 'match';    target_pp: string;
                        branches: { pattern_pp: string; body: StmtNode[] }[];
                        loc: StmtLoc | null };

// Judgment-kind-specific labeled fields. TypeScript discriminated
// union via judgment_kind would be type-cleaner but verbose; using
// optional fields and dispatching on judgment_kind at the renderer.
interface JudgmentFields {
  pre?: ConclusionNode;
  stmt?: ConclusionNode;             // hoare/phoare/ehoare
  post?: ConclusionNode;
  bound?: ConclusionNode;             // phoare
  cmp?: '<=' | '=' | '>=';            // phoare
  stmt_left?: ConclusionNode;         // equiv/eager
  stmt_right?: ConclusionNode;        // equiv/eager
  transferred_left?: ConclusionNode;  // eager
  transferred_right?: ConclusionNode; // eager
}

interface Subgoal {
  index: number;
  hypotheses: Hypothesis[];
  conclusion: ConclusionNode;
}

// Best-effort flattening for callers that want plain text. Mirrors
// daemon-side Goal_view.to_pp_text. Used as a fallback in places
// that haven't been migrated to structured rendering yet.
function conclusionToPpText(c: ConclusionNode): string {
  if (c.kind === 'pp') return c.text;
  if (c.kind === 'stmt') return c.body.map(stmtNodeToPpText).join('; ');
  // judgment
  const r = (n?: ConclusionNode) => n ? conclusionToPpText(n) : '';
  switch (c.judgment_kind) {
    case 'hoare':  return `hoare[${r(c.stmt)} : ${r(c.pre)} ==> ${r(c.post)}]`;
    case 'phoare': return `phoare[${r(c.stmt)} : ${r(c.pre)} ==> ${r(c.post)}] ${c.cmp ?? '?'} ${r(c.bound)}`;
    case 'ehoare': return `ehoare[${r(c.stmt)} : ${r(c.pre)} ==> ${r(c.post)}]`;
    case 'equiv':  return `equiv[${r(c.stmt_left)} ~ ${r(c.stmt_right)} : ${r(c.pre)} ==> ${r(c.post)}]`;
    case 'eager':  return `eager[ ${r(c.transferred_left)}, ${r(c.stmt_left)} ~ ${r(c.stmt_right)}, ${r(c.transferred_right)} : ${r(c.pre)} ==> ${r(c.post)} ]`;
  }
}

function stmtNodeToPpText(s: StmtNode): string {
  switch (s.kind) {
    case 'asgn': case 'rnd': case 'call': case 'raise': case 'abstract':
      return s.pp;
    case 'if':
      return s.else_body.length === 0
        ? `if (${s.cond_pp}) { ${s.then_body.map(stmtNodeToPpText).join(' ')} }`
        : `if (${s.cond_pp}) { ${s.then_body.map(stmtNodeToPpText).join(' ')} } else { ${s.else_body.map(stmtNodeToPpText).join(' ')} }`;
    case 'while':
      return `while (${s.cond_pp}) { ${s.body.map(stmtNodeToPpText).join(' ')} }`;
    case 'match':
      return `match (${s.target_pp}) with ${s.branches.map(b => `| ${b.pattern_pp} => ${b.body.map(stmtNodeToPpText).join(' ')}`).join(' ')} end`;
  }
}

interface GoalsResponse {
  active: boolean;
  subgoal_count: number;
  current_index: number;
  subgoals: Subgoal[];
  provenance: string;
  cas: string;
}

let goalsPanel: vscode.WebviewPanel | undefined;
let goalsForUri: string | undefined;
let goalsRefreshTimer: NodeJS.Timeout | undefined;
// Per-uri "user has cycled to a specific subgoal" pin. Null = follow
// EC's focused subgoal (current_index from the GOALS-JSON envelope).
// Cleared on every stateChanged so a fresh state-mutating step
// resets the pane to whatever EC is now focused on; cycling pins
// the index across goal-pane refreshes that don't change state
// (e.g., didChange-driven re-fetch).
const goalsCursor = new Map<string, number | null>();

// Per-uri preview override. When set, fetchAndRenderGoals renders
// THIS payload instead of fetching live goals. Used by the move /
// rewrite builders and the lemma picker to show the speculative
// post-tactic state without polluting the cached goals fetch.
// Cleared on builder/picker dismiss; cleared automatically on
// stateChanged so a real state mutation invalidates any leftover
// preview.
// Comparison-view outcomes for the lemma-picker preview. The picker
// always renders top: current goal (unchanged — apply is speculative)
// + bottom: a colored box with the would-be result.
//
// Error sub-kinds:
//   'does-not-apply' — generic apply failure (red)
//   'needs-args'     — EC says "not all variables can be inferred";
//                      the lemma matches structurally but EC needs
//                      explicit arg hints (amber + hint to refine)
//   'parse'          — parse error from the trial (red)
type ComparisonErrorKind = 'does-not-apply' | 'needs-args' | 'parse';
type ComparisonOutcome =
  | { kind: 'success'; newGoals: GoalsResponse; closedFocused: boolean; cycleIndex: number }
  | { kind: 'error'; errorKind: ComparisonErrorKind; error: string };

// Sniff EC's err message for known patterns. Stopgap until daemon
// returns structured error codes for tactic failures.
function classifyTacticError(err: string): ComparisonErrorKind {
  const lc = err.toLowerCase();
  if (lc.includes('not all variables can be inferred')
      || lc.includes('cannot infer')
      || lc.includes('unification failed')) {
    return 'needs-args';
  }
  if (lc.includes('parse error') || lc.includes('lexical')) {
    return 'parse';
  }
  return 'does-not-apply';
}

type GoalsPreview =
  // Single-goal preview (used by move / rewrite builders that just
  // want to show the speculative state in place of live goals).
  | { kind: 'goals'; goals: GoalsResponse; badge: string }
  // Comparison preview (apply-lemma picker: shows current goal on top,
  // success/err block on bottom).
  | { kind: 'comparison'; topGoals: GoalsResponse | null; badge: string; outcome: ComparisonOutcome }
  // Pair preview — two outcomes stacked. Used by the rewrite-lemma
  // picker on first hover to show forward + backward results side
  // by side, so the user can compare directions before committing.
  | { kind: 'pair'; topGoals: GoalsResponse | null; badge: string;
      label1: string; outcome1: ComparisonOutcome;
      label2: string; outcome2: ComparisonOutcome };
const goalsPreview = new Map<string, GoalsPreview>();

function setGoalsPreview(uri: string, goals: GoalsResponse, badge: string): void {
  goalsPreview.set(uri, { kind: 'goals', goals, badge });
  if (goalsPanel && (goalsForUri === undefined || goalsForUri === uri)) {
    const displayIndex = pickDisplayIndex(uri, goals);
    // Async render (TM tokenizer is async). Sync setter with
    // fire-and-forget html assignment — re-checks panel ownership
    // after await in case another preview/state-change races us.
    void (async () => {
      const html = await renderGoalsHtml(goals, displayIndex, badge);
      if (goalsPanel && (goalsForUri === undefined || goalsForUri === uri)) {
        goalsPanel.webview.html = html;
      }
    })();
  }
}

// Comparison preview — current goal on top, success (green) / err
// (red) / closed (gold) block on bottom. Used by the apply-lemma
// picker so the user can compare what they have now to what they'd
// get without losing context. Cycle controls in the bottom box let
// the user step through new subgoals (postMessage → cycleIndex
// update → re-render).
// Set a pair preview — two outcomes rendered stacked. Used by the
// rewrite-lemma picker's first hover so the user sees forward and
// backward results at once before drilling into a specific
// direction.
function setGoalsPairPreview(
  uri: string,
  topGoals: GoalsResponse | null,
  badge: string,
  label1: string, outcome1: ComparisonOutcome,
  label2: string, outcome2: ComparisonOutcome,
): void {
  goalsPreview.set(uri, {
    kind: 'pair', topGoals, badge, label1, outcome1, label2, outcome2,
  });
  if (goalsPanel && (goalsForUri === undefined || goalsForUri === uri)) {
    void (async () => {
      const html = await renderPairHtml(
        uri, topGoals, badge, label1, outcome1, label2, outcome2,
      );
      if (goalsPanel && (goalsForUri === undefined || goalsForUri === uri)) {
        goalsPanel.webview.html = html;
      }
    })();
  }
}

function setGoalsComparisonPreview(
  uri: string,
  topGoals: GoalsResponse | null,
  badge: string,
  outcome: ComparisonOutcome,
): void {
  goalsPreview.set(uri, { kind: 'comparison', topGoals, badge, outcome });
  if (goalsPanel && (goalsForUri === undefined || goalsForUri === uri)) {
    void (async () => {
      const html = await renderComparisonHtml(uri, topGoals, badge, outcome);
      if (goalsPanel && (goalsForUri === undefined || goalsForUri === uri)) {
        goalsPanel.webview.html = html;
      }
    })();
  }
}

function clearGoalsPreview(uri: string): void {
  if (goalsPreview.delete(uri) && goalsPanel) {
    void fetchAndRenderGoals(uri);
  }
}

function escapeHtml(s: string): string {
  return s
    .replace(/&/g, '&amp;')
    .replace(/</g, '&lt;')
    .replace(/>/g, '&gt;')
    .replace(/"/g, '&quot;')
    .replace(/'/g, '&#39;');
}

// Compute which subgoal index to display. The user's pinned cursor
// (goalsCursor) wins if set; otherwise we follow EC's focused goal
// (current_index from the response). The result is clamped to a
// valid range — if subgoal_count drops below the pinned index due
// to a state change that arrived between cycles, we fall back to
// the last valid subgoal.
function pickDisplayIndex(uri: string, g: GoalsResponse): number {
  if (g.subgoal_count <= 0) return 0;
  const pinned = goalsCursor.get(uri);
  const candidate =
    pinned === null || pinned === undefined ? g.current_index : pinned;
  const clamped = Math.max(0, Math.min(g.subgoal_count - 1, candidate));
  return clamped;
}

// Render a ConclusionNode (UPSTREAM #23). v0 has two node kinds:
//   pp       — opaque text leaf, escaped + emitted as-is
//   judgment — structured PHL judgment, dispatched on judgment_kind
//              into a per-kind layout:
//                hoare/phoare/ehoare: stacked Pre / Stmt / Post
//                                     phoare adds a bound + cmp line
//                equiv:               side-by-side Stmt-Left | Stmt-Right
//                                     under shared Pre, over shared Post
//                eager:               same as equiv + transferred-stmt
//                                     blocks above each side
// v1+ adds new node kinds (implies, and, or, forall, etc.) — extend
// the dispatch with new render branches at that point.
//
// Per-kind sub-children are themselves ConclusionNodes (recursive
// call). For v0 they always bottom out as `pp` leaves; for v_full
// they carry deeper structured trees.
//
// No syntax highlighting yet — that's B.2 (TM via tokenizeAtPosition,
// fed through this same render pipeline once it lands). For now,
// stmt/program text is plain `<pre>`-style.
async function renderConclusion(c: ConclusionNode): Promise<string> {
  if (c.kind === 'pp') {
    return `<span class="cn-pp">${await escapeOrPrettify(c.text)}</span>`;
  }
  if (c.kind === 'stmt') {
    // Bare Cn_stmt at top level — shouldn't happen in v0 (judgments
    // wrap stmt fields), but render as a flat pp-text fallback so
    // we don't trip on it. v1+ would route through the stmt-tree
    // renderer if this case becomes meaningful.
    const text = c.body.map(stmtNodeToPpText).join('; ');
    return `<span class="cn-pp">${await escapeOrPrettify(text)}</span>`;
  }

  // Judgment helpers ------------------------------------------------

  const sub = async (n?: ConclusionNode) =>
    n ? await renderConclusion(n) : '<span class="cn-empty">(missing)</span>';

  // Wrap mode class — picked from setting; flips visual line-wrap
  // behavior via cn-wrap / cn-scroll. Toggleable via
  // Cmd/Ctrl+Alt+Z (handleToggleProgramWrap).
  const wrapMode = vscode.workspace
    .getConfiguration('easycrypt-tooling.display')
    .get<'wrap' | 'scroll'>('programWrap', 'wrap');
  const wrapClass = wrapMode === 'wrap' ? 'cn-wrap' : 'cn-scroll';

  // ---- Stmt-tree rendering (UPSTREAM #24) -------------------------
  //
  // For Cn_stmt children: walk the StmtNode tree producing one row
  // per logical instruction with a hierarchical position label
  // (1, 2, 2.1, 2.2, 3 for instructions inside a while at pos 2).
  // Block constructs (if / while / match) emit a "header" row at
  // their position + nested body rows beneath. Branch separators
  // ("} else {", "| pattern =>") render as label-only rows with no
  // position number.
  //
  // For Cn_pp text fallback: tokenize line-by-line + flat 1..N
  // numbering (legacy v0 behavior; activates when a daemon emits a
  // legacy text leaf in stmt position).
  // Codepos addressing for a numbered row — mirrors EC's
  // EcMatching.Position.codepos = (path, cpos1) where path is a
  // list of (cpos1, branch_select) descents and cpos1 is the
  // 1-based block-local position. branch_select:
  //   { type: 'cond', value: true }   -- if-then OR while-body
  //   { type: 'cond', value: false }  -- if-else
  //   { type: 'match', ctor: string } -- match arm by ctor name
  // Match-arm addressing: post-merge with origin/main, EC's
  // codepos_brsel includes a `MatchByPos of int` variant
  // (src/ecMatching.mli) — branches are addressable by 1-based
  // index without needing the constructor name. Walker emits
  // `match-by-pos` for match-arm descendants. (Pre-merge HEAD
  // emitted ctor='?' as a placeholder + uncertain=true; that
  // gating is no longer needed.)
  type CodeposBrSel =
    | { kind: 'cond'; value: boolean }
    | { kind: 'match'; ctor: string }
    | { kind: 'match-by-pos'; idx: number };
  interface CodeposPathStep { cpos1: number; brsel: CodeposBrSel; }
  interface Codepos { path: CodeposPathStep[]; cpos1: number; }

  type ProgSide = 'left' | 'right' | 'none';

  type ProgRow =
    | { kind: 'numbered'; pos: string; html: string; depth: number;
        side: ProgSide; codepos: Codepos;
        // True iff any path step has an unresolved (placeholder)
        // ctor — descended through a match branch where we don't
        // know the constructor name. Right-click "Rewrite/Change"
        // is suppressed for these rows.
        codeposUncertain: boolean; }
    | { kind: 'separator'; label: string; depth: number };

  const tokenizeOneLine = async (text: string): Promise<string> => {
    try {
      const lines = await tokenizer.highlightSourceLines(extensionPath, text);
      return lines.join('\n');
    } catch (_) {
      return await escapeOrPrettify(text);
    }
  };

  // Walker carries the codepos path of the enclosing block + the
  // side and uncertainty flag. `path` is the list of descents from
  // the program root to the current block; `cpos1` for each row is
  // its index within the current block (idx).
  const stmtTreeToRows = async (
    stmts: StmtNode[], parentPos: string, depth: number,
    path: CodeposPathStep[], side: ProgSide, uncertain: boolean,
  ): Promise<ProgRow[]> => {
    const rows: ProgRow[] = [];
    let idx = 1;
    for (const s of stmts) {
      const pos = parentPos + idx.toString();
      const codepos: Codepos = { path, cpos1: idx };
      switch (s.kind) {
        case 'asgn': case 'rnd': case 'call':
        case 'raise': case 'abstract': {
          rows.push({ kind: 'numbered', pos,
                      html: await tokenizeOneLine(s.pp), depth,
                      side, codepos, codeposUncertain: uncertain });
          break;
        }
        case 'if': {
          const header = `if (${await tokenizeOneLine(s.cond_pp)}) {`;
          rows.push({ kind: 'numbered', pos, html: header, depth,
                      side, codepos, codeposUncertain: uncertain });
          rows.push(...await stmtTreeToRows(
            s.then_body, pos + '.', depth + 1,
            [...path, { cpos1: idx, brsel: { kind: 'cond', value: true } }],
            side, uncertain));
          if (s.else_body.length > 0) {
            rows.push({ kind: 'separator', label: '} else {', depth });
            rows.push(...await stmtTreeToRows(
              s.else_body, pos + '.', depth + 1,
              [...path, { cpos1: idx, brsel: { kind: 'cond', value: false } }],
              side, uncertain));
          }
          rows.push({ kind: 'separator', label: '}', depth });
          break;
        }
        case 'while': {
          const header = `while (${await tokenizeOneLine(s.cond_pp)}) {`;
          rows.push({ kind: 'numbered', pos, html: header, depth,
                      side, codepos, codeposUncertain: uncertain });
          // EC convention: while-body uses `Cond true` (single-body
          // analog of if-then) — see EcMatching.normalize_brsel.
          rows.push(...await stmtTreeToRows(
            s.body, pos + '.', depth + 1,
            [...path, { cpos1: idx, brsel: { kind: 'cond', value: true } }],
            side, uncertain));
          rows.push({ kind: 'separator', label: '}', depth });
          break;
        }
        case 'match': {
          const header = `match (${await tokenizeOneLine(s.target_pp)}) with`;
          rows.push({ kind: 'numbered', pos, html: header, depth,
                      side, codepos, codeposUncertain: uncertain });
          // Match branches addressable by 1-based index via
          // origin/main's `MatchByPos of int` codepos_brsel
          // variant — closes the UPSTREAM #24 pattern_pp ctor-
          // name gap. Index `branchIdx` matches EC's branch
          // numbering (declaration order in the match).
          let branchIdx = 1;
          for (const b of s.branches) {
            rows.push({ kind: 'separator',
                        label: `| ${b.pattern_pp} =>`, depth });
            rows.push(...await stmtTreeToRows(
              b.body, pos + '.', depth + 1,
              [...path, { cpos1: idx, brsel: { kind: 'match-by-pos', idx: branchIdx } }],
              side, uncertain));
            branchIdx++;
          }
          rows.push({ kind: 'separator', label: 'end', depth });
          break;
        }
      }
      idx++;
    }
    return rows;
  };

  // Convert a Cn_pp text leaf into a flat ProgRow list (one per
  // newline-separated line; positions 1..N; depth 0). Used as the
  // fallback when daemon emits legacy text in stmt position.
  // No structured codepos — pp-text fallback rows are NOT
  // selectable for proc rewrite / proc change (uncertain=true).
  const ppToRows = async (text: string, side: ProgSide): Promise<ProgRow[]> => {
    let lines: string[];
    try {
      lines = await tokenizer.highlightSourceLines(extensionPath, text);
    } catch (_) {
      lines = await Promise.all(text.split('\n').map((l) => escapeOrPrettify(l)));
    }
    return lines.map((html, i) => ({
      kind: 'numbered' as const, pos: (i + 1).toString(), html, depth: 0,
      side, codepos: { path: [], cpos1: i + 1 },
      codeposUncertain: true,
    }));
  };

  // Resolve a ConclusionNode in stmt position to ProgRow list.
  const programRows = async (
    n: ConclusionNode | undefined, side: ProgSide,
  ): Promise<ProgRow[]> => {
    if (!n) return [];
    if (n.kind === 'stmt') return await stmtTreeToRows(n.body, '', 0, [], side, false);
    if (n.kind === 'pp')   return await ppToRows(n.text, side);
    return [];
  };

  // Codepos JSON encoding for HTML data-* attributes. Round-trips
  // through JSON.parse on the webview side. Single-quoted in HTML
  // because we need to preserve the encoded JSON's double-quoted
  // strings.
  const encodeCodeposAttr = (cp: Codepos): string =>
    encodeURIComponent(JSON.stringify(cp));

  // Render rows into the LEFT-numbered grid (hoare/phoare/ehoare).
  // Numbered rows carry data-* attributes for the selection state
  // machine to read on click / shift-click / right-click.
  const renderRowsLeftNumbered = (rows: ProgRow[]): string => {
    if (rows.length === 0) return '<span class="cn-empty">(missing)</span>';
    return `<div class="cn-prog-grid cn-prog-left-num ${wrapClass}">` +
      rows.map((r) => {
        const indent = `style="padding-left: ${r.depth * 1.2}em"`;
        if (r.kind === 'separator') {
          return `<span class="cn-lineno"></span>` +
                 `<span class="cn-line cn-sep" ${indent}>${escapeHtml(r.label)}</span>`;
        }
        const attrs =
          ` data-side="${r.side}"` +
          ` data-codepos="${encodeCodeposAttr(r.codepos)}"` +
          ` data-cpos1="${r.codepos.cpos1}"` +
          (r.codeposUncertain ? ` data-codepos-uncertain="1"` : ``);
        return `<span class="cn-lineno cn-row-handle"${attrs}>${r.pos}</span>` +
               `<span class="cn-line cn-row-handle"${attrs} ${indent}>${r.html}</span>`;
      }).join('') +
      `</div>`;
  };

  // Render two row-lists into a side-by-side grid with line-numbers
  // in the middle. Equiv-alignment setting (default 'aligned')
  // controls whether numbers share a single shared row index across
  // both columns or render per-side independently.
  const renderRowsMiddleNumbered = (
    lRows: ProgRow[], rRows: ProgRow[],
  ): string => {
    const alignment = vscode.workspace
      .getConfiguration('easycrypt-tooling.display')
      .get<'aligned' | 'independent'>('equivAlignment', 'aligned');
    const renderCell = (r: ProgRow | undefined, side: 'l' | 'r'): string => {
      if (!r) return `<span class="cn-line cn-line-${side}"></span>`;
      const indent = `style="padding-left: ${r.depth * 1.2}em"`;
      if (r.kind === 'separator') {
        return `<span class="cn-line cn-line-${side} cn-sep" ${indent}>` +
               `${escapeHtml(r.label)}</span>`;
      }
      const attrs =
        ` data-side="${r.side}"` +
        ` data-codepos="${encodeCodeposAttr(r.codepos)}"` +
        ` data-cpos1="${r.codepos.cpos1}"` +
        (r.codeposUncertain ? ` data-codepos-uncertain="1"` : ``);
      return `<span class="cn-line cn-line-${side} cn-row-handle"${attrs} ${indent}>${r.html}</span>`;
    };
    const renderNumCell = (rl: ProgRow | undefined, rr: ProgRow | undefined,
                           rowIdx: number): string => {
      if (alignment === 'aligned') {
        const hasNumbered =
          (rl && rl.kind === 'numbered')
          || (rr && rr.kind === 'numbered');
        return `<span class="cn-lineno">${hasNumbered ? rowIdx : ''}</span>`;
      }
      const lp = rl && rl.kind === 'numbered' ? rl.pos : '';
      const rp = rr && rr.kind === 'numbered' ? rr.pos : '';
      const text = lp && rp ? `${lp}|${rp}` : (lp || rp);
      return `<span class="cn-lineno">${text}</span>`;
    };
    const n = Math.max(lRows.length, rRows.length);
    if (n === 0) return '<span class="cn-empty">(missing)</span>';
    const out: string[] = [];
    for (let i = 0; i < n; i++) {
      const lR = lRows[i];
      const rR = rRows[i];
      out.push(renderCell(lR, 'l'));
      out.push(renderNumCell(lR, rR, i + 1));
      out.push(renderCell(rR, 'r'));
    }
    return `<div class="cn-prog-grid cn-prog-mid-num ${wrapClass}">${out.join('')}</div>`;
  };

  // Hoare-style single program: line numbers on the LEFT. Side
  // is 'none' for hoare/phoare/ehoare (no relational side).
  const programWithLeftNumbers = async (n?: ConclusionNode): Promise<string> => {
    return renderRowsLeftNumbered(await programRows(n, 'none'));
  };

  // Equiv-style two-program: line numbers in the MIDDLE. Each
  // side gets its own programRows call with the matching side tag.
  const programsWithMiddleNumbers = async (
    nL?: ConclusionNode, nR?: ConclusionNode,
  ): Promise<string> => {
    const [lRows, rRows] = await Promise.all([
      programRows(nL, 'left'), programRows(nR, 'right'),
    ]);
    return renderRowsMiddleNumbered(lRows, rRows);
  };

  // Compact formula row — small label, inline value. No box; flows
  // with the surrounding text.
  const formulaRow = async (label: string, n?: ConclusionNode) => `
    <div class="cn-row">
      <span class="cn-label">${escapeHtml(label)}</span>
      <span class="cn-value">${await sub(n)}</span>
    </div>`;

  // Single-program block (hoare / phoare / ehoare): formula rows
  // for pre/post, framed program with left-side line numbers.
  const singleProgramJudgment = async (
    headerLabel: string, c2: ConclusionNode & { kind: 'judgment' },
    extraRows: string = '',
  ): Promise<string> => `
    <div class="cn-judgment cn-single">
      <div class="cn-kind-tag">${escapeHtml(headerLabel)}</div>
      ${await formulaRow('pre', c2.pre)}
      <div class="cn-prog-frame">
        ${await programWithLeftNumbers(c2.stmt)}
      </div>
      ${await formulaRow('post', c2.post)}
      ${extraRows}
    </div>`;

  switch (c.judgment_kind) {
    case 'hoare':
      return await singleProgramJudgment('hoare', c);
    case 'phoare': {
      // Render bound with cmp as a distinct, visible glyph (not
      // just inline text) so users don't misread `bound = X` as
      // assignment. cmp gets its own colored pill; bound value
      // sits on the right.
      const cmp = c.cmp ?? '?';
      const cmpUnicode =
        cmp === '<=' ? '≤' : cmp === '>=' ? '≥' : cmp === '=' ? '=' : cmp;
      const cmpClass = cmp === '=' ? 'cn-cmp cn-cmp-eq' : 'cn-cmp';
      const boundRow = `
        <div class="cn-row cn-bound-row">
          <span class="cn-label">bound</span>
          <span class="${cmpClass}">${escapeHtml(cmpUnicode)}</span>
          <span class="cn-value">${await sub(c.bound)}</span>
        </div>`;
      return await singleProgramJudgment('phoare', c, boundRow);
    }
    case 'ehoare':
      return await singleProgramJudgment('ehoare', c);
    case 'equiv':
      return `
        <div class="cn-judgment cn-double">
          <div class="cn-kind-tag">equiv</div>
          ${await formulaRow('pre', c.pre)}
          <div class="cn-prog-frame">
            ${await programsWithMiddleNumbers(c.stmt_left, c.stmt_right)}
          </div>
          ${await formulaRow('post', c.post)}
        </div>`;
    case 'eager':
      return `
        <div class="cn-judgment cn-double">
          <div class="cn-kind-tag">eager</div>
          ${await formulaRow('pre', c.pre)}
          <div class="cn-eager-section">
            <div class="cn-section-label">transferred</div>
            <div class="cn-prog-frame">
              ${await programsWithMiddleNumbers(c.transferred_left, c.transferred_right)}
            </div>
          </div>
          <div class="cn-eager-section">
            <div class="cn-section-label">main</div>
            <div class="cn-prog-frame">
              ${await programsWithMiddleNumbers(c.stmt_left, c.stmt_right)}
            </div>
          </div>
          ${await formulaRow('post', c.post)}
        </div>`;
  }
}

// Render a non-program text leaf with TM tokenization +
// highlighting + prettify. Used for pp leaves outside program
// contexts (formula bodies, hypothesis types). Same TM tokenizer
// pipeline as program leaves so prettify (Pr → ℙ, <$ → ←$ etc.)
// catches identifier-adjacent operators in formulas like
// `Pr[A.guess(x) @ &m : ...]`. Earlier whitespace-split tokenization
// failed because the whole bracketed expression stayed as one
// chunk.
//
// Async — see comment on renderConclusion. Falls back to plain
// escape on tokenizer failure.
async function escapeOrPrettify(s: string): Promise<string> {
  const prettify = vscode.workspace
    .getConfiguration('easycrypt-tooling.display')
    .get<boolean>('prettify', true);
  // Even with prettify off, run through the tokenizer so we get
  // syntax highlighting on formula-context pp text — keywords like
  // forall/exists/Pr light up consistently with the rest of the pane.
  try {
    return await tokenizer.highlightSource(extensionPath, s);
  } catch (_) {
    if (!prettify) return escapeHtml(s);
    return s
      .split(/(\s+)/)
      .map((chunk) => {
        if (/^\s+$/.test(chunk)) return chunk;
        return escapeHtml(tokenizer.prettifyTokenInline(chunk));
      })
      .join('');
  }
}

async function renderGoalsHtml(
  g: GoalsResponse,
  displayIndex: number,
  previewBadge?: string,
): Promise<string> {
  const styles = `
    body {
      font-family: var(--vscode-editor-font-family, monospace);
      font-size: var(--vscode-editor-font-size, 13px);
      color: var(--vscode-editor-foreground);
      background: var(--vscode-editor-background);
      padding: 0.5em 1em;
    }
    .header {
      color: var(--vscode-descriptionForeground);
      font-size: 0.9em;
      margin-bottom: 0.5em;
    }
    .pin-badge {
      color: var(--vscode-charts-orange, #d68000);
      font-weight: bold;
      margin-left: 0.5em;
    }
    .subgoal {
      margin-bottom: 1.5em;
      padding-bottom: 1em;
    }
    .subgoal-header {
      font-weight: bold;
      margin-bottom: 0.5em;
      color: var(--vscode-textLink-foreground);
    }
    .hyp {
      margin-left: 1em;
    }
    .hyp-name { font-weight: bold; }
    .hyp-kind {
      color: var(--vscode-descriptionForeground);
      font-size: 0.85em;
      margin-right: 0.5em;
    }
    .conclusion {
      margin-top: 0.5em;
      padding-top: 0.5em;
      border-top: 1px dashed var(--vscode-panel-border);
    }
    .pp { white-space: pre-wrap; }
    /* One outer scroll container for the whole subgoal — inner
       blocks flow naturally, no nested overflow that hides post. */
    .subgoal { max-height: calc(100vh - 4em); overflow: auto; }
    .empty {
      color: var(--vscode-descriptionForeground);
      font-style: italic;
    }
    .navhint {
      color: var(--vscode-descriptionForeground);
      font-size: 0.85em;
      margin-top: 1em;
      border-top: 1px dotted var(--vscode-panel-border);
      padding-top: 0.3em;
    }
    /* Structured conclusion (UPSTREAM #23) — judgment layouts.
       Sleek, PG-inspired but tighter. Each judgment is one block
       with a small kind tag, compact pre/post rows, and a framed
       program section. No nested overflow — outer .subgoal scrolls. */
    .cn-pp { white-space: pre-wrap; }
    .cn-empty { color: var(--vscode-descriptionForeground); font-style: italic; }
    .cn-judgment {
      display: block;
      margin: 0.25em 0;
    }
    .cn-kind-tag {
      display: inline-block;
      color: var(--vscode-textLink-foreground);
      font-size: 0.8em;
      font-weight: bold;
      letter-spacing: 0.05em;
      text-transform: uppercase;
      margin-bottom: 0.3em;
      padding: 0.05em 0.4em;
      border-radius: 2px;
      background: rgba(127,127,127,0.08);
    }
    /* Compact pre/post rows. Label + value on one line where
       possible; wraps under for long values. */
    .cn-row {
      display: flex;
      flex-wrap: wrap;
      align-items: baseline;
      gap: 0.5em;
      margin: 0.4em 0;
    }
    .cn-label {
      color: var(--vscode-descriptionForeground);
      font-size: 0.8em;
      font-weight: bold;
      min-width: 2.5em;
      text-align: right;
    }
    .cn-value { white-space: pre-wrap; flex: 1 1 auto; min-width: 0; }
    /* phoare bound cmp — bold, larger, colored so it doesn't read
       as assignment. Distinct color for the equality variant
       (semantically different from inequality bounds). */
    .cn-cmp {
      font-weight: bold;
      font-size: 1.15em;
      color: var(--vscode-charts-blue, #4fc1ff);
      padding: 0 0.2em;
      min-width: 1.2em;
      text-align: center;
    }
    .cn-cmp.cn-cmp-eq {
      color: var(--vscode-charts-purple, #c586c0);
    }
    .cn-bound-row { margin-top: 0.5em; }
    /* Program frame — subtle indent + tint, no heavy border. Adds
       a touch of vertical breathing room above + below so it
       doesn't crowd the pre/post rows. */
    .cn-prog-frame {
      margin: 0.6em 0 0.6em 0.5em;
      padding: 0.4em 0;
      background: rgba(127,127,127,0.04);
      border-radius: 3px;
    }
    /* Eager has multiple program sections, each labeled. */
    .cn-eager-section { margin: 0.3em 0; }
    .cn-section-label {
      color: var(--vscode-descriptionForeground);
      font-size: 0.75em;
      font-weight: bold;
      text-transform: uppercase;
      letter-spacing: 0.05em;
      padding-left: 0.5em;
    }
    /* Line-numbered program grids. */
    .cn-prog-grid {
      display: grid;
      font-family: var(--vscode-editor-font-family, monospace);
      font-size: var(--vscode-editor-font-size, 13px);
      line-height: 1.5;
      column-gap: 0.5em;
      align-items: baseline;
    }
    /* Hoare-style: line-no | code (left numbers). */
    .cn-prog-left-num {
      grid-template-columns: max-content 1fr;
      padding: 0.2em 0.5em;
    }
    /* Equiv-style: left | line-no | right (middle numbers).
       minmax(0, 1fr) forces equal halves regardless of content
       width — without it, the auto column hugs whichever side has
       wider content. column-gap puts breathing room around the
       numbers so they sit visually between the two programs. */
    .cn-prog-mid-num {
      grid-template-columns: minmax(0, 1fr) max-content minmax(0, 1fr);
      padding: 0.2em 0.5em;
      column-gap: 1.2em;
    }
    .cn-lineno {
      color: var(--vscode-editorLineNumber-foreground, #858585);
      font-size: 0.85em;
      text-align: center;
      user-select: none;
      padding: 0 0.5em;
      opacity: 0.7;
      min-width: 1.5em;
    }
    /* Wrap-aware line cells: when wrap mode is on, continuation
       lines sit closer than separate code lines (tighter
       line-height inside, normal margin-bottom between cells). */
    .cn-line {
      overflow-wrap: anywhere;
      line-height: 1.4;
    }
    .cn-line-l { text-align: left; }
    .cn-line-r { text-align: left; }
    /* Separator row in stmt-tree (UPSTREAM #24): "} else {", "}",
       "| pattern =>", "end" — no position number, lighter color
       than code. */
    .cn-sep {
      color: var(--vscode-descriptionForeground);
      opacity: 0.85;
      font-style: italic;
    }
    /* Wrap mode (default): wrap long lines; tighter line-height
       inside a wrapped line vs taller spacing between separate
       lines. */
    .cn-prog-grid.cn-wrap .cn-line {
      white-space: pre-wrap;
    }
    .cn-prog-grid.cn-wrap {
      row-gap: 0.15em;
    }
    /* Scroll mode: keep lines on one line each, horizontal scroll
       when overflowed. No wrap. */
    .cn-prog-grid.cn-scroll .cn-line {
      white-space: pre;
    }
    .cn-prog-grid.cn-scroll {
      overflow-x: auto;
      row-gap: 0;
    }
    /* TM tokenizer (tokenizer.ts) emits these classes. Theme-aware:
       VSCode webviews inherit body.vscode-{light,dark,high-contrast}.
       Per-theme palettes for readable contrast on both dark + light
       backgrounds. */
    body.vscode-dark {
      --ts-kw-control: #c586c0;
      --ts-kw: #569cd6;
      --ts-kw-op: #d4d4d4;
      --ts-storage: #4fc1ff;
      --ts-type: #4ec9b0;
      --ts-fn: #dcdcaa;
      --ts-name: #9cdcfe;
      --ts-num: #b5cea8;
      --ts-string: #ce9178;
      --ts-comment: #6a9955;
    }
    body.vscode-light {
      --ts-kw-control: #af00db;
      --ts-kw: #0000ff;
      --ts-kw-op: #000000;
      --ts-storage: #0070c1;
      --ts-type: #267f99;
      --ts-fn: #795e26;
      --ts-name: #001080;
      --ts-num: #098658;
      --ts-string: #a31515;
      --ts-comment: #008000;
    }
    body.vscode-high-contrast {
      --ts-kw-control: #d33682;
      --ts-kw: #569cd6;
      --ts-kw-op: #ffffff;
      --ts-storage: #4fc1ff;
      --ts-type: #4ec9b0;
      --ts-fn: #dcdcaa;
      --ts-name: #9cdcfe;
      --ts-num: #b5cea8;
      --ts-string: #ce9178;
      --ts-comment: #7ca668;
    }
    .ts-kw-control { color: var(--ts-kw-control); font-weight: bold; }
    .ts-kw-operator { color: var(--ts-kw-op); }
    .ts-kw { color: var(--ts-kw); font-weight: bold; }
    .ts-type { color: var(--ts-type); }
    .ts-type-name { color: var(--ts-type); }
    .ts-storage { color: var(--ts-storage); font-weight: bold; }
    .ts-fn-name { color: var(--ts-fn); }
    .ts-name { color: var(--ts-name); }
    .ts-var { color: var(--ts-name); }
    .ts-num { color: var(--ts-num); }
    .ts-const { color: var(--ts-num); }
    .ts-string { color: var(--ts-string); }
    .ts-comment { color: var(--ts-comment); font-style: italic; }
    .ts-punct { color: var(--vscode-foreground, inherit); }
    /* Mouse line selection on program rows (proc rewrite / proc
       change). cn-row-handle is the mouse-target span emitted by
       renderRowsLeftNumbered / renderRowsMiddleNumbered for each
       numbered row. The .ec-selected class (toggled by the
       selection state machine in selectionScript below) paints a
       left border + background tint to mark the chosen row(s).
       Uncertain rows (under match-arms; ctor name not yet surfaced
       per UPSTREAM #24 amendment) get a duller hover. */
    .cn-row-handle { cursor: pointer; }
    .cn-row-handle:hover {
      background: var(--vscode-list-hoverBackground, rgba(127,127,127,0.08));
    }
    .cn-row-handle[data-codepos-uncertain="1"]:hover {
      background: var(--vscode-list-inactiveSelectionBackground,
                  rgba(127,127,127,0.04));
    }
    .ec-selected {
      background: var(--vscode-list-activeSelectionBackground,
                  rgba(91,148,210,0.25)) !important;
      box-shadow: inset 3px 0 0 var(--vscode-charts-blue, #3794ff);
    }
    /* Floating context menu, positioned at click coords. */
    .ec-ctxmenu {
      position: fixed;
      z-index: 1000;
      min-width: 12em;
      background: var(--vscode-menu-background, var(--vscode-editor-background));
      color: var(--vscode-menu-foreground, var(--vscode-editor-foreground));
      border: 1px solid var(--vscode-menu-border, var(--vscode-panel-border));
      box-shadow: 0 2px 8px rgba(0,0,0,0.25);
      padding: 0.25em 0;
      font-size: var(--vscode-editor-font-size, 13px);
    }
    .ec-ctxmenu .ec-ctxitem {
      padding: 0.3em 0.9em;
      cursor: pointer;
      white-space: nowrap;
    }
    .ec-ctxmenu .ec-ctxitem:hover {
      background: var(--vscode-menu-selectionBackground, rgba(91,148,210,0.25));
      color: var(--vscode-menu-selectionForeground, inherit);
    }
    .ec-ctxmenu .ec-ctxitem.ec-ctxdisabled {
      color: var(--vscode-disabledForeground, rgba(127,127,127,0.6));
      cursor: default;
    }
    .ec-ctxmenu .ec-ctxitem.ec-ctxdisabled:hover { background: inherit; }
    .ec-ctxmenu .ec-ctxsep {
      border-top: 1px solid var(--vscode-menu-separatorBackground,
                              var(--vscode-panel-border));
      margin: 0.25em 0;
    }
  `;
  if (!g.active) {
    return `<!DOCTYPE html><html><head><style>${styles}</style></head>
<body>
  <div class="header">no active proof</div>
  <div class="empty">step into a lemma's proof to see goals here</div>
</body></html>`;
  }
  // Display the chosen subgoal. The header shows position + total
  // and a pin badge when the user has cycled away from EC's focus.
  const total = g.subgoal_count;
  const ecFocused = g.current_index;
  const isPinned = displayIndex !== ecFocused;
  const pinBadge = isPinned
    ? `<span class="pin-badge">📌 pinned (EC focus: subgoal ${ecFocused + 1})</span>`
    : '';
  const previewBadgeHtml = previewBadge
    ? `<span class="pin-badge">${escapeHtml(previewBadge)}</span>`
    : '';
  const header =
    `<div class="header">subgoal ${displayIndex + 1} of ${total} `
    + `· provenance=${escapeHtml(g.provenance)}${pinBadge}${previewBadgeHtml}</div>`;
  if (g.subgoals.length === 0) {
    return `<!DOCTYPE html><html><head><style>${styles}</style></head>
<body>${header}<div class="empty">no subgoals — proof complete</div></body></html>`;
  }
  // Single-subgoal view — render only the chosen one. Cycling
  // (Cmd/Ctrl+Alt+]/[) walks through the rest.
  const sg = g.subgoals[displayIndex] ?? g.subgoals[0];
  const hyps = sg.hypotheses.length === 0
    ? '<div class="empty hyp">(no hypotheses)</div>'
    : sg.hypotheses
        .map(
          (h) =>
            `<div class="hyp"><span class="hyp-kind">[${escapeHtml(h.kind)}]</span>` +
            `<span class="hyp-name">${escapeHtml(h.name)}</span>` +
            ` : <span class="pp">${escapeHtml(h.pp)}</span></div>`,
        )
        .join('\n');
  // For structured conclusions (judgment), drop the leading ⊢ — the
  // per-section labels (pre / stmt / post) replace its semantic role
  // and a leading turnstile becomes orphaned visual chrome. Keep ⊢
  // for `pp` leaves (single-line conclusions where it's meaningful).
  const turnstile = sg.conclusion.kind === 'pp' ? '⊢ ' : '';
  const subgoalHtml = `<div class="subgoal">
  <div class="subgoal-header">subgoal ${sg.index + 1}</div>
  ${hyps}
  <div class="conclusion">${turnstile}${await renderConclusion(sg.conclusion)}</div>
</div>`;
  const navHint =
    total > 1
      ? `<div class="navhint">Cmd/Ctrl+Alt+] next subgoal · Cmd/Ctrl+Alt+[ previous</div>`
      : '';
  // Mouse line selection state machine + context menu primitive.
  // Lives here (in the goals webview HTML) so the panel doesn't
  // need a separate WebView for the menu. acquireVsCodeApi must
  // be called exactly once per webview; calls happen here and in
  // any other in-pane scripts (just this one for now).
  //
  // Selection model:
  //   - Click a numbered row → lock single-row selection.
  //   - Shift+click another row → if same side AND same path,
  //     extend to range; else clear and lock at the new row.
  //   - Click empty area / Esc → clear.
  //   - Right-click a selected row (or unselected — auto-locks
  //     it) → show context menu with "Rewrite at line N"
  //     (single-row, non-uncertain) and "Change range N..M"
  //     (when range valid).
  //
  // Uncertain rows (data-codepos-uncertain="1") are still
  // selectable for visual purposes but the context menu shows
  // the actions disabled with an explanatory tooltip.
  const selectionScript = `<script>
    (function() {
      const vscode = acquireVsCodeApi();
      let anchor = null;  // first-clicked row (locks single)
      let extent = null;  // shift+clicked row (locks range)
      function rowFromTarget(t) {
        while (t && t.classList && !t.classList.contains('cn-row-handle')) t = t.parentElement;
        return t && t.classList && t.classList.contains('cn-row-handle') ? t : null;
      }
      function rowKey(r) {
        // Identity for selection: side + cpos string + JSON path
        return (r.dataset.side || 'none') + '|' +
               (r.dataset.codepos || '');
      }
      function decodeCodepos(r) {
        try { return JSON.parse(decodeURIComponent(r.dataset.codepos || '')); }
        catch (_) { return null; }
      }
      function pathEq(p1, p2) {
        if (!p1 || !p2) return false;
        if (p1.length !== p2.length) return false;
        for (let i = 0; i < p1.length; i++) {
          if (p1[i].cpos1 !== p2[i].cpos1) return false;
          const b1 = p1[i].brsel; const b2 = p2[i].brsel;
          if (b1.kind !== b2.kind) return false;
          if (b1.kind === 'cond' && b1.value !== b2.value) return false;
          if (b1.kind === 'match' && b1.ctor !== b2.ctor) return false;
        }
        return true;
      }
      function clearSelection() {
        document.querySelectorAll('.ec-selected').forEach((e) => e.classList.remove('ec-selected'));
        anchor = null; extent = null;
        hideMenu();
      }
      function applySelectionVisual() {
        document.querySelectorAll('.ec-selected').forEach((e) => e.classList.remove('ec-selected'));
        if (!anchor) return;
        // Mark all spans (lineno + line) for the anchor row.
        const aKey = rowKey(anchor);
        document.querySelectorAll('.cn-row-handle').forEach((e) => {
          if (rowKey(e) === aKey) e.classList.add('ec-selected');
        });
        if (!extent) return;
        // Mark all rows in range. Range spans cpos1 from anchor to
        // extent INCLUSIVE; same side, same path.
        const aCp = decodeCodepos(anchor);
        const eCp = decodeCodepos(extent);
        if (!aCp || !eCp) return;
        if (anchor.dataset.side !== extent.dataset.side) return;
        if (!pathEq(aCp.path, eCp.path)) return;
        const lo = Math.min(aCp.cpos1, eCp.cpos1);
        const hi = Math.max(aCp.cpos1, eCp.cpos1);
        const side = anchor.dataset.side;
        document.querySelectorAll('.cn-row-handle').forEach((e) => {
          if ((e.dataset.side || 'none') !== side) return;
          const cp = decodeCodepos(e);
          if (!cp) return;
          if (!pathEq(cp.path, aCp.path)) return;
          if (cp.cpos1 >= lo && cp.cpos1 <= hi) e.classList.add('ec-selected');
        });
      }
      function hideMenu() {
        const m = document.getElementById('ec-ctxmenu');
        if (m) m.remove();
      }
      function showMenu(x, y, items) {
        hideMenu();
        const m = document.createElement('div');
        m.id = 'ec-ctxmenu';
        m.className = 'ec-ctxmenu';
        m.style.left = x + 'px';
        m.style.top = y + 'px';
        items.forEach((it) => {
          if (it.sep) {
            const s = document.createElement('div');
            s.className = 'ec-ctxsep';
            m.appendChild(s);
            return;
          }
          const el = document.createElement('div');
          el.className = 'ec-ctxitem' + (it.disabled ? ' ec-ctxdisabled' : '');
          el.textContent = it.label;
          if (it.tooltip) el.title = it.tooltip;
          if (!it.disabled && it.onclick) {
            el.addEventListener('click', (ev) => {
              ev.stopPropagation();
              hideMenu();
              it.onclick();
            });
          }
          m.appendChild(el);
        });
        document.body.appendChild(m);
        // Keep on-screen.
        const rect = m.getBoundingClientRect();
        if (rect.right > window.innerWidth) {
          m.style.left = Math.max(0, window.innerWidth - rect.width - 4) + 'px';
        }
        if (rect.bottom > window.innerHeight) {
          m.style.top = Math.max(0, window.innerHeight - rect.height - 4) + 'px';
        }
      }
      // Selection range state machine: returns
      //   {kind:'single', codepos, side, uncertain}
      //   {kind:'range', side, path, cpos1Start, cpos1End, anyUncertain}
      //   {kind:'range-invalid', reason}
      //   null
      function currentSelection() {
        if (!anchor) return null;
        const aCp = decodeCodepos(anchor);
        if (!aCp) return null;
        const aSide = anchor.dataset.side || 'none';
        const aUnc = anchor.dataset.codeposUncertain === '1';
        if (!extent) {
          return { kind: 'single', codepos: aCp, side: aSide, uncertain: aUnc };
        }
        const eCp = decodeCodepos(extent);
        const eSide = extent.dataset.side || 'none';
        if (aSide !== eSide) return { kind: 'range-invalid', reason: 'different sides' };
        if (!eCp) return { kind: 'range-invalid', reason: 'bad codepos' };
        if (!pathEq(aCp.path, eCp.path)) return { kind: 'range-invalid', reason: 'different nesting paths' };
        const eUnc = extent.dataset.codeposUncertain === '1';
        const lo = Math.min(aCp.cpos1, eCp.cpos1);
        const hi = Math.max(aCp.cpos1, eCp.cpos1);
        return { kind: 'range', side: aSide, path: aCp.path,
                 cpos1Start: lo, cpos1End: hi,
                 anyUncertain: aUnc || eUnc };
      }
      function buildContextMenuItems(sel) {
        const items = [];
        if (!sel) {
          items.push({ label: '(no selection)', disabled: true });
          return items;
        }
        if (sel.kind === 'single') {
          const labelN = sel.codepos.cpos1;
          if (sel.uncertain) {
            items.push({ label: 'Rewrite at line ' + labelN,
                         disabled: true,
                         tooltip: 'Match-arm addressing not yet supported (UPSTREAM #24 amendment)' });
            items.push({ label: 'Change at line ' + labelN,
                         disabled: true,
                         tooltip: 'Match-arm addressing not yet supported' });
          } else {
            items.push({ label: 'Rewrite at line ' + labelN,
                         onclick: () => vscode.postMessage({
                           cmd: 'procRewrite',
                           side: sel.side, codepos: sel.codepos }) });
            items.push({ label: 'Change at line ' + labelN,
                         onclick: () => vscode.postMessage({
                           cmd: 'procChange',
                           side: sel.side, codepos: sel.codepos,
                           cpos1End: sel.codepos.cpos1 }) });
          }
        } else if (sel.kind === 'range') {
          const lbl = sel.cpos1Start + '..' + sel.cpos1End;
          if (sel.anyUncertain) {
            items.push({ label: 'Change range ' + lbl,
                         disabled: true,
                         tooltip: 'Match-arm addressing not yet supported' });
          } else {
            items.push({ label: 'Change range ' + lbl,
                         onclick: () => vscode.postMessage({
                           cmd: 'procChange',
                           side: sel.side,
                           codepos: { path: sel.path, cpos1: sel.cpos1Start },
                           cpos1End: sel.cpos1End }) });
          }
        } else if (sel.kind === 'range-invalid') {
          items.push({ label: 'Range invalid (' + sel.reason + ')', disabled: true });
        }
        items.push({ sep: true });
        items.push({ label: 'Clear selection', onclick: clearSelection });
        return items;
      }
      document.addEventListener('click', (e) => {
        const r = rowFromTarget(e.target);
        if (!r) {
          if (!e.target.closest('#ec-ctxmenu')) clearSelection();
          return;
        }
        if (e.shiftKey && anchor) {
          extent = r;
        } else {
          anchor = r; extent = null;
        }
        applySelectionVisual();
        hideMenu();
      });
      document.addEventListener('contextmenu', (e) => {
        const r = rowFromTarget(e.target);
        if (!r) return;
        e.preventDefault();
        // If user right-clicks an unselected row, lock single
        // selection on it first.
        if (!anchor || rowKey(anchor) !== rowKey(r)) {
          if (!extent || !document.querySelectorAll('.ec-selected').length) {
            anchor = r; extent = null;
            applySelectionVisual();
          }
        }
        const sel = currentSelection();
        showMenu(e.clientX, e.clientY, buildContextMenuItems(sel));
      });
      document.addEventListener('keydown', (e) => {
        if (e.key === 'Escape') clearSelection();
      });
    })();
  </script>`;
  return `<!DOCTYPE html><html><head><style>${styles}</style></head>
<body>${header}${subgoalHtml}${navHint}${selectionScript}</body></html>`;
}

// Render the comparison view: top section is the current goal
// (unchanged — apply is speculative); bottom section is one of three
// colored boxes:
//   - 'success'  green box, "+ N subgoals" + first new subgoal +
//                cycle controls (next/prev, "subgoal i of N")
//   - 'closed'   gold box, "✓ closes the focused goal" (no nav)
//   - 'error'    red box, "does not apply" + err text
// Cycle buttons post messages back to the extension; the message
// handler updates cycleIndex on the preview entry and re-renders.
async function renderComparisonHtml(
  uri: string,
  topGoals: GoalsResponse | null,
  badge: string,
  outcome: ComparisonOutcome,
): Promise<string> {
  const bottomBlock = await renderComparisonBottom(badge, outcome);
  const bottomStyles = `
    .cmp-section {
      margin-top: 1.5em;
      border-top: 1px dashed var(--vscode-panel-border);
      padding-top: 1em;
      max-height: 50vh;
      overflow: auto;
      box-sizing: border-box;
    }
    .cmp-header {
      font-weight: bold;
      margin-bottom: 0.5em;
    }
    .cmp-success-box {
      border-left: 3px solid var(--vscode-charts-green, #89d185);
      background: rgba(137, 209, 133, 0.08);
      padding: 0.5em 0.75em;
    }
    .cmp-success-box .cmp-header { color: var(--vscode-charts-green, #89d185); }
    .cmp-closed-box {
      border-left: 3px solid var(--vscode-charts-yellow, #d6c200);
      background: rgba(214, 194, 0, 0.08);
      padding: 0.5em 0.75em;
    }
    .cmp-closed-box .cmp-header { color: var(--vscode-charts-yellow, #d6c200); }
    .cmp-error-box {
      border-left: 3px solid var(--vscode-errorForeground, #f48771);
      background: var(--vscode-inputValidation-errorBackground, transparent);
      padding: 0.5em 0.75em;
    }
    .cmp-error-box .cmp-header { color: var(--vscode-errorForeground, #f48771); }
    .cmp-needs-args-box {
      /* Lighter, warmer amber than charts-orange — inviting "you're
         on the right track, just specify more" rather than the muted
         warning tone. Sits between the bold success-green and gold-
         yellow visually without competing with either. */
      border-left: 3px solid var(--vscode-list-warningForeground, #f0b461);
      background: rgba(240, 180, 97, 0.14);
      padding: 0.5em 0.75em;
    }
    .cmp-needs-args-box .cmp-header {
      color: var(--vscode-list-warningForeground, #f0b461);
    }
    .cmp-needs-args-hint {
      color: var(--vscode-foreground);
      font-size: 0.9em;
      margin: 0.25em 0 0.5em 0;
      line-height: 1.4;
    }
    .cmp-needs-args-hint code {
      background: var(--vscode-textCodeBlock-background, rgba(127,127,127,0.15));
      padding: 0 0.25em;
      border-radius: 2px;
      font-family: var(--vscode-editor-font-family, monospace);
    }
    .cmp-error-text {
      white-space: pre-wrap;
      font-family: var(--vscode-editor-font-family, monospace);
      max-height: 30vh;
      overflow: auto;
    }
    .cmp-error-label {
      color: var(--vscode-errorForeground, #f48771);
      font-weight: bold;
      margin-right: 0.4em;
    }
    /* Bound long content in the success-box's subgoal display too —
       large new goals shouldn't blow the panel height up. */
    .cmp-subgoal-header { margin: 0.25em 0; font-weight: bold;
      color: var(--vscode-textLink-foreground); }
    .cmp-success-box .cmp-conclusion,
    .cmp-success-box .cmp-pp { max-height: 30vh; overflow: auto; }
    .cmp-nav {
      display: flex;
      gap: 0.5em;
      align-items: center;
      margin: 0.5em 0;
      font-size: 0.85em;
      color: var(--vscode-descriptionForeground);
    }
    .cmp-nav button {
      background: var(--vscode-button-secondaryBackground, var(--vscode-button-background));
      color: var(--vscode-button-secondaryForeground, var(--vscode-button-foreground));
      border: none;
      padding: 0.15em 0.6em;
      cursor: pointer;
      border-radius: 3px;
      font-size: 0.95em;
    }
    .cmp-nav button:hover {
      background: var(--vscode-button-secondaryHoverBackground, var(--vscode-button-hoverBackground));
    }
    .cmp-subgoal-header {
      font-weight: bold;
      color: var(--vscode-textLink-foreground);
      margin: 0.25em 0;
    }
    .cmp-hyp { margin-left: 1em; }
    .cmp-hyp-name { font-weight: bold; }
    .cmp-hyp-kind {
      color: var(--vscode-descriptionForeground);
      font-size: 0.85em;
      margin-right: 0.5em;
    }
    .cmp-conclusion {
      border-top: 1px dashed var(--vscode-descriptionForeground);
      margin-top: 0.5em;
      padding-top: 0.5em;
      white-space: pre-wrap;
    }
    .cmp-pp { white-space: pre-wrap; }
    .cmp-empty {
      color: var(--vscode-descriptionForeground);
      font-style: italic;
    }
  `;
  const wireScript = `<script>
    const vscode = acquireVsCodeApi();
    function cycle(delta) { vscode.postMessage({ cmd: 'comparisonCycle', delta }); }
  </script>`;
  if (topGoals === null) {
    // No live goals (fetch failed or pre-proof). Still show the
    // comparison block standalone.
    return `<!DOCTYPE html><html><head><style>
      body {
        font-family: var(--vscode-editor-font-family, monospace);
        font-size: var(--vscode-editor-font-size, 13px);
        color: var(--vscode-editor-foreground);
        background: var(--vscode-editor-background);
        padding: 0.5em 1em;
      }
      ${bottomStyles}
    </style></head><body>${bottomBlock}${wireScript}</body></html>`;
  }
  const idx = pickDisplayIndex(uri, topGoals);
  const goalsHtml = await renderGoalsHtml(topGoals, idx);
  return goalsHtml
    .replace('</style>', `${bottomStyles}</style>`)
    .replace('</body>', `${bottomBlock}${wireScript}</body>`);
}

// Pair preview — top: live goal (same as comparison view); bottom:
// TWO outcome blocks stacked, each with its own label header. Used
// by the rewrite-lemma picker on first hover so the user can see
// forward + backward results side by side.
//
// Cycle controls are intentionally absent here — pair view is a
// peek; users drill into the direction picker (stage 3) for the
// full single-outcome view with cycle support.
async function renderPairHtml(
  uri: string,
  topGoals: GoalsResponse | null,
  badge: string,
  label1: string, outcome1: ComparisonOutcome,
  label2: string, outcome2: ComparisonOutcome,
): Promise<string> {
  // Reuse the existing comparison-bottom renderer but with empty
  // badge inside (we surface the per-direction label as a header
  // wrapping each block).
  const block1 = await renderComparisonBottom(label1, outcome1);
  const block2 = await renderComparisonBottom(label2, outcome2);
  const bottomBlock =
    `<div class="cmp-pair-header">${escapeHtml(badge)}</div>` +
    `<div class="cmp-pair-block">${block1}</div>` +
    `<div class="cmp-pair-block">${block2}</div>`;
  // Reuse the same styles as renderComparisonHtml (cmp-* classes).
  // Add a tiny pair-specific wrapper.
  const pairStyles = `
    .cmp-pair-header {
      font-weight: bold;
      color: var(--vscode-textLink-foreground);
      margin: 1em 0 0.25em 0;
      padding-top: 0.5em;
      border-top: 1px dashed var(--vscode-panel-border);
    }
    .cmp-pair-block { margin-bottom: 0.75em; }
    /* Trim the per-block margin-top so the two blocks pack tighter. */
    .cmp-pair-block .cmp-section { margin-top: 0.5em; }
  `;
  const wireScript = `<script>
    const vscode = acquireVsCodeApi();
    function cycle(delta) { vscode.postMessage({ cmd: 'comparisonCycle', delta }); }
  </script>`;
  // Reuse all comparison styles (lazy: re-render comparison shell
  // once with a no-op outcome to extract the style block — but
  // simpler to just inline a minimal style sheet that covers what
  // renderComparisonBottom emits).
  const sharedStyles = `
    body {
      font-family: var(--vscode-editor-font-family, monospace);
      font-size: var(--vscode-editor-font-size, 13px);
      color: var(--vscode-editor-foreground);
      background: var(--vscode-editor-background);
      padding: 0.5em 1em;
    }
    .cmp-section {
      margin-top: 0.5em;
      border-top: 1px dashed var(--vscode-panel-border);
      padding-top: 0.5em;
      max-height: 40vh;
      overflow: auto;
    }
    .cmp-header { font-weight: bold; margin-bottom: 0.5em; }
    .cmp-success-box {
      border-left: 3px solid var(--vscode-charts-green, #89d185);
      background: rgba(137, 209, 133, 0.08); padding: 0.5em 0.75em;
    }
    .cmp-success-box .cmp-header { color: var(--vscode-charts-green, #89d185); }
    .cmp-closed-box {
      border-left: 3px solid var(--vscode-charts-yellow, #d6c200);
      background: rgba(214, 194, 0, 0.08); padding: 0.5em 0.75em;
    }
    .cmp-closed-box .cmp-header { color: var(--vscode-charts-yellow, #d6c200); }
    .cmp-error-box {
      border-left: 3px solid var(--vscode-errorForeground, #f48771);
      background: var(--vscode-inputValidation-errorBackground, transparent);
      padding: 0.5em 0.75em;
    }
    .cmp-error-box .cmp-header { color: var(--vscode-errorForeground, #f48771); }
    .cmp-needs-args-box {
      border-left: 3px solid var(--vscode-list-warningForeground, #f0b461);
      background: rgba(240, 180, 97, 0.14); padding: 0.5em 0.75em;
    }
    .cmp-needs-args-box .cmp-header {
      color: var(--vscode-list-warningForeground, #f0b461);
    }
    .cmp-needs-args-hint {
      color: var(--vscode-foreground); font-size: 0.9em;
      margin: 0.25em 0 0.5em 0; line-height: 1.4;
    }
    .cmp-error-text {
      white-space: pre-wrap;
      font-family: var(--vscode-editor-font-family, monospace);
      max-height: 25vh; overflow: auto;
    }
    .cmp-error-label {
      color: var(--vscode-errorForeground, #f48771);
      font-weight: bold; margin-right: 0.4em;
    }
    .cmp-subgoal-header {
      font-weight: bold; color: var(--vscode-textLink-foreground);
      margin: 0.25em 0;
    }
    .cmp-success-box .cmp-conclusion,
    .cmp-success-box .cmp-pp { max-height: 25vh; overflow: auto; }
    .cmp-hyp { margin-left: 1em; }
    .cmp-hyp-name { font-weight: bold; }
    .cmp-hyp-kind {
      color: var(--vscode-descriptionForeground);
      font-size: 0.85em; margin-right: 0.5em;
    }
    .cmp-pp { white-space: pre-wrap; }
    .cmp-empty {
      color: var(--vscode-descriptionForeground);
      font-style: italic;
    }
    ${pairStyles}
  `;
  if (topGoals === null) {
    return `<!DOCTYPE html><html><head><style>${sharedStyles}</style></head>` +
           `<body>${bottomBlock}${wireScript}</body></html>`;
  }
  const idx = pickDisplayIndex(uri, topGoals);
  const goalsHtml = await renderGoalsHtml(topGoals, idx);
  return goalsHtml
    .replace('</style>', `${sharedStyles}</style>`)
    .replace('</body>', `${bottomBlock}${wireScript}</body>`);
}

async function renderComparisonBottom(badge: string, outcome: ComparisonOutcome): Promise<string> {
  if (outcome.kind === 'error') {
    if (outcome.errorKind === 'needs-args') {
      // Amber box: lemma matches structurally but needs explicit args.
      // Suggest refine-args path.
      return `
        <div class="cmp-section cmp-needs-args-box">
          <div class="cmp-header">⚠ ${escapeHtml(badge)} — needs explicit args</div>
          <div class="cmp-needs-args-hint">EC could not infer all unification variables from the goal. Press Shift+Enter (or 🔧 in the picker title bar) to refine args incrementally — supply terms or <code>_</code> wildcards for the unspecified positions.</div>
          <div class="cmp-error-text"><span class="cmp-error-label">detail:</span>${escapeHtml(outcome.error)}</div>
        </div>`;
    }
    return `
      <div class="cmp-section cmp-error-box">
        <div class="cmp-header">${escapeHtml(badge)}</div>
        <div class="cmp-error-text"><span class="cmp-error-label">error:</span>${escapeHtml(outcome.error)}</div>
      </div>`;
  }
  // success
  if (outcome.closedFocused && outcome.newGoals.subgoal_count === 0) {
    return `
      <div class="cmp-section cmp-closed-box">
        <div class="cmp-header">✓ ${escapeHtml(badge)} — closes the focused goal</div>
      </div>`;
  }
  // Display ONE subgoal (cycleIndex), with nav controls if more than 1.
  const total = outcome.newGoals.subgoal_count;
  const idx =
    total === 0 ? 0 : ((outcome.cycleIndex % total) + total) % total;
  const closedBadge =
    outcome.closedFocused
      ? ' · ✓ also closes the focused goal'
      : '';
  let nav = '';
  if (total > 1) {
    // Buttons stay for visual cue / mouse use AFTER picker is
    // accepted. While the picker is open, focus loss closes it —
    // user must use the keybinds (Cmd/Ctrl+Alt+] / [) which fire
    // VSCode commands gated on the easycrypt.lemmaPickerOpen
    // context. Tooltip steers users toward the right path.
    nav = `
      <div class="cmp-nav">
        <button onclick="cycle(-1)" title="Previous (Cmd/Ctrl+Alt+[ keeps picker open)">◀</button>
        <button onclick="cycle(+1)" title="Next (Cmd/Ctrl+Alt+] keeps picker open)">▶</button>
        <span>subgoal ${idx + 1} of ${total} · Cmd/Ctrl+Alt+]/[ to cycle</span>
      </div>`;
  } else if (total === 1) {
    nav = `<div class="cmp-nav"><span>1 subgoal</span></div>`;
  }
  let subgoalHtml = '';
  if (total === 0) {
    subgoalHtml = '<div class="cmp-empty">no new subgoals</div>';
  } else {
    const sg = outcome.newGoals.subgoals[idx] ?? outcome.newGoals.subgoals[0];
    if (!sg) {
      subgoalHtml = '<div class="cmp-empty">(subgoal not in payload)</div>';
    } else {
      const hyps =
        sg.hypotheses.length === 0
          ? '<div class="cmp-empty cmp-hyp">(no hypotheses)</div>'
          : sg.hypotheses
              .map(
                (h) =>
                  `<div class="cmp-hyp"><span class="cmp-hyp-kind">[${escapeHtml(h.kind)}]</span>` +
                  `<span class="cmp-hyp-name">${escapeHtml(h.name)}</span>` +
                  ` : <span class="cmp-pp">${escapeHtml(h.pp)}</span></div>`,
              )
              .join('\n');
      subgoalHtml = `
        <div class="cmp-subgoal-header">subgoal ${sg.index + 1}</div>
        ${hyps}
        <div class="cmp-conclusion">${sg.conclusion.kind === 'pp' ? '⊢ ' : ''}${await renderConclusion(sg.conclusion)}</div>`;
    }
  }
  return `
    <div class="cmp-section cmp-success-box">
      <div class="cmp-header">✓ ${escapeHtml(badge)} — ${total} subgoal${total === 1 ? '' : 's'}${closedBadge}</div>
      ${nav}
      ${subgoalHtml}
    </div>`;
}

function ensureGoalsPanel(): vscode.WebviewPanel {
  if (goalsPanel) {
    goalsPanel.reveal(vscode.ViewColumn.Beside, /* preserveFocus */ true);
    return goalsPanel;
  }
  const panel = vscode.window.createWebviewPanel(
    'easycrypt.goals',
    'EasyCrypt Goals',
    { viewColumn: vscode.ViewColumn.Beside, preserveFocus: true },
    {
      retainContextWhenHidden: true,
      // Comparison view's cycle controls (next/prev subgoal) need
      // postMessage. Sandboxed iframe; only message handler below
      // can reach the extension.
      enableScripts: true,
    },
  );
  panel.onDidDispose(() => {
    goalsPanel = undefined;
    goalsForUri = undefined;
  });
  panel.webview.onDidReceiveMessage(async (msg) => {
    if (!msg) return;
    if (msg.cmd === 'comparisonCycle') {
      if (typeof msg.delta !== 'number') return;
      compareCycleActive(msg.delta);
      return;
    }
    if (msg.cmd === 'procRewrite' || msg.cmd === 'procChange') {
      // Right-clicking inside the goal pane webview makes the
      // webview the active text editor, so [activeEcEditor] would
      // warn "no .ec editor active". Look up the editor for the
      // URI bound to this goal pane instead; fall back to any
      // visible .ec editor.
      const uri = goalsForUri ?? activeEcEditor()?.document.uri.toString();
      if (!uri) {
        vscode.window.showWarningMessage(
          'EasyCrypt: no .ec document bound to the goal pane.',
        );
        return;
      }
      const editor =
        vscode.window.visibleTextEditors.find(
          e => e.document.uri.toString() === uri,
        )
        ?? vscode.window.visibleTextEditors.find(
          e => e.document.languageId === 'easycrypt',
        );
      if (!editor) {
        vscode.window.showWarningMessage(
          'EasyCrypt: no visible .ec editor for ' + uri + '.',
        );
        return;
      }
      const insertPosition = editor.selection.active;
      if (msg.cmd === 'procRewrite') {
        await runProcRewrite({
          uri,
          insertPosition,
          side: msg.side as MsgProgSide,
          codepos: msg.codepos as MsgCodepos,
          editor,
        });
        return;
      }
      // procChange
      const cp = msg.codepos as MsgCodepos;
      const cpos1End = typeof msg.cpos1End === 'number' ? msg.cpos1End : cp.cpos1;
      const rangeLabel = cpos1End === cp.cpos1
        ? cp.cpos1.toString()
        : `${cp.cpos1}..${cpos1End}`;
      // Old-code lines: not yet wired; webview can pass them in a
      // future revision. For v1 we leave it empty (popup shows the
      // line label only) — the user already sees the old code in
      // the goal pane behind/beside the popup.
      await runProcChange({
        uri,
        insertPosition,
        side: msg.side as MsgProgSide,
        codepos: cp,
        cpos1End,
        oldCodeLines: [],
        rangeLabel,
        editor,
      });
      return;
    }
  });
  goalsPanel = panel;
  return panel;
}

// Set when the lemma picker is open and a context-gated keybind /
// button click should hand off to phase-3. The active picker writes
// its handler here on show; clears on hide. Reentrancy: only one
// picker open at a time (asserted by the singleton context).
let activeLemmaPickerRefineHandler: (() => void) | undefined;

// Shared mutator: shift the comparison preview's cycleIndex by delta
// and re-render. Used by both the in-webview button (postMessage path)
// and the editor-keybind commands (context-gated, fire while picker
// has focus). Returns true when something was cycled.
function compareCycleActive(delta: number): boolean {
  if (!goalsForUri) return false;
  const preview = goalsPreview.get(goalsForUri);
  if (!preview || preview.kind !== 'comparison') return false;
  if (preview.outcome.kind !== 'success') return false;
  preview.outcome.cycleIndex = preview.outcome.cycleIndex + delta;
  renderPreview(goalsForUri, preview);
  return true;
}

function renderPreview(uri: string, preview: GoalsPreview): void {
  if (!goalsPanel) return;
  // Async render with fire-and-forget html assignment. Re-checks
  // panel + uri ownership after await in case races change them.
  void (async () => {
    let html: string;
    if (preview.kind === 'goals') {
      const idx = pickDisplayIndex(uri, preview.goals);
      html = await renderGoalsHtml(preview.goals, idx, preview.badge);
    } else if (preview.kind === 'pair') {
      html = await renderPairHtml(
        uri, preview.topGoals, preview.badge,
        preview.label1, preview.outcome1,
        preview.label2, preview.outcome2,
      );
    } else {
      html = await renderComparisonHtml(
        uri, preview.topGoals, preview.badge, preview.outcome,
      );
    }
    if (goalsPanel && (goalsForUri === undefined || goalsForUri === uri)) {
      goalsPanel.webview.html = html;
    }
  })();
}

async function fetchAndRenderGoals(uri: string): Promise<void> {
  if (!goalsPanel) return;
  goalsForUri = uri;
  // Preview override (set by builder / lemma picker) wins over a
  // live fetch. Builders push the speculative post-tactic state
  // here directly so the goal pane reflects intent without a
  // round-trip.
  const preview = goalsPreview.get(uri);
  if (preview) {
    renderPreview(uri, preview);
    return;
  }
  const result = await withClient(c =>
    c.sendRequest<GoalsResponse>('easycrypt/proof/goals', { uri }),
  );
  if (!goalsPanel) return;  // closed while awaiting
  // Race: a builder/picker may have pushed a preview while we were
  // awaiting the live goals. Re-check before overwriting — preview
  // wins.
  const previewLate = goalsPreview.get(uri);
  if (previewLate) {
    renderPreview(uri, previewLate);
    return;
  }
  if (result === undefined) {
    goalsPanel.webview.html =
      '<html><body><pre>error fetching goals — see daemon logs</pre></body></html>';
    return;
  }
  const displayIndex = pickDisplayIndex(uri, result);
  const html = await renderGoalsHtml(result, displayIndex);
  if (goalsPanel && goalsForUri === uri) {
    goalsPanel.webview.html = html;
  }
}

// Cycle the displayed subgoal in the goal pane by [delta] (+1 next,
// -1 prev). Reads goalsCursor to know the current display index;
// computes the new pinned index modulo subgoal_count; stores it;
// re-renders. Falls through to a no-op when there's nothing
// meaningful to cycle (zero or one subgoal, no goal pane open, no
// active EC editor).
async function cycleSubgoal(delta: number): Promise<void> {
  const editor = activeEcEditor();
  if (!editor) return;
  if (!goalsPanel) {
    // Open the pane if cycling is invoked without one — friendlier
    // UX than silently doing nothing.
    ensureGoalsPanel();
  }
  const uri = editor.document.uri.toString();
  // Fetch fresh to know subgoal_count + EC focus. Cheap (cached in
  // Phase 5.0; just an LSP round-trip today).
  const result = await withClient(c =>
    c.sendRequest<GoalsResponse>('easycrypt/proof/goals', { uri }),
  );
  if (!result) return;
  if (result.subgoal_count <= 1) {
    // Nothing to cycle. Refresh the pane (in case it's stale) and
    // return.
    if (goalsPanel) {
      const displayIndex = pickDisplayIndex(uri, result);
      const html = await renderGoalsHtml(result, displayIndex);
      if (goalsPanel) goalsPanel.webview.html = html;
    }
    return;
  }
  const cur = pickDisplayIndex(uri, result);
  const next =
    ((cur + delta) % result.subgoal_count + result.subgoal_count) %
    result.subgoal_count;
  goalsCursor.set(uri, next);
  if (goalsPanel) {
    const html = await renderGoalsHtml(result, next);
    if (goalsPanel) goalsPanel.webview.html = html;
  }
}

async function handleCycleSubgoalNext(): Promise<void> {
  await cycleSubgoal(+1);
}

async function handleCycleSubgoalPrev(): Promise<void> {
  await cycleSubgoal(-1);
}

function scheduleGoalsRefresh(uri: string): void {
  if (!goalsPanel) return;
  if (goalsRefreshTimer) clearTimeout(goalsRefreshTimer);
  goalsRefreshTimer = setTimeout(() => {
    goalsRefreshTimer = undefined;
    void fetchAndRenderGoals(uri);
  }, 50);
}

async function handleShowGoals(): Promise<void> {
  const editor = activeEcEditor();
  if (!editor) {
    return;
  }
  ensureGoalsPanel();
  await fetchAndRenderGoals(editor.document.uri.toString());
}

// Per-uri navigation state. Two independent intent slots:
//
//   pendingGoto: a position target set by clicks (gotoCursor /
//                revertToCursor). Daemon resolves to nearest
//                sentence boundary via execToPoint / revertToPoint.
//                Coalescing: latest goto wins (fast click A then B
//                before A finishes — A runs, B fires next).
//
//   pendingStepDelta: a signed sentence-count delta set by
//                step / back keypresses. Daemon's sentence-aware
//                step / back count primitives execute it. Using
//                line-based approximation here used to confuse
//                the daemon: a "1 line back" target inside a
//                multi-line sentence resolved to the SAME sentence
//                (no-op), so Cmd+Opt+P silently did nothing.
//
//   inFlight: at most one request in flight per uri.
//
// Visual amber paints from locked → projected target, where the
// projected target is computed from whichever intent slot is set
// (goto wins if both set). approxLineBump is used for the visual
// projection only — daemon corrects via stateChanged. The amber
// shows the user their accumulated intent regardless of in-flight
// state.

interface NavState {
  pendingGoto: Position | null;
  pendingStepDelta: number;
  inFlight: boolean;
  lastFiredGoto: Position | null;
}

const navState = new Map<string, NavState>();

function getNav(uri: string): NavState {
  let s = navState.get(uri);
  if (!s) {
    s = {
      pendingGoto: null,
      pendingStepDelta: 0,
      inFlight: false,
      lastFiredGoto: null,
    };
    navState.set(uri, s);
  }
  return s;
}

// Approximate "next/previous sentence" by advancing one logical
// line. Used only for the VISUAL amber projection — daemon
// corrects to actual sentence boundary via stateChanged.
function approxLineBump(
  editor: vscode.TextEditor,
  start: Position,
  delta: number,
): Position {
  const doc = editor.document;
  let line = start.line + delta;
  const last = doc.lineCount - 1;
  if (line < 0) line = 0;
  if (line > last) line = last;
  const text = doc.lineAt(line).text;
  return { line, character: Math.min(start.character, text.length) };
}

// Recompute and paint the queued amber based on current nav state.
// Pendinging goto wins if both slots are set. Step delta projects
// from locked tip line-approximately.
function refreshQueuedFromNav(uri: string): void {
  const s = getNav(uri);
  if (s.pendingGoto !== null) {
    setQueued(uri, s.pendingGoto);
    return;
  }
  if (s.pendingStepDelta !== 0) {
    const locked = lockedEnd.get(uri) ?? { line: 0, character: 0 };
    const editor = vscode.window.visibleTextEditors.find(
      e => e.document.uri.toString() === uri,
    );
    if (editor) {
      setQueued(uri, approxLineBump(editor, locked, s.pendingStepDelta));
      return;
    }
  }
  clearQueued(uri);
}

// Show step/back/exec failures as a red error toast. The daemon's
// recoveryStrategy="halt" stops at the first failing sentence and
// the locked region reflects the last GOOD sentence — so user
// state isn't corrupted, just paused.
function surfaceDiagnostics(method: string, raw: unknown): void {
  if (raw === null || typeof raw !== 'object') return;
  const r = raw as { diagnostics?: Array<{ detail?: string; code?: string }> };
  const diags = r.diagnostics;
  if (!diags || diags.length === 0) return;
  const first = diags[0];
  const detail = (first.detail ?? 'unknown error').trim();
  const code = first.code ?? '';
  vscode.window.showErrorMessage(
    `${method} failed${code ? ` (${code})` : ''}: ${detail} — ` +
      `stopped before failing sentence; locked region preserved.`,
  );
}

async function driveNav(uri: string): Promise<void> {
  const s = getNav(uri);
  if (s.inFlight) return;
  while (true) {
    // Pendinging goto takes priority; reaching it consumes both
    // slots (clicking explicitly overrides any pending step delta).
    if (s.pendingGoto !== null) {
      const target = s.pendingGoto;
      const locked = lockedEnd.get(uri) ?? null;
      if (locked !== null && comparePositions(target, locked) === 0) {
        s.pendingGoto = null;
        refreshQueuedFromNav(uri);
        continue;
      }
      const goingForward =
        locked === null || comparePositions(target, locked) > 0;
      s.inFlight = true;
      s.lastFiredGoto = target;
      let response: unknown = null;
      let method = goingForward ? 'execToPoint' : 'revertToPoint';
      try {
        response = await withClient(c =>
          c.sendRequest<unknown>(`easycrypt/proof/${method}`, {
            uri,
            target: { position: target },
            expectedCas: null,
            ...(goingForward
              ? { recoveryStrategy: 'halt', cachePolicy: null }
              : {}),
          }),
        );
      } catch (err) {
        const msg = err instanceof Error ? err.message : String(err);
        vscode.window.showErrorMessage(`${method} request failed: ${msg}`);
        s.inFlight = false;
        s.pendingGoto = null;
        s.lastFiredGoto = null;
        refreshQueuedFromNav(uri);
        return;
      }
      s.inFlight = false;
      surfaceDiagnostics(method, response);
      if (
        s.pendingGoto !== null &&
        s.lastFiredGoto !== null &&
        comparePositions(s.pendingGoto, s.lastFiredGoto) === 0
      ) {
        s.pendingGoto = null;
      }
      s.lastFiredGoto = null;
      refreshQueuedFromNav(uri);
      continue;
    }
    if (s.pendingStepDelta > 0) {
      const count = s.pendingStepDelta;
      s.pendingStepDelta = 0;
      s.inFlight = true;
      let response: unknown = null;
      try {
        response = await withClient(c =>
          c.sendRequest<unknown>('easycrypt/proof/step', { uri, count }),
        );
      } catch (err) {
        const msg = err instanceof Error ? err.message : String(err);
        vscode.window.showErrorMessage(`step request failed: ${msg}`);
        s.inFlight = false;
        s.pendingStepDelta = 0;
        refreshQueuedFromNav(uri);
        return;
      }
      s.inFlight = false;
      surfaceDiagnostics('step', response);
      refreshQueuedFromNav(uri);
      continue;
    }
    if (s.pendingStepDelta < 0) {
      const count = -s.pendingStepDelta;
      s.pendingStepDelta = 0;
      s.inFlight = true;
      let response: unknown = null;
      try {
        response = await withClient(c =>
          c.sendRequest<unknown>('easycrypt/proof/back', { uri, count }),
        );
      } catch (err) {
        const msg = err instanceof Error ? err.message : String(err);
        vscode.window.showErrorMessage(`back request failed: ${msg}`);
        s.inFlight = false;
        s.pendingStepDelta = 0;
        refreshQueuedFromNav(uri);
        return;
      }
      s.inFlight = false;
      surfaceDiagnostics('back', response);
      refreshQueuedFromNav(uri);
      continue;
    }
    // Both slots empty — done.
    refreshQueuedFromNav(uri);
    return;
  }
}

// Auto-open the goal pane on navigation (step / back / exec-to-cursor /
// revert-to-cursor). User intent: "I'm proving — show me goals." Pane
// updates reactively via stateChanged once the response settles; an
// initial fetchAndRenderGoals shows whatever the current state is so
// the pane isn't blank until the request returns.
function autoOpenGoalsForNav(uri: string): void {
  ensureGoalsPanel();
  void fetchAndRenderGoals(uri);
}

async function handleGotoCursor(): Promise<void> {
  const editor = activeEcEditor();
  if (!editor) return;
  const uri = editor.document.uri.toString();
  autoOpenGoalsForNav(uri);
  const s = getNav(uri);
  s.pendingGoto = {
    line: editor.selection.active.line,
    character: editor.selection.active.character,
  };
  // A fresh click overrides any accumulated step intent.
  s.pendingStepDelta = 0;
  refreshQueuedFromNav(uri);
  await driveNav(uri);
}

async function handleStep(): Promise<void> {
  const editor = activeEcEditor();
  if (!editor) return;
  const uri = editor.document.uri.toString();
  autoOpenGoalsForNav(uri);
  const s = getNav(uri);
  s.pendingStepDelta += 1;
  refreshQueuedFromNav(uri);
  await driveNav(uri);
}

async function handleBack(): Promise<void> {
  const editor = activeEcEditor();
  if (!editor) return;
  const uri = editor.document.uri.toString();
  autoOpenGoalsForNav(uri);
  const s = getNav(uri);
  s.pendingStepDelta -= 1;
  refreshQueuedFromNav(uri);
  await driveNav(uri);
}

async function handleRevertToCursor(): Promise<void> {
  const editor = activeEcEditor();
  if (!editor) return;
  const uri = editor.document.uri.toString();
  autoOpenGoalsForNav(uri);
  const s = getNav(uri);
  s.pendingGoto = {
    line: editor.selection.active.line,
    character: editor.selection.active.character,
  };
  s.pendingStepDelta = 0;
  refreshQueuedFromNav(uri);
  await driveNav(uri);
}

async function handleProofRestart(): Promise<void> {
  const editor = activeEcEditor();
  if (!editor) return;
  await withClient(c =>
    c.sendRequest<unknown>('easycrypt/proof/restart', {
      uri: editor.document.uri.toString(),
    }),
  );
}

// Beta-1 gate point 4 — `easycrypt.proof.execAll`. Drive the
// daemon's `easycrypt/proof/execAll` to advance to the end of the
// document. Surfaced under a cancellable progress notification —
// the same Cancel button that suggestClosers uses, wired to
// `easycrypt/proof/cancel` so the daemon SIGINTs EC and rolls
// back to the last-executed sentence.
interface ExecAllResponse {
  advancedTo: string | null;
  newCas: string;
  executedSentences: number;
  skippedSentences: number;
  diagnostics: { code: string; phase: string; detail: string }[];
  atEndOfDocument: boolean;
}

async function handleExecAll(): Promise<void> {
  const editor = activeEcEditor();
  if (!editor) return;
  const uri = editor.document.uri.toString();
  let result: ExecAllResponse | undefined;
  try {
    result = await vscode.window.withProgress(
      {
        location: vscode.ProgressLocation.Notification,
        title: 'EasyCrypt: executing to end of document…',
        cancellable: true,
      },
      (_progress, token) => {
        token.onCancellationRequested(() => { void sendCancel(uri); });
        return withClient(c =>
          c.sendRequest<ExecAllResponse>('easycrypt/proof/execAll', { uri }),
        ).then(r => r as ExecAllResponse);
      },
    );
  } catch (err) {
    vscode.window.showInformationMessage(
      `EasyCrypt: ${err instanceof Error ? err.message : String(err)}`,
    );
    return;
  }
  if (!result) return;
  if (result.diagnostics.length > 0) {
    const d = result.diagnostics[0];
    vscode.window.showWarningMessage(
      `EasyCrypt: execAll halted after ${result.executedSentences} sentence(s): ${d.detail}`,
    );
  } else if (result.atEndOfDocument) {
    vscode.window.showInformationMessage(
      `EasyCrypt: executed ${result.executedSentences} sentence(s) to end of document.`,
    );
  }
}

// Beta-1 gate point 4 (other half) — "Focus current goal" command.
// Computes [delta = displayedIndex - currentIndex] and inserts
// `cycle <delta>.` at the cursor. Preserves stock-EC checkability
// of the resulting script (no new tactic; cycle is built-in).
//
// Defer note: an absolute-index focus tactic (`goto N.` /
// `select N.`) would be more robust to subgoal-index churn but
// the `Pfocus` parser symbol is already taken — pinned post-beta
// (UPSTREAM § 27).
async function handleFocusCurrentGoal(): Promise<void> {
  const editor = activeEcEditor();
  if (!editor) return;
  const uri = editor.document.uri.toString();
  const goals = await withClient(c =>
    c.sendRequest<GoalsResponse>('easycrypt/proof/goals', { uri }),
  );
  if (!goals || !goals.active) {
    vscode.window.showWarningMessage('EasyCrypt: no active proof.');
    return;
  }
  const displayed = pickDisplayIndex(uri, goals);
  const current = goals.current_index;
  const delta = displayed - current;
  if (delta === 0) {
    vscode.window.showInformationMessage(
      'EasyCrypt: displayed subgoal already matches EC focus — no cycle needed.',
    );
    return;
  }
  const tactic = `cycle ${delta}.`;
  await editor.edit(b => b.insert(editor.selection.active, tactic + '\n'));
}

// ---- Speculative methods (parity Phase 3) ---------------------------

interface TryTacticResponse {
  outcome: 'ok' | 'err';
  body: string | null;
  goalsAfter: GoalsResponse | null;
  closedFocused: boolean;
  error: string | null;
  newCas: string;
}

// tryTactic — refactored: opens a launcher offering (a) free-text
// (the legacy one-shot InputBox) or (b) any builder schema. Either
// way the result is preview-only — no insert unless the user
// explicitly chooses Insert at the end. Launcher entry first so the
// user can pick a structured builder without committing to a tactic
// shape upfront.
async function handleTryTactic(): Promise<void> {
  const editor = activeEcEditor();
  if (!editor) return;
  // Quick-pick: free-text fallback (top) + every known tactic schema.
  const items: vscode.QuickPickItem[] = [
    {
      label: '$(comment) free text',
      description: 'one-shot text input — try arbitrary tactic',
    },
    ...tacticSchemas.map(s => ({
      label: s.id,
      description: `builder — ${s.label}`,
    })),
  ];
  const picked = await vscode.window.showQuickPick(items, {
    title: 'EasyCrypt: Try Tactic — pick a builder or free-text',
    placeHolder: 'fuzzy filter, ↑/↓ navigate, Enter accepts',
  });
  if (!picked) return;
  if (picked.label === '$(comment) free text') {
    await runTryTacticFreeText(editor);
    return;
  }
  const schema = tacticSchemaById.get(picked.label);
  if (!schema) return;
  // Run the builder; on finalize it will offer insert (existing
  // behavior of runBuilder). For tryTactic-flavored entry the user
  // can finalize and choose insert via the standard commit path.
  await runBuilder({
    uri: editor.document.uri.toString(),
    insertPosition: editor.selection.active,
    schema,
  });
}

// Legacy one-shot tryTactic — preserved as the "free-text fallback"
// inside the launcher. Same behavior as before: enter source, see
// result via showInformationMessage, optional Insert at cursor.
async function runTryTacticFreeText(editor: vscode.TextEditor): Promise<void> {
  const insertPosition = editor.selection.active;
  const source = await vscode.window.showInputBox({
    title: 'EasyCrypt: Try Tactic (free text)',
    prompt:
      'Enter a tactic to try speculatively against the current goal. ' +
      'The primary session is rolled back after the trial.',
    placeHolder: 'reflexivity.',
    ignoreFocusOut: false,
  });
  if (source === undefined) return;
  const trimmed = source.trim();
  if (trimmed === '') return;
  const sourceWithDot = trimmed.endsWith('.') ? trimmed : `${trimmed}.`;
  const result = await withClient(c =>
    c.sendRequest<TryTacticResponse>('easycrypt/proof/tryTactic', {
      uri: editor.document.uri.toString(),
      source: sourceWithDot,
      expectedCas: null,
    }),
  );
  if (!result) return;
  if (result.outcome === 'ok') {
    const action = await vscode.window.showInformationMessage(
      `tryTactic: ${formatTryTacticOk(result)}`,
      'Insert at cursor',
    );
    if (action === 'Insert at cursor') {
      await editor.edit(b => b.insert(insertPosition, sourceWithDot + '\n'));
    }
  } else {
    const detail = (result.error ?? 'unknown error').trim();
    vscode.window.showWarningMessage(`tryTactic failed: ${detail}`);
  }
}

// Render an outcome=ok response: use the daemon's closedFocused
// flag for accurate closer detection (handles multi-subgoal goals
// where the focused subgoal closes but unrelated others remain
// open — checking goalsAfter.subgoal_count === 0 alone misses
// these). Conclusion snippets come from goalsAfter.subgoals when
// available; falls back to body string.
function formatTryTacticOk(result: TryTacticResponse): string {
  if (result.closedFocused) {
    return '★ closes the goal';
  }
  const ga = result.goalsAfter;
  if (ga) {
    const concNode = ga.subgoals[ga.current_index]?.conclusion;
    const conc = concNode ? conclusionToPpText(concNode) : '';
    const snippet =
      conc.length === 0
        ? ''
        : conc.length > 60
        ? conc.slice(0, 57) + '…'
        : conc;
    if (ga.subgoal_count === 1) {
      return snippet === ''
        ? '→ 1 subgoal remains'
        : `→ 1 subgoal remains: ${snippet}`;
    }
    return snippet === ''
      ? `→ ${ga.subgoal_count} subgoals remain`
      : `→ ${ga.subgoal_count} subgoals remain; first: ${snippet}`;
  }
  // Fall back to the body string when goalsAfter wasn't returned
  // (older daemon, or future variant where it's null).
  const body = (result.body ?? '').trim();
  return body === '' ? '✓ tactic ran cleanly' : `✓ ${body}`;
}

interface SuggestRow {
  src: string;
  label: string;
  outcome: 'closes' | 'open' | 'err';
  subgoalCount?: number;
  detail?: string;
}

interface SuggestClosersResponse {
  rows: SuggestRow[];
  newCas: string;
}

interface SuggestQuickPickItem extends vscode.QuickPickItem {
  src: string;
}

function quickPickItemOf(row: SuggestRow): SuggestQuickPickItem {
  let descr: string;
  switch (row.outcome) {
    case 'closes':
      descr = '★ closes the goal';
      break;
    case 'open':
      descr = `→ opens ${row.subgoalCount ?? '?'} subgoal(s)`;
      break;
    case 'err':
      descr = `✗ ${row.detail ?? 'error'}`;
      break;
  }
  return {
    label: row.label,
    description: descr,
    detail: row.src,
    src: row.src,
  };
}

// Stable sort: closes first, opens next, errs last. Preserves input
// order within each bucket. Mirrors Proof_speculation.sort_suggest_rows.
function sortSuggestRows(rows: SuggestRow[]): SuggestRow[] {
  const bucket = (r: SuggestRow): number => {
    switch (r.outcome) {
      case 'closes': return 0;
      case 'open':   return 1;
      case 'err':    return 2;
    }
  };
  // Decorate-sort-undecorate to keep stability.
  return rows
    .map((r, i) => ({ r, i, b: bucket(r) }))
    .sort((a, b) => a.b - b.b || a.i - b.i)
    .map(x => x.r);
}

// UPSTREAM § 25 / doc/cancellation.md C4 — explicit user-initiated
// cancel (Cmd/Ctrl+Alt+. by default + the 'EasyCrypt: Cancel' command
// + the goal-pane Cancel button). Sends easycrypt/proof/cancel; the
// daemon delivers SIGINT to its EC subprocess, which surfaces as a
// 'canceled' error reply on whatever request was in flight (closer
// sweep, tryTactic, execToPoint, ...). The cancel response itself
// returns immediately. Per-request seq correlation is deferred —
// current scope: cancel ALL in-flight work on the connection's
// primary session.
async function sendCancel(uri: string): Promise<boolean> {
  const r = await withClient(c =>
    c.sendRequest<{ canceled: boolean } | undefined>(
      'easycrypt/proof/cancel',
      { uri },
    ),
  );
  return r?.canceled === true;
}

async function handleCancel(): Promise<void> {
  const editor = activeEcEditor();
  if (!editor) return;
  const uri = editor.document.uri.toString();
  const ok = await sendCancel(uri);
  if (!ok) {
    vscode.window.showInformationMessage(
      'EasyCrypt: cancel sent, but daemon did not acknowledge.',
    );
  }
}

// Read [easycrypt-tooling.preview.timeoutMs] (default 3000ms). Used by
// callers that wrap a long-running speculative request and want the
// daemon-side cancel to fire after the budget elapses.
function previewTimeoutMs(): number {
  const cfg = vscode.workspace.getConfiguration('easycrypt-tooling.preview');
  const v = cfg.get<number>('timeoutMs');
  return typeof v === 'number' && v >= 100 ? v : 3000;
}

// Race [call] against the preview timeout. On timeout, dispatch
// proof/cancel for [uri]; the daemon-side request resolves with a
// canceled-style error reply, which the caller handles like any
// other failure. Returns whatever [call] resolved/rejected with —
// the cancel is fire-and-forget on the side.
async function withPreviewTimeout<T>(
  uri: string,
  call: () => Promise<T>,
): Promise<T> {
  const ms = previewTimeoutMs();
  let timer: NodeJS.Timeout | undefined;
  const guard = new Promise<never>((_resolve, reject) => {
    timer = setTimeout(() => {
      // Fire-and-forget: cancel the in-flight tactic on the daemon.
      // The original [call] then rejects/resolves on its own; we
      // surface "preview timeout" so the user knows why the
      // preview disappeared.
      void sendCancel(uri);
      reject(new Error(`preview timeout after ${ms}ms (cancel sent)`));
    }, ms);
  });
  try {
    return await Promise.race([call(), guard]);
  } finally {
    if (timer) clearTimeout(timer);
  }
}

async function handleSuggestClosers(): Promise<void> {
  const editor = activeEcEditor();
  if (!editor) return;
  const uri = editor.document.uri.toString();
  // Race the closer sweep against the preview timeout; on expiry,
  // dispatch proof/cancel and surface a "timed out" notice. Without
  // this, a slow closer candidate (e.g. an SMT call that runs to
  // EC's iterate-budget) would block the editor for ~16s with no
  // escape hatch. The user can also cancel explicitly via
  // [easycrypt.proof.cancel] (Cmd/Ctrl+Alt+.).
  let result: SuggestClosersResponse | undefined;
  try {
    result = await vscode.window.withProgress(
      {
        location: vscode.ProgressLocation.Notification,
        title: 'EasyCrypt: trying closer candidates…',
        cancellable: true,
      },
      (_progress, token) => {
        // Wire VS Code's progress-notification cancel button to
        // proof/cancel as well, so either the explicit Cancel command
        // or clicking the notification's Cancel button stops the
        // sweep.
        token.onCancellationRequested(() => { void sendCancel(uri); });
        return withPreviewTimeout(uri, () =>
          withClient(c =>
            c.sendRequest<SuggestClosersResponse>(
              'easycrypt/proof/suggestClosers',
              { uri, expectedCas: null },
            ),
          ).then(r => r as SuggestClosersResponse),
        );
      },
    );
  } catch (err) {
    const msg = err instanceof Error ? err.message : String(err);
    // Closer-sweep timeouts / cancels land here — full text logged
    // to the 'closer' Output channel for review (selectable via
    // easycrypt.proof.previewLog.show).
    logPreviewError('closer', `easycrypt/proof/suggestClosers (uri=${uri})`, msg);
    vscode.window.showInformationMessage(`EasyCrypt: ${msg}`);
    return;
  }
  if (!result) return;
  if (result.rows.length === 0) {
    vscode.window.showInformationMessage(
      'suggestClosers: no candidates were tried.',
    );
    return;
  }
  const sorted = sortSuggestRows(result.rows);
  const items = sorted.map(quickPickItemOf);
  const pick = await vscode.window.showQuickPick(items, {
    title: 'EasyCrypt: Suggest Closers',
    placeHolder: 'Select a closer to insert at the cursor (Esc to dismiss)',
    matchOnDescription: true,
    matchOnDetail: true,
  });
  if (!pick) return;
  // Insert the picked source at the cursor. User then runs Exec To
  // Cursor (Cmd/Ctrl+Alt+Enter) to actually advance through it.
  const cursor = editor.selection.active;
  await editor.edit(builder => {
    builder.insert(cursor, pick.src + '\n');
  });
}

// ---- Dev macros (rebuild + reload window) ---------------------------

function runShell(
  cmd: string,
  cwd: string,
): Promise<{ stdout: string; stderr: string }> {
  return new Promise((resolve, reject) => {
    cp.exec(cmd, { cwd, maxBuffer: 32 * 1024 * 1024 }, (err, stdout, stderr) => {
      if (err) {
        reject(
          new Error(
            `${cmd} failed: ${err.message}\nstdout:\n${stdout}\nstderr:\n${stderr}`,
          ),
        );
      } else {
        resolve({ stdout, stderr });
      }
    });
  });
}

// Rebuild the daemon (dune build) + the extension (npm run compile)
// then reload the window so both pick up. Reload also tears down +
// respawns the daemon and its EC subprocess, so an OCaml change in
// src/ec.ml or tooling/** is fully live in one keystroke. Default
// keybind: Cmd/Ctrl+Alt+Shift+B.
async function handleRebuildAndReload(): Promise<void> {
  const root = vscode.workspace.workspaceFolders?.[0]?.uri.fsPath;
  if (!root) {
    vscode.window.showErrorMessage(
      'EasyCrypt (dev): no workspace folder open.',
    );
    return;
  }
  try {
    await vscode.window.withProgress(
      {
        location: vscode.ProgressLocation.Notification,
        title: 'EasyCrypt (dev): rebuilding…',
        cancellable: false,
      },
      async (progress) => {
        progress.report({ message: 'dune build' });
        await runShell('dune build', root);
        progress.report({ message: 'tsc compile' });
        await runShell('npm run compile', path.join(root, 'vscode'));
      },
    );
  } catch (err) {
    const msg = err instanceof Error ? err.message : String(err);
    vscode.window.showErrorMessage(
      `EasyCrypt (dev): rebuild failed.\n${msg}`,
    );
    return;
  }
  await vscode.commands.executeCommand('workbench.action.reloadWindow');
}

async function handleLspRestart(): Promise<void> {
  await stopClient();
  lockedEnd.clear();
  lastSeq = 0;
  refreshAllVisible();
  if (goalsPanel) {
    goalsPanel.webview.html =
      '<html><body><pre>language server restarting…</pre></body></html>';
  }
  await startClient();
  vscode.window.showInformationMessage('EasyCrypt: language server restarted.');
}

// ---- Mouse line selection (proc rewrite / proc change) -------------
//
// Webview emits {cmd:'procRewrite'|'procChange', side, codepos,
// cpos1End?} from the goals pane on right-click context-menu actions.
// Pure helpers (codepos serialization, tactic-source synthesis,
// validity classification) live in ./codepos for unit-testability;
// re-imported here to keep extension.ts focused on VSCode glue.

import {
  Codepos as MsgCodepos,
  ProgSide as MsgProgSide,
  ProcChangeBinding,
  RewriteSlots,
  ecCodeposSource,
  procRewriteSource,
  procChangeSource,
  classifyChangeProbe,
  emptyRewriteSlots,
  rewriteAssembleArg,
  rewriteOccurrenceFromInput,
  rewriteMatchFromInput,
  rewriteSlotsSummary,
} from './codepos';

// ---- Token builders (move => / rewrite) ----------------------------
//
// Mirror of the TUI's S_move_intros / S_rewrite_build state machines:
// user types tokens incrementally; each token is tried as a cumulative
// `move => t1 t2 ... tk.` (or `rewrite t1 t2 ... tk.`) via the
// daemon's tryTactic; success commits the token, failure rejects with
// an inline error in the InputBox.
//
// Goal pane shows live preview of the speculative post-tactic state
// via setGoalsPreview when a token validates ok.
//
// Finalize on Enter-with-empty-input: insert the cumulative source at
// the cursor position captured at command-invocation time. Esc /
// dismiss cancels without insertion.
//
// Backspace-pop via the "Remove last token" button (top-right of the
// InputBox) to avoid clobbering normal text editing inside the input.

// ---- TacticSchema + runBuilder -------------------------------------
//
// TacticSchema describes what we know ABOUT a tactic; runBuilder USES
// it to drive an incremental token-builder. Adding a new builder is
// "add a schema entry" — no new builder code per tactic. Sentinels are
// shared across all builders (consistent grammar). Wildcard probing
// (auto-pad with `_` until tryTactic accepts) is opt-in per schema.

// Sentinel handler: invoked when the user types EXACTLY the sentinel
// character + Enter. Receives the uri; returns a string to splice into
// the input as the next token, or undefined to no-op.
type SentinelHandler = (uri: string) => Promise<string | undefined>;

interface TacticSchema {
  // Stable identifier for command IDs and the launcher.
  id: string;
  // Display label in the launcher / palette.
  label: string;
  // InputBox title.
  title: string;
  // Placeholder hint.
  hint: string;
  // Build the cumulative EC source for a token list.
  cumulative: (tokens: string[]) => string;
  // Sentinel grammar (precise: each fires only when input is EXACTLY
  // the sentinel character + Enter; longer inputs are literal).
  // Each value is the action; the key is the sentinel character.
  sentinels?: { [char: string]: { hint: string; handler: SentinelHandler } };
  // Wildcard probe: when set, validation that fails tries appending
  // 1..maxK fillToken before reporting err — gives the user feedback
  // about how many more args are needed without making them type `_`s.
  wildcardProbe?: { fillToken: string; maxK: number };
}

// Open the lemma picker as a subcommand returning a token (qname or
// `-qname` / `!qname` for rewrite-direction modifiers).
//
// `previewSourceBuilder`: optional. When the parent builder's
// eventual tactic shape differs from `verb qname.` (e.g., proc
// rewrite targeting a code position), pass a builder so the
// picker's preview reflects what the parent will commit. Without
// it, rewrite-into-program contexts show "nothing to rewrite"
// because the default `rewrite qname.` source operates on the
// goal conclusion, not the targeted instruction.
function lemmaPickerSentinelHandler(
  verb: 'apply' | 'rewrite',
  previewSourceBuilder?: (qname: string) => string,
  singleDirection: boolean = false,
): SentinelHandler {
  return async (uri: string) => {
    return runLemmaPicker({ uri, verb, mode: 'token-return',
                            previewSourceBuilder, singleDirection });
  };
}

// Built-in tactic schemas. New entries land here.
const tacticSchemas: TacticSchema[] = [
  {
    id: 'move',
    label: 'move => (intro builder)',
    title: 'EasyCrypt: move => (intro builder)',
    hint: 'next intro pattern (e.g., x, H, ?). Enter to commit. Enter on empty to finalize.',
    cumulative: (tokens) => `move => ${tokens.join(' ')}.`,
  },
  {
    id: 'rewrite',
    label: 'rewrite (token builder)',
    title: 'EasyCrypt: rewrite (token builder)',
    hint: 'next rewrite arg (e.g., H, -H, !L, /foo). Type "?" + Enter to pick a lemma.',
    cumulative: (tokens) => `rewrite ${tokens.join(' ')}.`,
    sentinels: {
      '?': {
        hint: 'Press Enter to open the lemma picker',
        handler: lemmaPickerSentinelHandler('rewrite'),
      },
    },
  },
  {
    id: 'apply',
    label: 'apply (token builder)',
    title: 'EasyCrypt: apply (token builder)',
    hint: 'next apply arg (qname, `_` wildcard, term). Type "?" + Enter to pick a lemma.',
    cumulative: (tokens) => `apply ${tokens.join(' ')}.`,
    sentinels: {
      '?': {
        hint: 'Press Enter to open the lemma picker',
        handler: lemmaPickerSentinelHandler('apply'),
      },
    },
    wildcardProbe: { fillToken: '_', maxK: 5 },
  },
  {
    id: 'have',
    label: 'have (assertion builder)',
    title: 'EasyCrypt: have (assertion)',
    hint: 'have <name> : <term>  (e.g., H : 0 < 1). Enter on empty to finalize.',
    cumulative: (tokens) => `have ${tokens.join(' ')}.`,
  },
  {
    id: 'case',
    label: 'case (case-split builder)',
    title: 'EasyCrypt: case',
    hint: 'next case arg (term, hyp). Enter on empty to finalize.',
    cumulative: (tokens) => `case ${tokens.join(' ')}.`,
  },
  {
    id: 'elim',
    label: 'elim (elimination builder)',
    title: 'EasyCrypt: elim',
    hint: 'next elim arg (hyp, qname). Enter on empty to finalize.',
    cumulative: (tokens) => `elim ${tokens.join(' ')}.`,
  },
  {
    id: 'exact',
    label: 'exact (term builder)',
    title: 'EasyCrypt: exact',
    hint: 'exact term (qname or expression). Enter on empty to finalize.',
    cumulative: (tokens) => `exact ${tokens.join(' ')}.`,
    wildcardProbe: { fillToken: '_', maxK: 5 },
  },
];

const tacticSchemaById = new Map(tacticSchemas.map(s => [s.id, s]));

interface BuilderOpts {
  uri: string;
  insertPosition: vscode.Position;
  schema: TacticSchema;
  // Pre-resolved editor — used when the caller invoked the builder
  // from a webview (goal pane right-click), where [activeEcEditor]
  // returns undefined because the active editor is the webview.
  // When omitted, falls back to [activeEcEditor].
  editor?: vscode.TextEditor;
}

async function runBuilder(opts: BuilderOpts): Promise<void> {
  const { uri, insertPosition, schema } = opts;
  const editor = opts.editor ?? activeEcEditor();
  if (!editor) return;
  ensureGoalsPanel();
  void fetchAndRenderGoals(uri);
  const tokens: string[] = [];
  let currentValue = '';
  let lastValidatedOk = false;
  let lastValidatedFor = '';
  let validateSeq = 0;
  let debounceTimer: NodeJS.Timeout | undefined;
  // Same flag as runApplyPhase3 — prevents onDidHide from disposing
  // the input when we hide it to launch a sub-picker (?-sentinel).
  let intentionallyHiding = false;

  const removeButton: vscode.QuickInputButton = {
    iconPath: new vscode.ThemeIcon('arrow-left'),
    tooltip: 'Remove last committed token',
  };
  const detailButton: vscode.QuickInputButton = {
    iconPath: new vscode.ThemeIcon('output'),
    tooltip: 'Open full error in EasyCrypt: tactic preview Output channel',
  };
  // [previewKind] selects the Output channel (per-builder + the
  // shared "(all)" aggregator). Cleared full-error log captured the
  // last truncated [validationMessage]'s body for the (detail)
  // button to surface.
  const previewKind: PreviewLogKind = schema.id;
  let lastFullError: string | undefined;

  const cumulativeOf = (extras: string[]): string =>
    schema.cumulative([...tokens, ...extras]);

  const input = vscode.window.createInputBox();
  input.placeholder = schema.hint;
  // Title carries [schema.title — committed: <summary>] and stays
  // visible regardless of validationMessage; prompt carries the
  // in-flight status. See [summarizeCommittedTokens] for overflow
  // handling.
  function applyTitle() {
    const sum = summarizeCommittedTokens(tokens, 80);
    input.title = `${schema.title} — committed: ${sum.short}`;
  }
  applyTitle();

  // Set [validationMessage] to a short summary; stash the full
  // body for the (detail) button. Always log full text to the
  // per-builder Output channel + the aggregator. [severity] is
  // VSCode's enum value.
  function setShortValidation(
    short: string,
    severity: vscode.InputBoxValidationSeverity,
    full?: string,
    sourceForLog?: string,
  ): void {
    input.validationMessage = { message: short, severity };
    if (full !== undefined && severity === vscode.InputBoxValidationSeverity.Error) {
      lastFullError = full;
      logPreviewError(previewKind, sourceForLog ?? '(unknown)', full);
    } else {
      // Non-error states clear the stashed error so (detail) doesn't
      // surface stale text from an earlier failure.
      lastFullError = undefined;
    }
    refreshButtons();
  }
  function clearValidation(): void {
    input.validationMessage = undefined;
    lastFullError = undefined;
    refreshButtons();
  }
  function refreshButtons(): void {
    const buttons: vscode.QuickInputButton[] = [];
    if (lastFullError !== undefined) buttons.push(detailButton);
    if (tokens.length > 0) buttons.push(removeButton);
    input.buttons = buttons;
  }

  // Sentinel handler dispatch — hides the input, runs the schema's
  // handler (e.g., lemma picker), resumes with the picked token
  // loaded as the next value.
  async function runSentinelHandler(handler: SentinelHandler): Promise<void> {
    intentionallyHiding = true;
    input.hide();
    const picked = await handler(uri);
    intentionallyHiding = false;
    // Clear any pre-typed sentinel before re-showing.
    input.value = '';
    currentValue = '';
    input.show();
    if (picked !== undefined) {
      currentValue = picked;
      input.value = picked;
      await validate(picked);
    }
  }

  function refreshUI() {
    applyTitle();
    const inflight = currentValue.trim() === '' ? '(empty)' : currentValue.trim();
    input.prompt = `in-flight: ${inflight}`;
    refreshButtons();
  }

  // Try the cumulative source as-is, then optionally probe with
  // 1..maxK appended fillToken in parallel. Returns the smallest-N
  // ok result if the bare source fails, or the bare-source result
  // unchanged if it succeeds (or all probes fail).
  async function validateWithProbe(
    cumulative: string,
  ): Promise<{ result: TryTacticResponse | undefined; padCount: number }> {
    const probeSources: string[] = [cumulative];
    if (schema.wildcardProbe) {
      const fill = schema.wildcardProbe.fillToken;
      const trimmed = cumulative.replace(/\.$/, '');
      for (let k = 1; k <= schema.wildcardProbe.maxK; k++) {
        const wildcards = Array(k).fill(fill).join(' ');
        probeSources.push(`${trimmed} ${wildcards}.`);
      }
    }
    const probes = await Promise.all(
      probeSources.map((src, idx) =>
        withClient(c =>
          c.sendRequest<TryTacticResponse>('easycrypt/proof/tryTactic', {
            uri,
            source: src,
            expectedCas: null,
          }),
        ).then(r => ({ result: r, padCount: idx })),
      ),
    );
    const winner = probes.find(p => p.result?.outcome === 'ok');
    return winner ?? probes[0];
  }

  async function validate(value: string): Promise<void> {
    const trimmed = value.trim();
    if (trimmed === '') {
      clearValidation();
      lastValidatedOk = false;
      lastValidatedFor = '';
      clearGoalsPreview(uri);
      return;
    }
    // Sentinel hint — don't validate as a tactic; show schema's hint.
    const sentinel = schema.sentinels?.[trimmed];
    if (sentinel) {
      setShortValidation(
        sentinel.hint,
        vscode.InputBoxValidationSeverity.Info,
      );
      lastValidatedOk = false;
      lastValidatedFor = trimmed;
      return;
    }
    const cumulative = cumulativeOf([trimmed]);
    const seq = ++validateSeq;
    input.busy = true;
    const { result, padCount } = await validateWithProbe(cumulative);
    if (seq !== validateSeq) return;
    input.busy = false;
    if (!result) {
      setShortValidation(
        '(daemon unavailable)',
        vscode.InputBoxValidationSeverity.Error,
      );
      lastValidatedOk = false;
      lastValidatedFor = trimmed;
      return;
    }
    if (result.outcome === 'ok') {
      const summary = result.closedFocused
        ? '★ closes the goal'
        : `→ ${result.goalsAfter?.subgoal_count ?? '?'} subgoal(s)`;
      const padNote =
        padCount > 0
          ? `  ⚠ needs ${padCount} more arg${padCount === 1 ? '' : 's'}`
          : '';
      if (padCount > 0) {
        setShortValidation(
          `Bare input fails — would succeed with ${padCount} more arg${padCount === 1 ? '' : 's'} (e.g., ${schema.wildcardProbe?.fillToken ?? '_'} placeholders).`,
          vscode.InputBoxValidationSeverity.Warning,
        );
      } else {
        clearValidation();
      }
      input.prompt = `in-flight: ${trimmed}  ·  preview: ${summary}${padNote}`;
      lastValidatedOk = padCount === 0;  // only commit if as-is works
      lastValidatedFor = trimmed;
      if (result.goalsAfter) {
        setGoalsPreview(uri, result.goalsAfter, '🔍 builder preview');
      }
    } else {
      const full = (result.error ?? 'tactic failed').trim();
      const { short } = truncateForValidation(full);
      setShortValidation(
        short,
        vscode.InputBoxValidationSeverity.Error,
        full,
        cumulative,
      );
      lastValidatedOk = false;
      lastValidatedFor = trimmed;
    }
  }

  async function refreshCommittedPreview(): Promise<void> {
    if (tokens.length === 0) {
      clearGoalsPreview(uri);
      return;
    }
    const seq = ++validateSeq;
    input.busy = true;
    const result = await withClient(c =>
      c.sendRequest<TryTacticResponse>('easycrypt/proof/tryTactic', {
        uri,
        source: cumulativeOf([]),
        expectedCas: null,
      }),
    );
    if (seq !== validateSeq) return;
    input.busy = false;
    if (result?.outcome === 'ok' && result.goalsAfter) {
      setGoalsPreview(uri, result.goalsAfter, '🔍 builder preview');
    }
  }

  input.onDidChangeValue(value => {
    currentValue = value;
    refreshUI();  // keep [in-flight: …] live
    if (debounceTimer) clearTimeout(debounceTimer);
    if (value.trim() === '') {
      clearValidation();
      lastValidatedOk = false;
      lastValidatedFor = '';
      void refreshCommittedPreview();
      return;
    }
    debounceTimer = setTimeout(() => {
      void validate(value);
    }, 150);
  });

  input.onDidAccept(async () => {
    if (debounceTimer) {
      clearTimeout(debounceTimer);
      debounceTimer = undefined;
    }
    const value = currentValue.trim();
    if (value === '') {
      // Finalize.
      if (tokens.length > 0) {
        const finalSource = cumulativeOf([]);
        await editor.edit(b => b.insert(insertPosition, finalSource + '\n'));
      }
      input.dispose();
      return;
    }
    // Sentinel exact-match dispatch.
    const sentinel = schema.sentinels?.[value];
    if (sentinel) {
      input.value = '';
      currentValue = '';
      await runSentinelHandler(sentinel.handler);
      return;
    }
    if (!lastValidatedOk || lastValidatedFor !== value) {
      await validate(value);
    }
    if (lastValidatedOk) {
      tokens.push(value);
      input.value = '';
      currentValue = '';
      lastValidatedOk = false;
      lastValidatedFor = '';
      clearValidation();
      refreshUI();
      void refreshCommittedPreview();
    }
  });

  input.onDidTriggerButton(async button => {
    if (button === removeButton) {
      if (tokens.length > 0) {
        tokens.pop();
        refreshUI();
        if (currentValue.trim() !== '') {
          await validate(currentValue);
        } else {
          await refreshCommittedPreview();
        }
      }
      return;
    }
    if (button === detailButton) {
      // Surface the per-builder Output channel; the most-recent
      // full error was already appended there when the validation
      // fired. The user can switch to "(all)" via the dropdown if
      // they want cross-builder context.
      getPreviewLogChannel(previewKind).show(/* preserveFocus */ false);
      return;
    }
  });

  input.onDidHide(() => {
    // Don't dispose if we're hiding for a sub-picker — onDidHide
    // would otherwise tear down state the sub-flow needs to restore.
    if (intentionallyHiding) return;
    if (debounceTimer) clearTimeout(debounceTimer);
    clearGoalsPreview(uri);
    input.dispose();
  });

  input.show();
  refreshUI();
}

// ---- Rewrite builder (5 independently-editable slots) -------------
//
// Specialized builder for `rewrite` whose model differs from the
// generic cumulative-token pattern. Each `rwarg1` is a tuple of
// modifier slots (side / repeat / occurrence / match) + a lemma
// (pterm). The rewrite tactic accepts a list of such args, joined
// with spaces. Per `rwarg1` parser production
// (src/ecParser.mly:2420), token assembly order is:
//
//   side · repeat · occurrence · match · lemma
//
// All five slots of the in-flight arg are independently editable
// via title-bar buttons: direction (←/→ toggle), repeat (!), occ
// (@), pattern ([), lemma (?). The user can populate them in any
// order; preview re-fires (debounced tryTactic) on every slot
// change. The lemma slot accepts free-text typing in the InputBox
// OR comes back from the lemma picker (singleDirection: returns
// bare qname — the rewrite builder owns direction independently).
//
// On commit (✓ button or Enter on non-empty value):
//   1. The current InputBox value (if non-empty) becomes the lemma
//      slot's final value (overriding any picker-set lemma).
//   2. The slots are assembled into one rwarg1 token and pushed
//      to `tokens`.
//   3. The pending state resets; the InputBox clears.
//
// Finalize: empty input + Enter when `tokens.length > 0` and
// in-flight is empty → insert `rewrite t1 t2 … tN.` at cursor.

interface RewriteBuilderOpts {
  uri: string;
  insertPosition: vscode.Position;
  // Pre-resolved editor (mirrors runBuilder.editor — relevant when
  // launched from the goal-pane webview right-click flow).
  editor?: vscode.TextEditor;
  // Tactic source prefix. Default: 'rewrite' (the regular tactic).
  // For proc rewrite triggered from a code-position context, set
  // to e.g. 'proc rewrite{1} 2 . 1' so the assembled args compose
  // into the proc-rewrite syntax. The prefix is the entire pre-arg
  // portion of the tactic — caller is responsible for any side
  // suffix and codepos serialization. The trailing '.' is added
  // by the builder.
  tacticPrefix?: string;
  // Display label shown in the InputBox title and the preview
  // badge. Defaults to 'rewrite'; for proc rewrite, callers pass
  // e.g. 'proc rewrite{1} at 2 . 1' for at-a-glance visibility.
  title?: string;
}

// Sentinel chars that, when typed alone in the InputBox value,
// should NOT be folded into the lemma slot for preview purposes
// (and instead route to a sub-flow on Enter). Including them in the
// cumulative source would cause spurious parse errors in the
// preview as the user types; we suppress them at the inflight-fold
// step.
const REWRITE_SENTINEL_CHARS = new Set(['?', '[', '@']);

async function runRewriteBuilder(opts: RewriteBuilderOpts): Promise<void> {
  const { uri, insertPosition } = opts;
  const tacticPrefix = opts.tacticPrefix ?? 'rewrite';
  const titleLabel = opts.title ?? 'rewrite';
  const editor = opts.editor ?? activeEcEditor();
  if (!editor) return;
  ensureGoalsPanel();
  void fetchAndRenderGoals(uri);

  const tokens: string[] = [];                    // committed rwarg1 strings
  let pending: RewriteSlots = emptyRewriteSlots();
  let currentValue = '';                          // free-text typed lemma
  let validateSeq = 0;
  let debounceTimer: NodeJS.Timeout | undefined;
  let intentionallyHiding = false;

  // Title-bar buttons. Order chosen for grammar-order discoverability:
  // direction → repeat → occurrence → match → lemma → commit.
  const sideButton: vscode.QuickInputButton = {
    iconPath: new vscode.ThemeIcon('arrow-swap'),
    tooltip: 'Toggle direction: forward (→) ↔ reverse (-, ←)',
  };
  const repeatButton: vscode.QuickInputButton = {
    iconPath: new vscode.ThemeIcon('refresh'),
    tooltip: 'Toggle repeat (!)',
  };
  const occButton: vscode.QuickInputButton = {
    iconPath: new vscode.ThemeIcon('list-ordered'),
    tooltip: 'Set occurrence(s) — e.g. "1 3" inclusive, "-2" exclusive, empty = all',
  };
  const matchButton: vscode.QuickInputButton = {
    iconPath: new vscode.ThemeIcon('selection'),
    tooltip: 'Set match pattern (optional binder for [x in p] form)',
  };
  const lemmaButton: vscode.QuickInputButton = {
    iconPath: new vscode.ThemeIcon('symbol-method'),
    tooltip: 'Pick lemma (search)',
  };
  const commitArgButton: vscode.QuickInputButton = {
    iconPath: new vscode.ThemeIcon('check'),
    tooltip: 'Commit current arg, start a new one',
  };
  const removeButton: vscode.QuickInputButton = {
    iconPath: new vscode.ThemeIcon('arrow-left'),
    tooltip: 'Remove last committed arg',
  };
  const detailButton: vscode.QuickInputButton = {
    iconPath: new vscode.ThemeIcon('output'),
    tooltip: 'Open full error in EasyCrypt: tactic preview Output channel',
  };
  // Both `rewrite` and `proc rewrite ...` 5-slot flows share the
  // 'rewrite' channel; the per-entry source line in the channel
  // log carries the full [tacticPrefix] so users can disambiguate.
  const previewKind: PreviewLogKind = 'rewrite';
  let lastFullError: string | undefined;

  const input = vscode.window.createInputBox();
  input.placeholder =
    'lemma name. Sentinels: ? lemma picker, [ match pattern, @ occurrence. Buttons mirror these + ↔ direction, ! repeat, ✓ commit arg.';

  function applyTitle() {
    const sum = summarizeCommittedTokens(tokens, 80);
    input.title =
      `EasyCrypt: ${titleLabel} (5-slot builder) — committed: ${sum.short}`;
  }
  applyTitle();

  function setShortValidation(
    short: string,
    severity: vscode.InputBoxValidationSeverity,
    full?: string,
    sourceForLog?: string,
  ): void {
    input.validationMessage = { message: short, severity };
    if (full !== undefined && severity === vscode.InputBoxValidationSeverity.Error) {
      lastFullError = full;
      logPreviewError(previewKind, sourceForLog ?? '(unknown)', full);
    } else {
      lastFullError = undefined;
    }
    refreshButtons();
  }
  function clearValidation(): void {
    input.validationMessage = undefined;
    lastFullError = undefined;
    refreshButtons();
  }
  function refreshButtons(): void {
    const buttons: vscode.QuickInputButton[] = [
      sideButton, repeatButton, occButton, matchButton,
      lemmaButton, commitArgButton,
    ];
    if (lastFullError !== undefined) buttons.push(detailButton);
    if (tokens.length > 0) buttons.push(removeButton);
    input.buttons = buttons;
  }

  // Returns the in-flight arg with the current InputBox value
  // folded into the lemma slot (overriding any prior set value
  // when the user types). Sentinel chars typed alone do NOT get
  // folded — they're sub-flow triggers, not lemma names.
  function inflightWithTyped(): RewriteSlots {
    const typed = currentValue.trim();
    if (typed === '' || REWRITE_SENTINEL_CHARS.has(typed)) return pending;
    return { ...pending, lemma: typed };
  }

  // Build the cumulative `<prefix> t1 … tN.` source. Optionally
  // append the in-flight arg (if non-empty) for live preview.
  // For the regular `rewrite` prefix, this emits standard rewrite
  // syntax. For `proc rewrite{side} <codepos>`, the same arg
  // composition applies — the slots' grammar is the rwarg1
  // grammar EC uses for both (post-merge `rwarg1` parsing covers
  // both the toplevel rewrite tactic and the in-flight v1+ proc
  // rewrite parity work).
  function cumulativeWith(includeInflight: boolean): string {
    const argTokens = [...tokens];
    if (includeInflight) {
      const s = rewriteAssembleArg(inflightWithTyped());
      if (s !== '') argTokens.push(s);
    }
    if (argTokens.length === 0) return '';
    return tacticPrefix + ' ' + argTokens.join(' ') + '.';
  }

  // Refresh title (committed) + prompt (in-flight) + buttons.
  // Static buttons are always present; remove-arg only when there's
  // a committed token; (detail) only when there's a stashed error.
  function refreshUI() {
    applyTitle();
    const slotsSummary = rewriteSlotsSummary(inflightWithTyped());
    const inflight = slotsSummary === '' ? '(empty)' : slotsSummary;
    input.prompt = `in-flight: ${inflight}`;
    refreshButtons();
  }

  // Re-fire preview against the cumulative source including the
  // in-flight arg. If in-flight is empty (no slots populated and no
  // typed value), fall back to committed-only. If the typed value
  // is a known sentinel, show its hint instead of running validate
  // (sentinels are sub-flow triggers, not lemma names).
  async function fireValidate(): Promise<void> {
    const seq = ++validateSeq;
    const trimmed = currentValue.trim();
    if (REWRITE_SENTINEL_CHARS.has(trimmed)) {
      const hint =
        trimmed === '?' ? 'Press Enter to open the lemma picker'
        : trimmed === '[' ? 'Press Enter to open the match-pattern popup'
        : 'Press Enter to set the occurrence selector';
      setShortValidation(hint, vscode.InputBoxValidationSeverity.Info);
      return;
    }
    const src = cumulativeWith(true);
    if (src === '') {
      // Nothing to preview — restore live goals.
      clearGoalsPreview(uri);
      clearValidation();
      return;
    }
    input.busy = true;
    const result = await withClient(c =>
      c.sendRequest<TryTacticResponse>('easycrypt/proof/tryTactic', {
        uri, source: src, expectedCas: null,
      }),
    );
    input.busy = false;
    if (seq !== validateSeq) return;
    if (!result) return;
    if (result.outcome === 'ok') {
      clearValidation();
      if (result.goalsAfter) {
        setGoalsPreview(uri, result.goalsAfter, `🔍 ${titleLabel} preview`);
      }
    } else {
      const full = (result.error ?? 'tactic failed').trim();
      const { short } = truncateForValidation(full);
      setShortValidation(
        short,
        vscode.InputBoxValidationSeverity.Error,
        full,
        src,
      );
    }
  }

  function scheduleValidate(): void {
    if (debounceTimer) clearTimeout(debounceTimer);
    debounceTimer = setTimeout(() => void fireValidate(), 300);
  }

  // Commit the in-flight arg (if non-empty) → tokens, reset state.
  function commitInflight(): boolean {
    const s = rewriteAssembleArg(inflightWithTyped());
    if (s === '') return false;
    tokens.push(s);
    pending = emptyRewriteSlots();
    currentValue = '';
    input.value = '';
    clearValidation();
    refreshUI();
    return true;
  }

  // Hide the input while a sub-flow runs (popup, picker), then
  // re-show. Mirrors runBuilder's intentionallyHiding pattern.
  async function withSubflow<T>(fn: () => Promise<T>): Promise<T> {
    intentionallyHiding = true;
    input.hide();
    try {
      return await fn();
    } finally {
      intentionallyHiding = false;
      input.show();
    }
  }

  // Edit-occurrence flow: opens an InputBox, parses the result via
  // rewriteOccurrenceFromInput, sets pending.occurrence.
  async function editOccurrence(): Promise<void> {
    const ib = vscode.window.createInputBox();
    ib.title = 'EasyCrypt: rewrite — occurrence(s)';
    ib.placeholder =
      'space-separated indices (e.g. "1 3" inclusive). Prefix all with "-" for exclusive (e.g. "-2 -4"). Empty = all';
    ib.value = pending.occurrence
      ? pending.occurrence.replace(/^\{|\}$/g, '').replace(/^-\s*/, '-')
      : '';
    const result = await new Promise<string | undefined>((resolve) => {
      let accepted = false;
      ib.onDidAccept(() => {
        accepted = true;
        resolve(ib.value);
        ib.hide();
      });
      ib.onDidHide(() => {
        ib.dispose();
        if (!accepted) resolve(undefined);
      });
      ib.show();
    });
    if (result === undefined) return;
    pending.occurrence = rewriteOccurrenceFromInput(result);
  }

  // Edit-match flow: opens the term-popup primitive with TWO inputs
  // (binder + pattern). For v1 we reuse editTermInPopup with a
  // contextHint — user types `<binder> in <pat>` directly OR just
  // `<pat>` for the no-binder form. Lighter UI than a custom 2-input
  // popup; the popup primitive is general-purpose.
  async function editMatch(): Promise<void> {
    const initial =
      pending.match_ === ''
        ? ''
        : pending.match_.replace(/^\[|\]$/g, '');
    const result = await editTermInPopup({
      title: 'EasyCrypt: rewrite — match pattern',
      contextHint:
        'pattern to find. Use "<binder> in <pat>" for the context-binder form (e.g. "x in f x y"). Empty = clear the slot.',
      initialValue: initial,
    });
    if (result === undefined) return;
    const trimmed = result.trim();
    if (trimmed === '') {
      pending.match_ = '';
      return;
    }
    // Detect the "<ident> in <rest>" form.
    const inMatch = trimmed.match(/^([A-Za-z_][A-Za-z_0-9']*)\s+in\s+(.+)$/);
    if (inMatch) {
      pending.match_ = rewriteMatchFromInput(inMatch[1], inMatch[2]);
    } else {
      pending.match_ = rewriteMatchFromInput('', trimmed);
    }
  }

  // Open the lemma picker. singleDirection=true → returns bare
  // qname; the rewrite builder's slot model owns direction
  // independently. previewSourceBuilder ensures the picker's
  // hover-preview reflects the actual cumulative tactic shape
  // (with the current in-flight modifiers folded in).
  async function openLemmaPicker(): Promise<string | undefined> {
    return runLemmaPicker({
      uri,
      verb: 'rewrite',
      mode: 'token-return',
      singleDirection: true,
      previewSourceBuilder: (qname) => {
        const inflight = { ...pending, lemma: qname };
        const argTokens = [...tokens, rewriteAssembleArg(inflight)];
        return 'rewrite ' + argTokens.join(' ') + '.';
      },
    });
  }

  input.onDidChangeValue(value => {
    currentValue = value;
    refreshUI();
    scheduleValidate();
  });

  input.onDidAccept(async () => {
    const trimmed = currentValue.trim();
    if (trimmed === '?') {
      // Sentinel: open lemma picker.
      const picked = await withSubflow(openLemmaPicker);
      if (picked !== undefined) {
        pending.lemma = picked;
        currentValue = '';
        input.value = '';
        refreshUI();
        scheduleValidate();
      }
      return;
    }
    if (trimmed === '[') {
      // Sentinel: open match-pattern popup.
      await withSubflow(editMatch);
      currentValue = '';
      input.value = '';
      refreshUI();
      scheduleValidate();
      return;
    }
    if (trimmed === '@') {
      // Sentinel: open occurrence InputBox.
      await withSubflow(editOccurrence);
      currentValue = '';
      input.value = '';
      refreshUI();
      scheduleValidate();
      return;
    }
    if (trimmed === '') {
      // Empty input: commit in-flight if non-empty, else finalize
      // the whole tactic (insert at cursor).
      if (rewriteAssembleArg(inflightWithTyped()) !== '') {
        commitInflight();
        scheduleValidate();
        return;
      }
      // Finalize. Use the configured [tacticPrefix] (defaults to
      // 'rewrite' for the regular builder; for proc-rewrite flows
      // it carries `proc rewrite{side} <codepos>`). Hardcoding
      // 'rewrite' here would emit a plain rewrite even when the
      // caller asked for proc rewrite — bug surfaced by the goal-
      // pane right-click flow.
      if (tokens.length === 0) return;
      const finalSrc = tacticPrefix + ' ' + tokens.join(' ') + '.';
      intentionallyHiding = true;
      input.hide();
      await editor.edit(b => b.insert(insertPosition, finalSrc + '\n'));
      input.dispose();
      clearGoalsPreview(uri);
      return;
    }
    // Non-empty input: treat the typed value as the lemma slot,
    // commit the in-flight arg.
    pending.lemma = trimmed;
    if (commitInflight()) {
      scheduleValidate();
    }
  });

  input.onDidTriggerButton(async button => {
    if (button === sideButton) {
      pending.side = pending.side === 'forward' ? 'reverse' : 'forward';
      refreshUI();
      scheduleValidate();
      return;
    }
    if (button === repeatButton) {
      pending.repeat = !pending.repeat;
      refreshUI();
      scheduleValidate();
      return;
    }
    if (button === occButton) {
      await withSubflow(editOccurrence);
      refreshUI();
      scheduleValidate();
      return;
    }
    if (button === matchButton) {
      await withSubflow(editMatch);
      refreshUI();
      scheduleValidate();
      return;
    }
    if (button === lemmaButton) {
      const picked = await withSubflow(openLemmaPicker);
      if (picked !== undefined) {
        pending.lemma = picked;
        currentValue = '';
        input.value = '';
        refreshUI();
        scheduleValidate();
      }
      return;
    }
    if (button === commitArgButton) {
      if (commitInflight()) scheduleValidate();
      return;
    }
    if (button === removeButton) {
      if (tokens.length > 0) {
        tokens.pop();
        refreshUI();
        scheduleValidate();
      }
      return;
    }
    if (button === detailButton) {
      getPreviewLogChannel(previewKind).show(/* preserveFocus */ false);
      return;
    }
  });

  input.onDidHide(() => {
    if (intentionallyHiding) return;
    if (debounceTimer) clearTimeout(debounceTimer);
    clearGoalsPreview(uri);
    input.dispose();
  });

  input.show();
  refreshUI();
}

// Per-tactic command handlers — direct keybinds for high-frequency
// builders. New tactics added via tacticSchemas can be reached via the
// launcher (Cmd/Ctrl+Alt+T) without needing a dedicated keybind.
function makeBuilderHandler(schemaId: string): () => Promise<void> {
  return async () => {
    const editor = activeEcEditor();
    if (!editor) return;
    const schema = tacticSchemaById.get(schemaId);
    if (!schema) {
      vscode.window.showErrorMessage(
        `EasyCrypt: no tactic schema "${schemaId}".`,
      );
      return;
    }
    await runBuilder({
      uri: editor.document.uri.toString(),
      insertPosition: editor.selection.active,
      schema,
    });
  };
}

const handleMoveBuilder = makeBuilderHandler('move');

// Rewrite uses the dedicated 5-slot builder rather than the generic
// schema-driven runBuilder — see runRewriteBuilder above.
const handleRewriteBuilder = async (): Promise<void> => {
  const editor = activeEcEditor();
  if (!editor) return;
  await runRewriteBuilder({
    uri: editor.document.uri.toString(),
    insertPosition: editor.selection.active,
  });
};

const handleApplyBuilder = makeBuilderHandler('apply');

// Launcher: fuzzy-pick any tactic builder. New schemas show up here
// automatically — no per-tactic keybind needed.
async function handleTacticBuilderLauncher(): Promise<void> {
  const editor = activeEcEditor();
  if (!editor) return;
  const items: vscode.QuickPickItem[] = tacticSchemas.map(s => ({
    label: s.id,
    description: s.label,
  }));
  const picked = await vscode.window.showQuickPick(items, {
    title: 'EasyCrypt: choose a tactic builder',
    placeHolder: 'fuzzy filter, ↑/↓ navigate, Enter accepts',
  });
  if (!picked) return;
  // `rewrite` has its own dedicated 5-slot builder (handles
  // direction / repeat / occurrence / match / lemma slots
  // independently); other tactics use the generic schema-driven
  // runBuilder.
  if (picked.label === 'rewrite') {
    await runRewriteBuilder({
      uri: editor.document.uri.toString(),
      insertPosition: editor.selection.active,
    });
    return;
  }
  const schema = tacticSchemaById.get(picked.label);
  if (!schema) return;
  await runBuilder({
    uri: editor.document.uri.toString(),
    insertPosition: editor.selection.active,
    schema,
  });
}

// ---- Lemma picker (apply / rewrite) --------------------------------
//
// Two-stage UI:
//   Stage 1: InputBox for the EC search pattern. User types the
//            pattern (e.g., `_ <= _` or `Foo.bar`); we auto-wrap with
//            parens and dispatch via easycrypt/proof/searchLemmas.
//   Stage 2: QuickPick of returned hits, with VSCode's built-in fuzzy
//            filter on the input. Selection-change fires a debounced
//            previewApply (tryTactic with `apply Foo.bar.` or
//            `rewrite Foo.bar.`) into the goal pane with a "🔍 lemma
//            preview" badge. Esc returns to Stage 1 (preserving the
//            pattern); Esc from Stage 1 cancels everything.
//
// Two modes:
//   'standalone' — used by Cmd+Alt+L (apply lemma). On accept, insert
//                  `apply <qname>.\n` at the captured cursor.
//   'token-return' — used as a subcommand of the rewrite builder. On
//                  accept, present a 3-way direction picker (forward
//                  / -reverse / !repeat) and return the resulting
//                  token string. Builder uses it as the next token.

interface SearchHit {
  qname: string;
  kind: string;
  short_name: string;
  signature: string;
}

interface SearchLemmasResponse {
  hits: SearchHit[];
  error: string | null;
}

interface LemmaPickerOpts {
  uri: string;
  verb: 'apply' | 'rewrite';
  // 'standalone'   — on accept, insert `verb qname.` at insertPosition
  // 'token-return' — on accept, return the qname (with optional rewrite
  //                  direction) so a builder can splice it into its input
  // 'display'      — pure browser: highlight previews via `print qname.`
  //                  (rendered to the print panel), accept just closes
  mode: 'standalone' | 'token-return' | 'display';
  insertPosition?: vscode.Position;
  // Optional preview-source builder. Default behavior synthesizes
  // `verb qname.` (with auto-wildcard probing for `apply`) — that
  // works for top-level rewrite/apply against the goal conclusion.
  // For builder contexts where the eventual tactic is shape-
  // different (e.g., proc rewrite at a codepos targets a program
  // instruction, not the conclusion), pass a builder that emits
  // the actual shape so the preview reflects what commit will do.
  // The function returns the BARE source for the bare hit; the
  // picker still adds `_` wildcards when `wildcardProbe` is
  // enabled (currently apply-only).
  previewSourceBuilder?: (qname: string) => string;
  // Suppress the rewrite-direction stage. Used by proc-rewrite
  // contexts where EC's tactic (`process_rewrite_rw` in
  // src/phl/ecPhlRewrite.ml) hard-codes the LtoR direction and
  // accepts only a bare pterm — no `-`/`!` modifiers. With this
  // flag, the picker returns the bare qname on accept; pair-
  // preview at stage 2 also collapses to a single forward probe.
  singleDirection?: boolean;
}

async function runLemmaPicker(
  opts: LemmaPickerOpts,
): Promise<string | undefined> {
  const editor = activeEcEditor();
  if (!editor) return undefined;
  const { uri, verb } = opts;
  // Display mode renders to the print panel only; apply/rewrite modes
  // render speculative goals in the goal pane.
  let liveGoals: GoalsResponse | null = null;
  if (opts.mode !== 'display') {
    ensureGoalsPanel();
    // Live-goals baseline + cache for err-previews (apply candidates
    // that don't apply render the unchanged goal as context above the
    // err block).
    void (async () => {
      const r = await withClient(c =>
        c.sendRequest<GoalsResponse>('easycrypt/proof/goals', { uri }),
      );
      if (r) liveGoals = r;
      void fetchAndRenderGoals(uri);
    })();
  }
  let lastPattern = '';
  let lastWrapped = '';
  // Carries an err / no-hits message from a failed search back into
  // Stage 1 so the user can iterate without losing the picker.
  let pendingPatternMessage:
    | { message: string; severity: vscode.InputBoxValidationSeverity }
    | undefined;
  // Cache the last successful dispatch so phase-3 rollback can re-enter
  // Stage 2 directly (skipping Stage 1's InputBox + redispatch). Set
  // when Stage 2 opens; cleared on cancel / commit.
  let cachedDispatch: SearchLemmasResponse | null = null;
  // True when we should skip Stage 1 this iteration (rollback from
  // phase-3): jumps straight to Stage 2 with cachedDispatch's hits.
  let skipToStage2 = false;
  // Search mode: 'all' uses the EC `searchall` directive (UPSTREAM
  // #22) which is overload-tolerant — patterns like `_ <= _` return
  // hits across every overload of `<=` instead of erroring on
  // ambiguity. 'strict' uses the original `search`. Default 'all';
  // user can toggle per-search via the Stage 2 title-bar 🎯 button.
  // (Workspace-setting default deferred — for now this is the
  // hardcoded sensible default.)
  let searchMode: 'all' | 'strict' = 'all';
  // True when we should skip Stage 1's InputBox and re-dispatch with
  // the existing lastPattern (used by mode-toggle to avoid showing
  // the pattern entry box again).
  let autoRedispatch = false;

  // Outer loop: Esc from Stage 2 returns to Stage 1 (with the same
  // pattern). Esc from Stage 1 returns undefined (cancel). Esc from
  // phase-3 returns to Stage 2 (skipping Stage 1).
  while (true) {
    let dispatched: SearchLemmasResponse;
    let wrapped: string;
    if (skipToStage2 && cachedDispatch) {
      // Bypass Stage 1: re-use the last dispatched hits + wrapped pattern.
      dispatched = cachedDispatch;
      wrapped = lastWrapped;
      skipToStage2 = false;
    } else {
      // Stage 1: pattern. Skip the InputBox if autoRedispatch is set
      // (mode toggle from Stage 2 — re-use lastPattern with the new
      // verb, no need to re-prompt).
      let pattern: string | undefined;
      if (autoRedispatch && lastPattern !== '') {
        pattern = lastPattern;
        autoRedispatch = false;
      } else {
        pattern = await new Promise<string | undefined>(resolve => {
          const ib = vscode.window.createInputBox();
          ib.title = `EasyCrypt: ${verb} lemma — search pattern`;
          ib.value = lastPattern;
          ib.placeholder =
            'EC pattern (e.g., _ <= _, op + op, qname). Enter dispatches; auto-wrapped with parens.';
          ib.prompt =
            'Type a pattern, press Enter to dispatch. Esc cancels.';
          if (pendingPatternMessage) {
            ib.validationMessage = pendingPatternMessage;
            pendingPatternMessage = undefined;
          }
          ib.onDidAccept(() => {
            const v = ib.value.trim();
            if (v === '') return;
            resolve(v);
            ib.dispose();
          });
          ib.onDidHide(() => {
            resolve(undefined);
            ib.dispose();
          });
          ib.show();
        });
        if (pattern === undefined) return undefined;
      }
      lastPattern = pattern;

      // Dispatch search. Auto-wrap with parens so operator patterns
      // like `_ <= _` parse cleanly on EC's side. Verb chosen by
      // searchMode — 'all' (default) uses `searchall` to tolerate
      // operator-overload ambiguity; 'strict' uses `search`.
      wrapped = pattern.startsWith('(') && pattern.endsWith(')')
        ? pattern
        : `(${pattern})`;
      lastWrapped = wrapped;
      const searchVerb = searchMode === 'all' ? 'searchall' : 'search';
      const searchSource = `${searchVerb} ${wrapped}.`;

      const dispatchedMaybe = await vscode.window.withProgress(
        {
          location: vscode.ProgressLocation.Notification,
          title: `EasyCrypt: ${searchVerb} ${wrapped}…`,
          cancellable: false,
        },
        () =>
          withClient(c =>
            c.sendRequest<SearchLemmasResponse>(
              'easycrypt/proof/searchLemmas',
              { uri, source: searchSource },
            ),
          ),
      );
      if (!dispatchedMaybe) return undefined;
      if (dispatchedMaybe.error) {
        // Don't close the picker on err — return to Stage 1 with the
        // err displayed so the user can iterate.
        pendingPatternMessage = {
          message: `searchLemmas: ${dispatchedMaybe.error}`,
          severity: vscode.InputBoxValidationSeverity.Error,
        };
        continue;
      }
      if (dispatchedMaybe.hits.length === 0) {
        pendingPatternMessage = {
          message: `No hits for ${wrapped}. Refine the pattern and try again.`,
          severity: vscode.InputBoxValidationSeverity.Info,
        };
        continue;
      }
      dispatched = dispatchedMaybe;
      cachedDispatch = dispatched;
    }

    // Stage 2: QuickPick over hits.
    interface HitItem extends vscode.QuickPickItem {
      hit: SearchHit;
    }
    const items: HitItem[] = dispatched.hits.map(h => ({
      label: h.qname,
      description: h.kind,
      detail: h.signature,
      hit: h,
    }));
    const qp = vscode.window.createQuickPick<HitItem>();
    const titleVerb =
      opts.mode === 'display' ? 'browse' : `${verb} lemma`;
    qp.title = `EasyCrypt: ${titleVerb} — search ${wrapped}.  · Esc returns to pattern`;
    qp.placeholder = opts.mode === 'display'
      ? 'fuzzy filter, ↑/↓ navigate, Enter closes (preview shown in print pane)'
      : 'fuzzy filter, ↑/↓ navigate, Enter accepts (Shift+Enter / 🔧 button: refine args)';
    // Stage-2 title-bar buttons: refine-args (apply standalone only)
    // + search-mode toggle (always). Toggle re-runs the current
    // pattern with the alternate verb (`searchall` ↔ `search`) and
    // re-displays Stage 2 with the new hits.
    let refineArgsButton: vscode.QuickInputButton | undefined;
    const toggleModeButton: vscode.QuickInputButton = {
      iconPath: new vscode.ThemeIcon(
        searchMode === 'all' ? 'symbol-misc' : 'target',
      ),
      tooltip:
        searchMode === 'all'
          ? 'Mode: ALL overloads (default) — click to switch to strict (faster, requires unambiguous pattern)'
          : 'Mode: STRICT — click to switch to all (overload-tolerant, default)',
    };
    const stageButtons: vscode.QuickInputButton[] = [];
    if (verb === 'apply' && opts.mode === 'standalone') {
      refineArgsButton = {
        iconPath: new vscode.ThemeIcon('tools'),
        tooltip: 'Refine args (Shift+Enter): incremental builder for the active hit',
      };
      stageButtons.push(refineArgsButton);
    }
    stageButtons.push(toggleModeButton);
    qp.buttons = stageButtons;
    qp.matchOnDescription = true;
    qp.matchOnDetail = true;
    qp.items = items;
    qp.activeItems = [items[0]];

    let previewTimer: NodeJS.Timeout | undefined;
    let previewSeq = 0;

    function clearPreview() {
      if (previewTimer) {
        clearTimeout(previewTimer);
        previewTimer = undefined;
      }
      clearGoalsPreview(uri);
    }

    async function firePreview(hit: SearchHit) {
      const seq = ++previewSeq;
      // 'display' mode previews via `print` (renders to print panel,
      // leaves goal pane alone). Other modes preview via tryTactic
      // and render the speculative goals (or err) in the goal pane.
      if (opts.mode === 'display') {
        const printSource = `print ${hit.qname}.`;
        const result = await withClient(c =>
          c.sendRequest<PrintResponse>('easycrypt/proof/print', {
            uri,
            source: printSource,
          }),
        );
        if (seq !== previewSeq) return;
        if (!result) return;
        const body = result.error
          ? (result.output
              ? result.output + '\n\nerror: ' + result.error
              : 'error: ' + result.error)
          : result.output;
        setPrintOutput({
          title: `print: ${hit.qname}`,
          source: printSource,
          body,
        });
        return;
      }
      // Auto-wildcard probe: try the bare `verb qname.` first; if it
      // fails (often does for `apply` because EC needs explicit
      // args), probe IN PARALLEL with 1..K trailing wildcards. Take
      // the smallest N that succeeds. Only kicks in for verbs whose
      // grammar admits `_` wildcards (apply / exact / refine).
      // Rewrite uses `-`/`!` modifiers instead — no probing.
      const probeWildcards = verb === 'apply';
      // Preview-source synthesis: default to `verb qname.` (works
      // for top-level rewrite/apply against the goal conclusion).
      // Callers that target a different shape (e.g., proc rewrite
      // at a codepos) supply their own builder via opts.
      const buildSrc = opts.previewSourceBuilder ?? ((q: string) => `${verb} ${q}.`);
      // Probe one direction (single qname-or-modified-qname token).
      // Returns the resolved source + the resulting outcome
      // suitable for ComparisonOutcome construction.
      async function probeOneDir(token: string): Promise<{
        source: string; outcome: ComparisonOutcome;
      }> {
        const baseSource = buildSrc(token);
        const probeSources: string[] = [baseSource];
        if (probeWildcards) {
          const trimmed = baseSource.replace(/\.$/, '');
          for (let k = 1; k <= 5; k++) {
            const wildcards = Array(k).fill('_').join(' ');
            probeSources.push(`${trimmed} ${wildcards}.`);
          }
        }
        const probes = await Promise.all(
          probeSources.map(src =>
            withClient(c =>
              c.sendRequest<TryTacticResponse>('easycrypt/proof/tryTactic', {
                uri, source: src, expectedCas: null,
              }),
            ).then(r => ({ source: src, result: r })),
          ),
        );
        const winner = probes.find(p => p.result?.outcome === 'ok');
        const fallback = probes[0];
        const chosen = winner ?? fallback;
        if (!chosen.result) {
          return {
            source: baseSource,
            outcome: { kind: 'error', errorKind: 'does-not-apply', error: 'no result' },
          };
        }
        const outcome: ComparisonOutcome =
          chosen.result.outcome === 'ok' && chosen.result.goalsAfter
            ? { kind: 'success', newGoals: chosen.result.goalsAfter,
                closedFocused: chosen.result.closedFocused === true,
                cycleIndex: 0 }
            : { kind: 'error',
                errorKind: classifyTacticError((chosen.result.error ?? 'tactic failed').trim()),
                error: (chosen.result.error ?? 'tactic failed').trim() };
        return { source: chosen.source, outcome };
      }
      // Rewrite: dispatch BOTH forward (`qname`) and reverse
      // (`-qname`) at first hover so the user sees both directions
      // before picking. Stage 3 (direction picker) handles per-
      // direction previews individually.
      //
      // Skip the dual-preview when the caller asked for single-
      // direction (e.g., proc rewrite, where EC's tactic only
      // supports forward — see lemmaPickerSentinelHandler comment).
      if (verb === 'rewrite' && !opts.singleDirection) {
        const [fwd, rev] = await Promise.all([
          probeOneDir(hit.qname),
          probeOneDir('-' + hit.qname),
        ]);
        if (seq !== previewSeq) return;
        // Stash the resolved sources so any 'standalone' mode
        // insert path uses the right one. (Forward by default.)
        pickedSourceFor.set(hit.qname, fwd.source);
        pickedSourceFor.set('-' + hit.qname, rev.source);
        const badge = `🔍 ${verb} ${hit.qname}  ·  forward + reverse`;
        setGoalsPairPreview(
          uri, liveGoals, badge,
          `→ Forward: ${verb} ${hit.qname}`, fwd.outcome,
          `← Reverse: ${verb} -${hit.qname}`, rev.outcome,
        );
        return;
      }
      // Apply (or any other future verb): single-direction preview.
      const single = await probeOneDir(hit.qname);
      if (seq !== previewSeq) return;
      pickedSourceFor.set(hit.qname, single.source);
      // Reconstruct wildcardCount from resolved source vs base.
      const baseSrc = buildSrc(hit.qname);
      const wildcardCount =
        probeWildcards && single.source !== baseSrc
          ? (single.source.match(/\b_\b/g) ?? []).length
          : 0;
      const wildcardNote =
        wildcardCount > 0
          ? `  ·  +${wildcardCount} wildcard${wildcardCount === 1 ? '' : 's'}`
          : '';
      const badge = `🔍 ${verb} ${hit.qname}${wildcardNote}`;
      setGoalsComparisonPreview(uri, liveGoals, badge, single.outcome);
    }
    // Per-picker map: qname → resolved source (with wildcards if any).
    // Read by the standalone-mode insert path so the editor gets the
    // wildcard-padded source instead of the bare `verb qname.`.
    const pickedSourceFor = new Map<string, string>();

    function schedulePreview(hit: SearchHit): void {
      if (previewTimer) clearTimeout(previewTimer);
      previewTimer = setTimeout(() => void firePreview(hit), 150);
    }

    qp.onDidChangeActive(active => {
      if (active.length === 0) {
        clearPreview();
        return;
      }
      schedulePreview(active[0].hit);
    });

    // While the picker is open, expose the lemmaPickerOpen context
    // so the cycle keybinds (Cmd/Ctrl+Alt+]/[) and refine-args
    // keybind (Shift+Enter) fire commands instead of being inert.
    void vscode.commands.executeCommand(
      'setContext', 'easycrypt.lemmaPickerOpen', true,
    );
    // Tracks whether the user invoked refine-args (button click or
    // keybind) — set true when triggered, picker hides, and the outer
    // logic reads this flag to dispatch phase-3 instead of the normal
    // accept path.
    let refineArgsRequested = false;
    // Tracks whether the user toggled search mode via the title-bar
    // button — Stage 2 hides; outer loop re-enters Stage 1 to
    // re-dispatch with the new verb.
    let modeToggleRequested = false;
    activeLemmaPickerRefineHandler = () => {
      const sel = qp.selectedItems[0] ?? qp.activeItems[0];
      if (!sel) return;
      refineArgsRequested = true;
      // Resolve the picker with the current active hit; phase-3 runs
      // outside the loop using the hit data.
      qp.hide();
    };
    const picked = await new Promise<SearchHit | undefined>(resolve => {
      qp.onDidAccept(() => {
        const sel = qp.selectedItems[0] ?? qp.activeItems[0];
        resolve(sel?.hit);
        qp.hide();
      });
      qp.onDidTriggerButton((button) => {
        if (button === refineArgsButton) {
          activeLemmaPickerRefineHandler?.();
          return;
        }
        if (button === toggleModeButton) {
          // Flip mode + re-enter Stage 1's dispatch path (clearing
          // cached hits so a fresh search runs with the new verb).
          // autoRedispatch skips the InputBox prompt — we just want
          // the new verb dispatched against the same pattern.
          searchMode = searchMode === 'all' ? 'strict' : 'all';
          cachedDispatch = null;
          modeToggleRequested = true;
          autoRedispatch = true;
          qp.hide();
          return;
        }
      });
      qp.onDidHide(() => {
        void vscode.commands.executeCommand(
          'setContext', 'easycrypt.lemmaPickerOpen', false,
        );
        activeLemmaPickerRefineHandler = undefined;
        clearPreview();
        qp.dispose();
        // If refine-args was requested, the active hit is passed back
        // through the resolve path so the outer logic can dispatch.
        if (refineArgsRequested) {
          const sel = qp.selectedItems[0] ?? qp.activeItems[0];
          resolve(sel?.hit);
        } else {
          resolve(undefined);
        }
        // mode-toggle path: handled below via modeToggleRequested
        // flag. resolve(undefined) above lets the outer loop iterate;
        // we'll then re-enter Stage 1 (cachedDispatch is cleared).
      });
      qp.show();
      // VSCode's onDidChangeActive does not always fire for items set
      // programmatically before show() — single-result lists are the
      // canonical case (active[0] was already the active item, no
      // change). Manually kick off the preview for the initial active
      // item so the user always sees something.
      if (items.length > 0) {
        schedulePreview(items[0].hit);
      }
    });
    clearPreview();
    if (!picked) {
      // Esc returns to Stage 1 (loop continues with lastPattern set).
      continue;
    }

    // We have a hit. Branch on mode.
    if (opts.mode === 'display') {
      // Browse-only: closing on Enter is sufficient (the print panel
      // already shows the highlighted candidate's body). No insert.
      return picked.qname;
    }
    if (opts.mode === 'standalone') {
      // Refine-args path: hand off to phase-3 with the picked qname.
      // Pre-populate args from the auto-wildcard probe (if any) so
      // the user starts with `apply qname _ _ ...` matching what
      // their preview was showing — incrementally specialize from
      // there.
      if (refineArgsRequested && verb === 'apply') {
        const resolved = pickedSourceFor.get(picked.qname);
        let initialArgs: string[] = [];
        if (resolved) {
          // Strip prefix `apply qname ` and trailing `.` to get the
          // arg string; split into tokens (whitespace-only — does NOT
          // handle nested parens, but the probe only emits `_`s).
          const m = resolved.match(/^apply\s+\S+\s+(.+)\.$/);
          if (m) initialArgs = m[1].trim().split(/\s+/);
        }
        const insertPos = opts.insertPosition ?? editor.selection.active;
        const phase3Outcome = await runApplyPhase3({
          uri,
          qname: picked.qname,
          initialArgs,
          insertPosition: insertPos,
        });
        if (phase3Outcome === 'rollback') {
          // User pressed Esc in phase-3; jump directly back to
          // Stage 2 (the QuickPick of hits) — skip Stage 1's
          // pattern InputBox + redispatch since we already have
          // hits cached.
          skipToStage2 = true;
          continue;
        }
        // 'committed' — source was inserted by phase-3 itself.
        return picked.qname;
      }
      // Use the wildcard-resolved source captured during preview, so
      // `apply foo` that needs `apply foo _ _.` inserts the working
      // form. Falls back to bare `verb qname.` if no preview ran
      // (shouldn't happen — picker always previews on activation).
      const resolved = pickedSourceFor.get(picked.qname) ?? `${verb} ${picked.qname}.`;
      const insertPos = opts.insertPosition ?? editor.selection.active;
      await editor.edit(b => b.insert(insertPos, resolved + '\n'));
      return picked.qname;
    }
    // token-return: prompt for direction (rewrite only).
    //
    // Four options: forward / reverse, each with an optional repeat
    // (`!`) modifier. EC syntax:
    //   forward, once   → `<qname>`
    //   reverse, once   → `-<qname>`
    //   forward, repeat → `!<qname>`
    //   reverse, repeat → `!-<qname>`
    //
    // Hovering over each item live-previews that specific direction
    // via the parent's previewSourceBuilder (so `proc rewrite` etc.
    // contexts see the actual targeted-instruction effect).
    //
    // singleDirection: skip stage 3 entirely and return the bare
    // qname. Used by proc-rewrite where EC's tactic doesn't accept
    // direction modifiers.
    if (verb === 'rewrite' && opts.singleDirection) {
      return picked.qname;
    }
    if (verb === 'rewrite') {
      interface DirItem extends vscode.QuickPickItem {
        token: string;
      }
      const dirItems: DirItem[] = [
        {
          label: '→ Forward',
          description: `rewrite ${picked.qname}.`,
          token: picked.qname,
        },
        {
          label: '← Reverse',
          description: `rewrite -${picked.qname}.`,
          token: `-${picked.qname}`,
        },
        {
          label: '→! Forward · repeat',
          description: `rewrite !${picked.qname}.`,
          token: `!${picked.qname}`,
        },
        {
          label: '←! Reverse · repeat',
          description: `rewrite !-${picked.qname}.`,
          token: `!-${picked.qname}`,
        },
      ];
      const dirPick = vscode.window.createQuickPick<DirItem>();
      dirPick.title = `EasyCrypt: rewrite ${picked.qname} — direction`;
      dirPick.placeholder = 'Esc cancels (returns to pattern stage). Hover to preview.';
      dirPick.matchOnDescription = true;
      dirPick.items = dirItems;
      dirPick.activeItems = [dirItems[0]];

      // Per-direction preview wiring. Reuse the same buildSrc /
      // probe path as stage-2 firePreview by calling the parent's
      // previewSourceBuilder with the modified token. We dispatch
      // a single comparison preview (NOT pair) so the user sees
      // exactly what THIS direction does.
      const dirBuildSrc =
        opts.previewSourceBuilder ?? ((q: string) => `${verb} ${q}.`);
      let dirPreviewSeq = 0;
      let dirPreviewTimer: NodeJS.Timeout | undefined;
      async function fireDirPreview(token: string): Promise<void> {
        const seq = ++dirPreviewSeq;
        const src = dirBuildSrc(token);
        const result = await withClient(c =>
          c.sendRequest<TryTacticResponse>('easycrypt/proof/tryTactic', {
            uri, source: src, expectedCas: null,
          }),
        );
        if (seq !== dirPreviewSeq) return;
        const badge = `🔍 ${src.replace(/\.$/, '')}`;
        const outcome: ComparisonOutcome =
          result?.outcome === 'ok' && result.goalsAfter
            ? { kind: 'success', newGoals: result.goalsAfter,
                closedFocused: result.closedFocused === true,
                cycleIndex: 0 }
            : { kind: 'error',
                errorKind: classifyTacticError((result?.error ?? 'tactic failed').trim()),
                error: (result?.error ?? 'tactic failed').trim() };
        setGoalsComparisonPreview(uri, liveGoals, badge, outcome);
      }
      function scheduleDirPreview(token: string): void {
        if (dirPreviewTimer) clearTimeout(dirPreviewTimer);
        dirPreviewTimer = setTimeout(() => void fireDirPreview(token), 150);
      }
      dirPick.onDidChangeActive(active => {
        if (active.length === 0) return;
        scheduleDirPreview(active[0].token);
      });
      // Fire the initial preview for the first item (Forward).
      scheduleDirPreview(dirItems[0].token);

      // Resolve in onDidAccept BEFORE hide() to avoid the race
      // where dispose() inside onDidAccept synchronously fires
      // onDidHide → resolves with undefined first. Pattern
      // matches the stage-2 lemma-picker promise wiring above.
      let dirAccepted = false;
      const dirToken = await new Promise<string | undefined>((resolve) => {
        dirPick.onDidAccept(() => {
          const sel = dirPick.activeItems[0];
          dirAccepted = true;
          resolve(sel?.token);
          dirPick.hide();
        });
        dirPick.onDidHide(() => {
          if (dirPreviewTimer) clearTimeout(dirPreviewTimer);
          dirPick.dispose();
          if (!dirAccepted) resolve(undefined);
        });
        dirPick.show();
      });
      if (dirToken === undefined) continue;  // back to Stage 1
      return dirToken;
    }
    // apply mode in token-return shouldn't really fire (apply isn't
    // a rewrite-builder subcommand) but handle for safety.
    return picked.qname;
  }
}

// Toggle the prettify display setting. Workspace-scoped if a
// workspace is open; falls back to global. Configuration-change
// watcher (registered in activate) re-renders open webviews
// automatically. No keybind by default — command-palette accessible
// via "EasyCrypt: Toggle Prettify Display".
async function handleTogglePrettify(): Promise<void> {
  const cfg = vscode.workspace.getConfiguration('easycrypt-tooling.display');
  const current = cfg.get<boolean>('prettify', true);
  const target = (vscode.workspace.workspaceFolders?.length ?? 0) > 0
    ? vscode.ConfigurationTarget.Workspace
    : vscode.ConfigurationTarget.Global;
  await cfg.update('prettify', !current, target);
  vscode.window.setStatusBarMessage(
    `EasyCrypt: prettify ${!current ? 'on' : 'off'}`,
    1500,
  );
}

// Toggle program-wrap mode (wrap ↔ scroll). Bound to Cmd/Ctrl+Alt+Z
// by default. Re-renders via the existing config-change watcher.
async function handleToggleProgramWrap(): Promise<void> {
  const cfg = vscode.workspace.getConfiguration('easycrypt-tooling.display');
  const current = cfg.get<'wrap' | 'scroll'>('programWrap', 'wrap');
  const next: 'wrap' | 'scroll' = current === 'wrap' ? 'scroll' : 'wrap';
  const target = (vscode.workspace.workspaceFolders?.length ?? 0) > 0
    ? vscode.ConfigurationTarget.Workspace
    : vscode.ConfigurationTarget.Global;
  await cfg.update('programWrap', next, target);
  vscode.window.setStatusBarMessage(
    `EasyCrypt: program ${next}`,
    1500,
  );
}

async function handleApplyLemma(): Promise<void> {
  const editor = activeEcEditor();
  if (!editor) return;
  await runLemmaPicker({
    uri: editor.document.uri.toString(),
    verb: 'apply',
    mode: 'standalone',
    insertPosition: editor.selection.active,
  });
}

// ---- Ephemeral term editor (popup) ---------------------------------
//
// Reusable primitive: open a small horizontal webview with a multi-line
// textarea, let the user edit, return the edited value (or undefined
// on cancel). Used by builders' "??" sentinel for paste-this-formula
// flows; will eventually host hover-to-edit, local-edit-mode,
// program-printing v1 inline editor, etc.
//
// Lifecycle: created and disposed per call. No persistent state.
// Dispose-on-commit/cancel keeps the editor surface clean — no leftover
// untitled tabs.

interface EditTermPopupOpts {
  initialValue: string;
  title?: string;
  // Hint shown above the textarea (e.g., "Edit slot: <path>").
  contextHint?: string;
}

async function editTermInPopup(opts: EditTermPopupOpts): Promise<string | undefined> {
  return new Promise((resolve) => {
    const panel = vscode.window.createWebviewPanel(
      'easycrypt.termEdit',
      opts.title ?? 'EasyCrypt: Edit term',
      { viewColumn: vscode.ViewColumn.Beside, preserveFocus: false },
      { enableScripts: true, retainContextWhenHidden: false },
    );
    let resolved = false;
    const finish = (value: string | undefined) => {
      if (resolved) return;
      resolved = true;
      try { panel.dispose(); } catch (_) { /* already disposed */ }
      resolve(value);
    };
    panel.webview.html = `<!DOCTYPE html><html><head><style>
      body {
        font-family: var(--vscode-editor-font-family, monospace);
        font-size: var(--vscode-editor-font-size, 13px);
        color: var(--vscode-editor-foreground);
        background: var(--vscode-editor-background);
        padding: 0.6em 1em;
        margin: 0;
      }
      .hint {
        color: var(--vscode-descriptionForeground);
        font-size: 0.85em;
        margin-bottom: 0.4em;
      }
      textarea {
        width: 100%;
        min-height: 6em;
        max-height: 60vh;
        font-family: var(--vscode-editor-font-family, monospace);
        font-size: var(--vscode-editor-font-size, 13px);
        background: var(--vscode-input-background);
        color: var(--vscode-input-foreground);
        border: 1px solid var(--vscode-input-border, transparent);
        padding: 0.4em 0.6em;
        box-sizing: border-box;
        resize: vertical;
      }
      .buttons {
        margin-top: 0.5em;
        display: flex;
        gap: 0.5em;
      }
      button {
        background: var(--vscode-button-background);
        color: var(--vscode-button-foreground);
        border: none;
        padding: 0.3em 0.8em;
        cursor: pointer;
        border-radius: 3px;
        font-size: 0.95em;
      }
      button:hover { background: var(--vscode-button-hoverBackground); }
      button.cancel {
        background: var(--vscode-button-secondaryBackground, var(--vscode-button-background));
        color: var(--vscode-button-secondaryForeground, var(--vscode-button-foreground));
      }
      button.cancel:hover {
        background: var(--vscode-button-secondaryHoverBackground, var(--vscode-button-hoverBackground));
      }
      .keyhint {
        color: var(--vscode-descriptionForeground);
        font-size: 0.8em;
        margin-left: 0.5em;
        align-self: center;
      }
    </style></head>
    <body>
      ${opts.contextHint ? `<div class="hint">${escapeHtml(opts.contextHint)}</div>` : ''}
      <textarea id="ed">${escapeHtml(opts.initialValue)}</textarea>
      <div class="buttons">
        <button onclick="commit()">📥 Commit</button>
        <button class="cancel" onclick="cancel()">Cancel</button>
        <span class="keyhint">Cmd/Ctrl+Enter to commit · Esc to cancel</span>
      </div>
      <script>
        const vscode = acquireVsCodeApi();
        const ed = document.getElementById('ed');
        ed.focus();
        ed.setSelectionRange(ed.value.length, ed.value.length);
        function commit() { vscode.postMessage({ cmd: 'commit', value: ed.value }); }
        function cancel() { vscode.postMessage({ cmd: 'cancel' }); }
        ed.addEventListener('keydown', (e) => {
          if (e.key === 'Enter' && (e.metaKey || e.ctrlKey)) {
            e.preventDefault(); commit();
          } else if (e.key === 'Escape') {
            e.preventDefault(); cancel();
          }
        });
      </script>
    </body></html>`;
    panel.webview.onDidReceiveMessage((msg) => {
      if (!msg) return;
      if (msg.cmd === 'commit') finish(typeof msg.value === 'string' ? msg.value : '');
      else if (msg.cmd === 'cancel') finish(undefined);
    });
    panel.onDidDispose(() => { finish(undefined); });
  });
}

// ---- Apply phase-3 arg builder -------------------------------------
//
// After the lemma picker accepts a hit, Shift+Enter (or the title-bar
// "Refine args" button) hands off to this: incremental construction
// of `apply <qname> arg1 arg2 ...` with addressable per-arg editing.
//
// v0 scope: flat (single-level) args — each token can be a leaf
// (qname, wildcard, term) or a `??`-sentinel-edited paste-from-popup.
// Recursive sub-app entry (sentinels `(` / `)`) and folded strip
// rendering for nested apps deferred to next pass; user falls back
// to popup-paste for nested cases.
//
// Backtracking: addressable. `<<` / `>>` sentinels (or the title-bar
// arrow buttons) move position WITHIN the existing token list without
// deleting later tokens. Enter at the end appends; Enter at a non-end
// position REPLACES the token at that position.
//
// Sentinels:
//   ?     open lemma picker, returned qname becomes the next token
//   _     wildcard token (single)
//   ??    open ephemeral popup pre-loaded with current token's value,
//         commit on close replaces the current token
//   <<    move position back one (without deleting)
//   >>    move position forward one
// All exact-match-on-Enter; longer inputs are literal tokens.

interface ApplyPhase3Opts {
  uri: string;
  qname: string;                       // the picked lemma
  initialArgs?: string[];              // pre-populated (e.g., from auto-wildcard probe)
  insertPosition: vscode.Position;
}

// Outcome of phase-3:
//   'committed' — user finalized (Enter on empty at end), source inserted
//   'rollback'  — user pressed Esc, wants to go back to phase-2 picker
type ApplyPhase3Outcome = 'committed' | 'rollback';

// Wrap args in parens when present: EC's `apply` parser sometimes
// needs `apply (lemma arg1 arg2).` to resolve unification correctly,
// especially when args themselves are applications. Bare
// `apply lemma.` (no args) stays unwrapped.
function cumulativeApplyPhase3(qname: string, args: string[]): string {
  if (args.length === 0) return `apply ${qname}.`;
  return `apply (${qname} ${args.join(' ')}).`;
}

// Render the arg strip with a position marker. Active position is
// highlighted with ▶...◀ marker; appending position (== args.length)
// is shown as ▶[…]◀ at the end.
function renderArgStrip(qname: string, args: string[], position: number): string {
  const cells = args.map((a, i) =>
    i === position ? `▶[${a}]◀` : `[${a}]`,
  );
  if (position === args.length) cells.push('▶[…]◀');
  return `apply ${qname}  ${cells.join('  ')}`;
}

async function runApplyPhase3(opts: ApplyPhase3Opts): Promise<ApplyPhase3Outcome> {
  const { uri, qname, insertPosition } = opts;
  const editor = activeEcEditor();
  if (!editor) return 'rollback';

  // Open / refresh goal pane for live preview.
  ensureGoalsPanel();
  void fetchAndRenderGoals(uri);
  // Cache live goals for comparison view's err context.
  let liveGoals: GoalsResponse | null = null;
  void (async () => {
    const r = await withClient(c =>
      c.sendRequest<GoalsResponse>('easycrypt/proof/goals', { uri }),
    );
    if (r) liveGoals = r;
  })();

  const args: string[] = (opts.initialArgs ?? []).slice();
  let position = args.length;  // start in append mode at the end
  let currentValue = '';
  let validateSeq = 0;
  let debounceTimer: NodeJS.Timeout | undefined;
  // intentionallyHiding: true while we're hiding the input to launch a
  // sub-picker / popup — prevents onDidHide from disposing the input
  // (which would prevent input.show() from re-displaying it). Reset
  // to false once the sub-flow completes.
  let intentionallyHiding = false;

  const prevButton: vscode.QuickInputButton = {
    iconPath: new vscode.ThemeIcon('arrow-left'),
    tooltip: 'Move position back (<<)',
  };
  const nextButton: vscode.QuickInputButton = {
    iconPath: new vscode.ThemeIcon('arrow-right'),
    tooltip: 'Move position forward (>>)',
  };
  const popupButton: vscode.QuickInputButton = {
    iconPath: new vscode.ThemeIcon('edit'),
    tooltip: 'Edit current token in a popup (??)',
  };
  const removeButton: vscode.QuickInputButton = {
    iconPath: new vscode.ThemeIcon('trash'),
    tooltip: 'Delete current token',
  };
  const pickerButton: vscode.QuickInputButton = {
    iconPath: new vscode.ThemeIcon('search'),
    tooltip: 'Open lemma picker (?)',
  };

  const input = vscode.window.createInputBox();
  input.title = `EasyCrypt: refine args for ${qname}`;

  function refreshUI() {
    input.prompt = renderArgStrip(qname, args, position);
    input.placeholder =
      position < args.length
        ? `editing arg ${position + 1} of ${args.length}. Enter replaces. <</>> navigates. ?/?? subcommand. Enter on empty deletes.`
        : `appending arg ${args.length + 1}. Enter commits. ? lemma picker, _ wildcard, ?? popup. Enter on empty finalizes.`;
    const buttons: vscode.QuickInputButton[] = [];
    if (position > 0) buttons.push(prevButton);
    if (position < args.length) buttons.push(nextButton);
    if (position < args.length) buttons.push(removeButton);
    buttons.push(pickerButton);
    buttons.push(popupButton);
    input.buttons = buttons;
  }

  // Run the cumulative source through tryTactic; update preview pane.
  async function refreshPreview(): Promise<void> {
    const seq = ++validateSeq;
    input.busy = true;
    const cumulative = cumulativeApplyPhase3(qname, args);
    const result = await withClient(c =>
      c.sendRequest<TryTacticResponse>('easycrypt/proof/tryTactic', {
        uri,
        source: cumulative,
        expectedCas: null,
      }),
    );
    if (seq !== validateSeq) return;
    input.busy = false;
    if (!result) return;
    const badge = `🔍 ${cumulative}`;
    if (result.outcome === 'ok' && result.goalsAfter) {
      setGoalsComparisonPreview(uri, liveGoals, badge, {
        kind: 'success',
        newGoals: result.goalsAfter,
        closedFocused: result.closedFocused === true,
        cycleIndex: 0,
      });
    } else {
      const err = (result.error ?? 'tactic failed').trim();
      // Mirror the full error to the 'apply' Output channel — the
      // goal-pane comparison view shows the error inline, but the
      // channel preserves history across this and other apply
      // flows (selectable via easycrypt.proof.previewLog.show).
      logPreviewError('apply', cumulative, err);
      setGoalsComparisonPreview(uri, liveGoals, badge, {
        kind: 'error',
        errorKind: classifyTacticError(err),
        error: err,
      });
    }
  }

  // Apply a candidate token at the current position. Returns true if
  // the token was inserted/replaced, false if user wants to retry.
  async function commitToken(token: string): Promise<void> {
    if (position < args.length) {
      args[position] = token;
      position += 1;
    } else {
      args.push(token);
      position += 1;
    }
    input.value = '';
    currentValue = '';
    refreshUI();
    void refreshPreview();
  }

  async function loadCurrentTokenIntoInput(): Promise<void> {
    if (position < args.length) {
      input.value = args[position];
      currentValue = args[position];
    } else {
      input.value = '';
      currentValue = '';
    }
  }

  async function openPopupForCurrent(): Promise<void> {
    // Pre-load: when editing an existing token, use its current
    // value. When appending (position == args.length), use whatever
    // the user has typed in currentValue — UNLESS that's the `??`
    // sentinel itself (or `?`), in which case start with an empty
    // textarea (the sentinel was the trigger, not content the user
    // wanted to keep).
    const triggered = currentValue.trim();
    const isSentinelTrigger = triggered === '??' || triggered === '?';
    const initial =
      position < args.length
        ? args[position]
        : (isSentinelTrigger ? '' : triggered);
    intentionallyHiding = true;
    input.hide();
    const edited = await editTermInPopup({
      initialValue: initial,
      title: `EasyCrypt: edit arg ${position + 1} for ${qname}`,
      contextHint: `apply ${qname} — arg ${position + 1}${position < args.length ? ' (replacing)' : ' (new)'}`,
    });
    intentionallyHiding = false;
    // Clear any pre-typed sentinel BEFORE re-showing so the input
    // doesn't carry the `??` trigger.
    input.value = '';
    currentValue = '';
    input.show();
    if (edited === undefined) return;
    const trimmed = edited.trim();
    if (trimmed === '') return;
    await commitToken(trimmed);
  }

  async function openPickerForCurrent(): Promise<void> {
    intentionallyHiding = true;
    input.hide();
    const picked = await runLemmaPicker({
      uri,
      verb: 'apply',
      mode: 'token-return',
    });
    intentionallyHiding = false;
    input.value = '';
    currentValue = '';
    input.show();
    if (picked === undefined) return;
    await commitToken(picked);
  }

  function moveBack() {
    if (position > 0) {
      position -= 1;
      void loadCurrentTokenIntoInput();
      refreshUI();
    }
  }
  function moveForward() {
    if (position < args.length) {
      position += 1;
      void loadCurrentTokenIntoInput();
      refreshUI();
    }
  }
  function deleteCurrent() {
    if (position < args.length) {
      args.splice(position, 1);
      // Position stays — now points at the next token (or end).
      void loadCurrentTokenIntoInput();
      refreshUI();
      void refreshPreview();
    }
  }

  return new Promise<ApplyPhase3Outcome>((resolve) => {
    let resolved = false;
    const finish = (outcome: ApplyPhase3Outcome) => {
      if (resolved) return;
      resolved = true;
      if (debounceTimer) clearTimeout(debounceTimer);
      clearGoalsPreview(uri);
      try { input.dispose(); } catch (_) { /* already disposed */ }
      resolve(outcome);
    };

    input.onDidChangeValue((v) => {
      currentValue = v;
    });

    input.onDidAccept(async () => {
      const value = currentValue.trim();
      // Sentinel exact-match dispatch.
      switch (value) {
        case '?':  await openPickerForCurrent(); return;
        case '??': await openPopupForCurrent();  return;
        case '<<': moveBack();    input.value = ''; currentValue = ''; return;
        case '>>': moveForward(); input.value = ''; currentValue = ''; return;
      }
      if (value === '') {
        // Empty Enter: at end → finalize; mid-list → delete current token.
        if (position < args.length) {
          deleteCurrent();
          return;
        }
        // Finalize and insert.
        const finalSource = cumulativeApplyPhase3(qname, args);
        await editor.edit(b => b.insert(insertPosition, finalSource + '\n'));
        finish('committed');
        return;
      }
      // Literal token commit / replace.
      await commitToken(value);
    });

    input.onDidTriggerButton(async (button) => {
      if (button === prevButton)   { moveBack();    input.value = ''; currentValue = ''; return; }
      if (button === nextButton)   { moveForward(); input.value = ''; currentValue = ''; return; }
      if (button === removeButton) { deleteCurrent(); return; }
      if (button === pickerButton) { await openPickerForCurrent(); return; }
      if (button === popupButton)  { await openPopupForCurrent();  return; }
    });

    input.onDidHide(() => {
      // If we're hiding intentionally to launch a sub-picker / popup,
      // do NOT dispose — the sub-flow will re-show this input on
      // completion. Dispose only on real user-initiated dismiss.
      if (intentionallyHiding) return;
      finish('rollback');
    });

    input.show();
    refreshUI();
    void loadCurrentTokenIntoInput();
    void refreshPreview();
  });
}

// ---- Proc rewrite (right-click "Rewrite at line N") ---------------
//
// Drives an InputBox titled "proc rewrite at <codepos>" where the
// user types a single pterm (lemma name, term, or `?` to open the
// lemma picker). On commit, synthesizes
// `proc rewrite{side}? <codepos> <pterm>.` and inserts at cursor.
// Empty input commits the simplify form `proc rewrite ... /=.`.
//
// Speculation: tryTactic is fired on each typed token so the goal
// pane shows the post-tactic state live. Schema is built dynamically
// because cumulative depends on side + codepos.

interface ProcRewriteOpts {
  uri: string;
  insertPosition: vscode.Position;
  side: MsgProgSide;
  codepos: MsgCodepos;
  // Pre-resolved editor (see BuilderOpts.editor). Pass when
  // launching from the goal pane webview right-click flow.
  editor?: vscode.TextEditor;
}

async function runProcRewrite(opts: ProcRewriteOpts): Promise<void> {
  const { uri, insertPosition, side, codepos, editor } = opts;
  const cpStr = ecCodeposSource(codepos);
  const sideStr = side === 'none' ? '' : ` {${side === 'left' ? '1' : '2'}}`;
  const sideLabel = side === 'none' ? '' : `${side === 'left' ? '{1} ' : '{2} '}`;
  // Route through the same 5-slot builder as the regular rewrite
  // tactic, with the prefix set to the proc-rewrite header so the
  // assembled args compose into `proc rewrite{side} <codepos>
  // <args…>.`. Note: EC's current `process_rewrite_rw` accepts only
  // a bare pterm (no rwside / rwrepeat / rwocc / rwmatch) — using
  // any of those slots will preview-fail as a parse error until
  // EC parity work lands. The UX itself is fully consistent with
  // the regular builder; UX is what the line-selection flow
  // promised.
  await runRewriteBuilder({
    uri,
    insertPosition,
    editor,
    tacticPrefix: `proc rewrite${sideStr} ${cpStr}`,
    title: `proc rewrite ${sideLabel}at ${cpStr}`,
  });
}

// ---- Proc change (right-click "Change [range]") -------------------
//
// Multi-line popup: textarea for replacement instructions + var-row
// panel + "+ Add var" button + live validity badge. Validity is
// classified per-edit via tryTactic; the popup is non-modal but
// blocks the change-flow promise until commit / cancel.
//
// Preview philosophy (per user): show OLD code (read-only context)
// + new vars + validity. Do NOT render the new program — large
// programs would make this unusable.

interface ProcChangeOpts {
  uri: string;
  insertPosition: vscode.Position;
  side: MsgProgSide;
  codepos: MsgCodepos;
  cpos1End: number;
  // Old-code context to render at the top of the popup. Strings
  // are pre-tokenized HTML lines from the goal pane. Empty list
  // is acceptable (caller couldn't extract context — popup falls
  // back to a single-line label).
  oldCodeLines: string[];
  // Render target for the popup header.
  rangeLabel: string;  // e.g., "2..4" or "2"
  // Pre-resolved editor for the commit path (see BuilderOpts.editor).
  // Pass when launching from the goal pane webview right-click flow,
  // where activeTextEditor would be the webview itself.
  editor?: vscode.TextEditor;
}

async function runProcChange(opts: ProcChangeOpts): Promise<void> {
  const { uri, insertPosition, side, codepos, cpos1End,
          oldCodeLines, rangeLabel, editor: optEditor } = opts;
  return new Promise<void>((resolve) => {
    const panel = vscode.window.createWebviewPanel(
      'easycrypt.procChange',
      `EasyCrypt: proc change ${rangeLabel}`,
      { viewColumn: vscode.ViewColumn.Beside, preserveFocus: false },
      { enableScripts: true, retainContextWhenHidden: false },
    );
    let resolved = false;
    const finish = () => {
      if (resolved) return;
      resolved = true;
      try { panel.dispose(); } catch (_) { /* already disposed */ }
      resolve();
    };
    const sideLabel = side === 'none' ? '' : ` {${side === 'left' ? '1' : '2'}}`;
    const oldHtml = oldCodeLines.length === 0
      ? `<div class="ctx-empty">(old code: line ${rangeLabel})</div>`
      : oldCodeLines.map((html, i) =>
          `<div class="ctx-line">` +
          `<span class="ctx-num">${i + 1}</span>` +
          `<span class="ctx-code">${html}</span>` +
          `</div>`).join('');
    panel.webview.html = `<!DOCTYPE html><html><head><style>
      body {
        font-family: var(--vscode-editor-font-family, monospace);
        font-size: var(--vscode-editor-font-size, 13px);
        color: var(--vscode-editor-foreground);
        background: var(--vscode-editor-background);
        padding: 0.6em 1em;
        margin: 0;
      }
      .header {
        font-weight: bold;
        color: var(--vscode-textLink-foreground);
        margin-bottom: 0.3em;
      }
      .hint {
        color: var(--vscode-descriptionForeground);
        font-size: 0.85em;
        margin-bottom: 0.4em;
      }
      .section { margin: 0.5em 0; }
      .section-label {
        color: var(--vscode-descriptionForeground);
        font-size: 0.8em;
        text-transform: uppercase;
        letter-spacing: 0.05em;
        margin-bottom: 0.2em;
      }
      .ctx-frame {
        background: var(--vscode-textCodeBlock-background, rgba(127,127,127,0.07));
        padding: 0.4em 0.6em;
        border-left: 3px solid var(--vscode-panel-border);
        max-height: 25vh;
        overflow: auto;
      }
      .ctx-line { display: grid; grid-template-columns: 2.5em 1fr; gap: 0.5em; }
      .ctx-num {
        color: var(--vscode-editorLineNumber-foreground);
        text-align: right;
      }
      .ctx-empty { color: var(--vscode-descriptionForeground); font-style: italic; }
      textarea {
        width: 100%;
        min-height: 6em;
        max-height: 40vh;
        font-family: var(--vscode-editor-font-family, monospace);
        font-size: var(--vscode-editor-font-size, 13px);
        background: var(--vscode-input-background);
        color: var(--vscode-input-foreground);
        border: 1px solid var(--vscode-input-border, transparent);
        padding: 0.4em 0.6em;
        box-sizing: border-box;
        resize: vertical;
      }
      .vars { margin-top: 0.3em; }
      .vars-row {
        display: flex;
        gap: 0.4em;
        margin-bottom: 0.25em;
        align-items: center;
      }
      .vars-row input {
        flex: 1 1 auto;
        font-family: var(--vscode-editor-font-family, monospace);
        background: var(--vscode-input-background);
        color: var(--vscode-input-foreground);
        border: 1px solid var(--vscode-input-border, transparent);
        padding: 0.2em 0.4em;
      }
      .vars-row input.var-names { flex: 2 1 auto; }
      .vars-row input.var-ty { flex: 1 1 auto; }
      .vars-row button { padding: 0.15em 0.5em; }
      .add-var {
        background: var(--vscode-button-secondaryBackground, var(--vscode-button-background));
        color: var(--vscode-button-secondaryForeground, var(--vscode-button-foreground));
        border: none;
        padding: 0.25em 0.7em;
        cursor: pointer;
        border-radius: 3px;
        font-size: 0.9em;
        margin-top: 0.25em;
      }
      .badge {
        display: inline-block;
        padding: 0.15em 0.5em;
        border-radius: 3px;
        font-size: 0.85em;
        font-weight: bold;
        margin-left: 0.5em;
      }
      .badge-ok { background: var(--vscode-charts-green, #89d185); color: #000; }
      .badge-parse {
        background: var(--vscode-errorForeground, #f48771); color: #000;
      }
      .badge-scope {
        background: var(--vscode-list-warningForeground, #f0b461); color: #000;
      }
      .badge-sem {
        background: var(--vscode-charts-yellow, #d6c200); color: #000;
      }
      .badge-pending {
        background: var(--vscode-descriptionForeground, #999); color: #fff;
      }
      .err-detail {
        margin-top: 0.3em;
        white-space: pre-wrap;
        max-height: 10vh;
        overflow: auto;
        font-size: 0.85em;
        color: var(--vscode-errorForeground, #f48771);
        font-family: var(--vscode-editor-font-family, monospace);
      }
      .buttons { margin-top: 0.5em; display: flex; gap: 0.5em; align-items: center; }
      button.commit, button.cancel {
        background: var(--vscode-button-background);
        color: var(--vscode-button-foreground);
        border: none;
        padding: 0.3em 0.8em;
        cursor: pointer;
        border-radius: 3px;
        font-size: 0.95em;
      }
      button.commit:hover { background: var(--vscode-button-hoverBackground); }
      button.cancel {
        background: var(--vscode-button-secondaryBackground, var(--vscode-button-background));
        color: var(--vscode-button-secondaryForeground, var(--vscode-button-foreground));
      }
      button.cancel:hover {
        background: var(--vscode-button-secondaryHoverBackground, var(--vscode-button-hoverBackground));
      }
      .keyhint {
        color: var(--vscode-descriptionForeground);
        font-size: 0.8em;
        margin-left: 0.5em;
      }
    </style></head>
    <body>
      <div class="header">proc change${sideLabel} ${escapeHtml(rangeLabel)}</div>
      <div class="hint">Replace the selected range with new instructions. Add vars to bind locals usable in the replacement.</div>
      <div class="section">
        <div class="section-label">old code (read-only)</div>
        <div class="ctx-frame">${oldHtml}</div>
      </div>
      <div class="section">
        <div class="section-label">new instructions <span id="badge" class="badge badge-pending">…</span></div>
        <textarea id="instr" placeholder="instr1; instr2; …"></textarea>
        <div id="errDetail" class="err-detail"></div>
      </div>
      <div class="section">
        <div class="section-label">vars (optional)</div>
        <div id="vars" class="vars"></div>
        <button class="add-var" onclick="addVar()">+ Add var</button>
      </div>
      <div class="buttons">
        <button class="commit" onclick="commit()">📥 Commit</button>
        <button class="cancel" onclick="cancel()">Cancel</button>
        <span class="keyhint">Cmd/Ctrl+Enter to commit · Esc to cancel</span>
      </div>
      <script>
        const vscode = acquireVsCodeApi();
        const ed = document.getElementById('instr');
        const varsBox = document.getElementById('vars');
        const badge = document.getElementById('badge');
        const errDetail = document.getElementById('errDetail');
        ed.focus();
        let probeSeq = 0;
        function readVars() {
          const out = [];
          varsBox.querySelectorAll('.vars-row').forEach((r) => {
            const namesIn = r.querySelector('.var-names');
            const tyIn = r.querySelector('.var-ty');
            const names = (namesIn.value || '').split(',').map(s => s.trim()).filter(s => s !== '');
            const ty = (tyIn.value || '').trim();
            if (names.length > 0 && ty !== '') out.push({ names, ty });
          });
          return out;
        }
        function addVar() {
          const row = document.createElement('div');
          row.className = 'vars-row';
          row.innerHTML =
            '<input class="var-names" placeholder="x, y, z (comma-separated)" />' +
            '<input class="var-ty" placeholder="int" />' +
            '<button onclick="this.parentElement.remove(); probeNow();">✕</button>';
          varsBox.appendChild(row);
          row.querySelector('.var-names').addEventListener('input', probeDeb);
          row.querySelector('.var-ty').addEventListener('input', probeDeb);
        }
        function commit() {
          vscode.postMessage({ cmd: 'commit',
                               instructions: ed.value,
                               vars: readVars() });
        }
        function cancel() { vscode.postMessage({ cmd: 'cancel' }); }
        let debTimer;
        function probeDeb() {
          if (debTimer) clearTimeout(debTimer);
          debTimer = setTimeout(probeNow, 400);
        }
        function probeNow() {
          probeSeq++;
          const seq = probeSeq;
          badge.className = 'badge badge-pending';
          badge.textContent = '…';
          errDetail.textContent = '';
          vscode.postMessage({ cmd: 'probe', seq,
                               instructions: ed.value, vars: readVars() });
        }
        ed.addEventListener('input', probeDeb);
        ed.addEventListener('keydown', (e) => {
          if (e.key === 'Enter' && (e.metaKey || e.ctrlKey)) {
            e.preventDefault(); commit();
          } else if (e.key === 'Escape') {
            e.preventDefault(); cancel();
          }
        });
        window.addEventListener('message', (ev) => {
          const m = ev.data;
          if (!m || m.cmd !== 'probeResult') return;
          if (m.seq !== probeSeq) return;
          if (m.status === 'ok') {
            badge.className = 'badge badge-ok'; badge.textContent = '✓ valid';
            errDetail.textContent = '';
          } else if (m.status === 'parse-err') {
            badge.className = 'badge badge-parse'; badge.textContent = 'parse error';
            errDetail.textContent = m.errText || '';
          } else if (m.status === 'scope-err') {
            badge.className = 'badge badge-scope'; badge.textContent = 'unbound name';
            errDetail.textContent = m.errText || '';
          } else if (m.status === 'sem-err') {
            badge.className = 'badge badge-sem'; badge.textContent = 'tactic refused';
            errDetail.textContent = m.errText || '';
          } else {
            badge.className = 'badge badge-pending'; badge.textContent = m.status || '…';
            errDetail.textContent = m.errText || '';
          }
        });
      </script>
    </body></html>`;

    panel.webview.onDidReceiveMessage(async (msg) => {
      if (!msg) return;
      if (msg.cmd === 'cancel') { finish(); return; }
      if (msg.cmd === 'commit') {
        const stmts = (msg.instructions ?? '')
          .split(/\n|;/).map((s: string) => s.trim()).filter((s: string) => s !== '');
        const bindings: ProcChangeBinding[] = (msg.vars ?? []) as ProcChangeBinding[];
        const src = procChangeSource(side, codepos, cpos1End, bindings, stmts);
        const editor = optEditor ?? activeEcEditor();
        if (editor) {
          await editor.edit((e) => {
            e.insert(insertPosition, src + '\n');
          });
        } else {
          // Fallback: copy to clipboard so the user doesn't lose work.
          await vscode.env.clipboard.writeText(src);
          vscode.window.showWarningMessage(
            'EasyCrypt: no active editor; proc change source copied to clipboard.',
          );
        }
        finish();
        return;
      }
      if (msg.cmd === 'probe') {
        const seq = msg.seq;
        const stmts = (msg.instructions ?? '')
          .split(/\n|;/).map((s: string) => s.trim()).filter((s: string) => s !== '');
        const bindings: ProcChangeBinding[] = (msg.vars ?? []) as ProcChangeBinding[];
        if (stmts.length === 0) {
          panel.webview.postMessage({ cmd: 'probeResult', seq,
                                      status: 'pending', errText: '(empty)' });
          return;
        }
        const src = procChangeSource(side, codepos, cpos1End, bindings, stmts);
        try {
          const r = await withClient(c =>
            c.sendRequest<TryTacticResponse>('easycrypt/proof/tryTactic', {
              uri, source: src, expectedCas: null,
            }),
          );
          const status = classifyChangeProbe(r?.outcome, r?.error ?? undefined);
          panel.webview.postMessage({ cmd: 'probeResult', seq, status,
                                      errText: r?.error ?? '' });
        } catch (e) {
          panel.webview.postMessage({ cmd: 'probeResult', seq,
                                      status: 'sem-err',
                                      errText: e instanceof Error ? e.message : String(e) });
        }
      }
    });
    panel.onDidDispose(() => { finish(); });
  });
}

// ---- Print panel ----------------------------------------------------
//
// Webview pane (single global) used for two things:
//   1. The explicit print command (Cmd/Ctrl+Alt+P, right-click "Print
//      symbol under cursor"): user invokes `print <qname>.`, output
//      lands here.
//   2. The search-display picker preview (Cmd/Ctrl+Alt+S): highlighting
//      a search hit dispatches `print <qname>.` and renders the body
//      here so the user can read the lemma signature without leaving
//      the picker.
//
// Replace-on-render is the default — the panel always shows the most
// recent output. enableFindWidget gives Cmd/Ctrl+F. The "Open in
// editor" button posts a message back to the extension which spawns a
// scratch document with the same content (for users who want native
// editor controls — search, copy, save).

interface PrintEntry {
  title: string;
  source: string;   // the EC directive that was dispatched (e.g. "print foo.")
  body: string;     // captured output
}
let printPanel: vscode.WebviewPanel | undefined;
let lastPrintEntry: PrintEntry | undefined;

function ensurePrintPanel(): vscode.WebviewPanel {
  if (printPanel) {
    printPanel.reveal(vscode.ViewColumn.Beside, /* preserveFocus */ true);
    return printPanel;
  }
  const panel = vscode.window.createWebviewPanel(
    'easycrypt.print',
    'EasyCrypt Print',
    { viewColumn: vscode.ViewColumn.Beside, preserveFocus: true },
    {
      retainContextWhenHidden: true,
      enableScripts: true,        // needed for the "Open in editor" button
      enableFindWidget: true,     // Cmd/Ctrl+F inside the webview
    },
  );
  panel.onDidDispose(() => {
    printPanel = undefined;
  });
  panel.webview.onDidReceiveMessage(async (msg) => {
    if (msg && msg.cmd === 'openInEditor' && lastPrintEntry) {
      const doc = await vscode.workspace.openTextDocument({
        content: lastPrintEntry.body,
        language: 'easycrypt',
      });
      await vscode.window.showTextDocument(doc, vscode.ViewColumn.Beside);
    }
  });
  printPanel = panel;
  return panel;
}

async function renderPrintHtml(entry: PrintEntry): Promise<string> {
  const styles = `
    body {
      font-family: var(--vscode-editor-font-family, monospace);
      font-size: var(--vscode-editor-font-size, 13px);
      color: var(--vscode-editor-foreground);
      background: var(--vscode-editor-background);
      padding: 0.5em 1em;
    }
    .header {
      display: flex;
      align-items: center;
      gap: 0.75em;
      margin-bottom: 0.5em;
      color: var(--vscode-descriptionForeground);
      font-size: 0.9em;
    }
    .source {
      color: var(--vscode-textLink-foreground);
      font-weight: bold;
    }
    .body {
      white-space: pre-wrap;
      border-top: 1px dashed var(--vscode-panel-border);
      padding-top: 0.5em;
    }
    .empty {
      font-style: italic;
      color: var(--vscode-descriptionForeground);
    }
    button.open-in-editor {
      background: var(--vscode-button-background);
      color: var(--vscode-button-foreground);
      border: none;
      padding: 0.2em 0.6em;
      cursor: pointer;
      font-size: 0.85em;
      border-radius: 3px;
    }
    button.open-in-editor:hover {
      background: var(--vscode-button-hoverBackground);
    }
    /* TM tokenizer classes — mirror goal-pane styles so the print
       panel renders EC source consistently. Theme-aware via
       body.vscode-{light,dark,high-contrast}. */
    body.vscode-dark {
      --ts-kw-control: #c586c0;
      --ts-kw: #569cd6;
      --ts-kw-op: #d4d4d4;
      --ts-storage: #4fc1ff;
      --ts-type: #4ec9b0;
      --ts-fn: #dcdcaa;
      --ts-name: #9cdcfe;
      --ts-num: #b5cea8;
      --ts-string: #ce9178;
      --ts-comment: #6a9955;
    }
    body.vscode-light {
      --ts-kw-control: #af00db;
      --ts-kw: #0000ff;
      --ts-kw-op: #000000;
      --ts-storage: #0070c1;
      --ts-type: #267f99;
      --ts-fn: #795e26;
      --ts-name: #001080;
      --ts-num: #098658;
      --ts-string: #a31515;
      --ts-comment: #008000;
    }
    body.vscode-high-contrast {
      --ts-kw-control: #d33682;
      --ts-kw: #569cd6;
      --ts-kw-op: #ffffff;
      --ts-storage: #4fc1ff;
      --ts-type: #4ec9b0;
      --ts-fn: #dcdcaa;
      --ts-name: #9cdcfe;
      --ts-num: #b5cea8;
      --ts-string: #ce9178;
      --ts-comment: #7ca668;
    }
    .ts-kw-control { color: var(--ts-kw-control); font-weight: bold; }
    .ts-kw-operator { color: var(--ts-kw-op); }
    .ts-kw { color: var(--ts-kw); font-weight: bold; }
    .ts-type { color: var(--ts-type); }
    .ts-type-name { color: var(--ts-type); }
    .ts-storage { color: var(--ts-storage); font-weight: bold; }
    .ts-fn-name { color: var(--ts-fn); }
    .ts-name { color: var(--ts-name); }
    .ts-var { color: var(--ts-name); }
    .ts-num { color: var(--ts-num); }
    .ts-const { color: var(--ts-num); }
    .ts-string { color: var(--ts-string); }
    .ts-comment { color: var(--ts-comment); font-style: italic; }
    .ts-punct { color: var(--vscode-foreground, inherit); }
  `;
  // Always-on TM highlighting in print panel — print output is
  // typically EC source (module / proc / abbrev / lemma bodies) so
  // tokenizer + prettify give the right look. Falls back to plain
  // escaped text if the tokenizer fails.
  let highlightedBody: string;
  try {
    highlightedBody = await tokenizer.highlightSource(extensionPath, entry.body);
  } catch (_) {
    highlightedBody = escapeHtml(entry.body);
  }
  const bodyHtml = entry.body.length === 0
    ? '<div class="empty">(no output)</div>'
    : `<div class="body">${highlightedBody}</div>`;
  return `<!DOCTYPE html><html><head><style>${styles}</style></head>
<body>
  <div class="header">
    <span class="source">${escapeHtml(entry.source)}</span>
    <button class="open-in-editor" onclick="vscode.postMessage({cmd:'openInEditor'})">📋 Open in editor</button>
  </div>
  ${bodyHtml}
  <script>const vscode = acquireVsCodeApi();</script>
</body></html>`;
}

function setPrintOutput(entry: PrintEntry): void {
  lastPrintEntry = entry;
  const panel = ensurePrintPanel();
  panel.title = entry.title;
  void (async () => {
    const html = await renderPrintHtml(entry);
    // Re-check panel + entry are still current; setPrintOutput may
    // have been called again with a newer entry while we awaited.
    if (printPanel === panel && lastPrintEntry === entry) {
      panel.webview.html = html;
    }
  })();
}

interface PrintResponse {
  output: string;
  error: string | null;
}

// Dispatch `print <something>.` (caller passes the full directive
// source, with trailing dot) and render the result to the print
// panel. Surfaces errs into the panel body too — the user always
// sees why a print failed.
async function dispatchPrint(uri: string, source: string, title: string): Promise<void> {
  const result = await withClient(c =>
    c.sendRequest<PrintResponse>('easycrypt/proof/print', { uri, source }),
  );
  if (!result) {
    setPrintOutput({ title, source, body: '(daemon unavailable)' });
    return;
  }
  const body = result.error
    ? (result.output ? result.output + '\n\nerror: ' + result.error : 'error: ' + result.error)
    : result.output;
  setPrintOutput({ title, source, body });
}

async function handlePrint(): Promise<void> {
  const editor = activeEcEditor();
  if (!editor) return;
  const uri = editor.document.uri.toString();
  const target = await vscode.window.showInputBox({
    title: 'EasyCrypt: print',
    placeHolder: 'qname or term to print (e.g., AllCore.true_neq_false, true)',
    prompt: 'Sent to EC as `print <input>.` — Esc cancels.',
  });
  if (!target) return;
  const source = `print ${target.trim()}.`;
  await dispatchPrint(uri, source, `print: ${target.trim()}`);
}

// Text-based identifier extraction at the cursor position. Sufficient
// for the common case (qname under cursor); the semantic version
// (UPSTREAM § 2 decl dump → resolve identifier to its qualified path)
// lands once the workspace symbol index ships.
function identifierUnderCursor(editor: vscode.TextEditor): string | undefined {
  const sel = editor.selection;
  // If user has a selection, prefer it verbatim — lets them grab
  // multi-token expressions like `Real.( + )`.
  if (!sel.isEmpty) {
    return editor.document.getText(sel).trim() || undefined;
  }
  // EC identifiers: letters/digits/_/' for name segments, joined by
  // `.` for qualified names. Regex must end with a name segment, NOT
  // a dot — sentence terminators ("apply lemma." → "lemma" not
  // "lemma.") would otherwise get dragged into the identifier and
  // produce `print lemma..` parse errors. Belt: also strip any
  // trailing dots that slip through from selection-based extraction.
  const wordRange = editor.document.getWordRangeAtPosition(
    sel.active,
    /[A-Za-z_][A-Za-z0-9_']*(\.[A-Za-z_][A-Za-z0-9_']*)*/,
  );
  if (!wordRange) return undefined;
  return editor.document.getText(wordRange).replace(/\.+$/, '');
}

async function handlePrintSymbolUnderCursor(): Promise<void> {
  const editor = activeEcEditor();
  if (!editor) return;
  const ident = identifierUnderCursor(editor);
  if (!ident) {
    vscode.window.showWarningMessage('EasyCrypt: no identifier under cursor.');
    return;
  }
  const uri = editor.document.uri.toString();
  const source = `print ${ident}.`;
  await dispatchPrint(uri, source, `print: ${ident}`);
}

// Search-display picker — same fuzzy search UX as apply, but on
// highlight dispatches `print <qname>.` (rendered to the print panel)
// instead of `apply <qname>.`. On accept, just closes — no insert.
async function handleSearchSymbols(): Promise<void> {
  const editor = activeEcEditor();
  if (!editor) return;
  await runLemmaPicker({
    uri: editor.document.uri.toString(),
    verb: 'apply',         // search uses any verb's qname; doesn't matter for display
    mode: 'display',
  });
}

// Mirror the [easycrypt-tooling.keybindings.preset] setting into a
// VSCode context key (`easycrypt.kbdPreset`) so package.json's PG-
// style keybinding entries can gate via `when:
// easycrypt.kbdPreset == 'pg'`. Called on activate + on config
// change. Falls back to 'default' on missing/invalid values.
async function applyKbdPresetContext(): Promise<void> {
  const cfg = vscode.workspace.getConfiguration('easycrypt-tooling.keybindings');
  const v = cfg.get<string>('preset', 'default');
  const preset = v === 'pg' ? 'pg' : 'default';
  await vscode.commands.executeCommand(
    'setContext', 'easycrypt.kbdPreset', preset,
  );
}

export async function activate(context: vscode.ExtensionContext): Promise<void> {
  // Stash extension path for the tokenizer (loads vscode-textmate
  // grammar + vscode-oniguruma WASM relative to it). Warmup kicks
  // off async so first-render doesn't block on WASM init.
  extensionPath = context.extensionPath;
  tokenizer.warmup(extensionPath);

  // Mirror the keybindings.preset setting → context key for the
  // `when` gates on PG-preset keybindings. Synchronous on first
  // activation; the onDidChangeConfiguration handler keeps it
  // current.
  void applyKbdPresetContext();

  // UPSTREAM § 14 / doc/session-model.md — easycrypt.project file
  // watcher. On change, prompt the user "easycrypt.project was
  // updated, reload the proof session?" with Reload / Keep options.
  // Reload sends easycrypt/proof/restart with a URI rooted at the
  // project (the daemon-side restart respawns the project's EC
  // subprocess, which picks up the new load paths). Keep adds the
  // file to a session-local "ignored" set so subsequent prompts
  // don't fire until the user reloads explicitly via the
  // EasyCrypt: Restart Language Server command.
  const projectWatcher =
    vscode.workspace.createFileSystemWatcher('**/easycrypt.project');
  context.subscriptions.push(projectWatcher);
  // URIs the user has chosen NOT to reload on this session — string
  // form so set semantics work cleanly.
  const ignoredProjectFiles = new Set<string>();
  const handleProjectChange = async (uri: vscode.Uri) => {
    const key = uri.toString();
    if (ignoredProjectFiles.has(key)) return;
    const choice = await vscode.window.showInformationMessage(
      `EasyCrypt: ${uri.fsPath} was updated. ` +
      `Reload the proof session for that project?`,
      { modal: false },
      'Reload', 'Keep current',
    );
    if (choice === 'Reload') {
      // Find an open .ec editor under the same directory tree as
      // the changed easycrypt.project and use its URI to drive the
      // restart — proof/restart's session-keying matches the
      // daemon's URI-to-project resolution. If no .ec file is open
      // for this project, defer the restart to the next open.
      const projectDir = path.dirname(uri.fsPath);
      const targetEditor = vscode.window.visibleTextEditors.find(e =>
        e.document.languageId === 'easycrypt'
        && e.document.uri.fsPath.startsWith(projectDir + path.sep)
      );
      if (!targetEditor) {
        vscode.window.showInformationMessage(
          `EasyCrypt: no .ec editor open under ${projectDir}; ` +
          `the next file you open will use the new load paths.`,
        );
        return;
      }
      await withClient(c =>
        c.sendRequest('easycrypt/proof/restart', {
          uri: targetEditor.document.uri.toString(),
        }),
      );
      vscode.window.showInformationMessage(
        `EasyCrypt: reloaded session for ${projectDir}.`,
      );
    } else if (choice === 'Keep current') {
      ignoredProjectFiles.add(key);
    }
    // No-choice (dismissed): re-prompt next time.
  };
  context.subscriptions.push(
    projectWatcher.onDidChange(handleProjectChange),
    projectWatcher.onDidCreate(handleProjectChange),
  );

  // Auto-open the EC repo when the Extension Host launches empty.
  // VSCodium quirks make launch.json folder-opening unreliable:
  // positional ${workspaceFolder} + --folder-uri + persistent
  // --user-data-dir all leave the Extension Host with no folder.
  // Cmd+O inside the Extension Host opens in the main window
  // instead. So we drive openFolder ourselves on activation.
  const isDev =
    context.extensionMode === vscode.ExtensionMode.Development;
  const noWorkspace =
    (vscode.workspace.workspaceFolders?.length ?? 0) === 0;
  if (isDev && noWorkspace) {
    const ecRoot = vscode.Uri.file(path.dirname(context.extensionPath));
    // updateWorkspaceFolders adds the folder to the current window's
    // workspace WITHOUT going through the OS-window code path that
    // openFolder uses (which under VSCodium ends up opening in the
    // main window instead of the Extension Host).
    const accepted = vscode.workspace.updateWorkspaceFolders(0, 0, {
      uri: ecRoot,
      name: 'easycrypt-tooling',
    });
    if (accepted) {
      vscode.window.showInformationMessage(
        `EasyCrypt (dev): added ${ecRoot.fsPath} to workspace`,
      );
    } else {
      vscode.window.showWarningMessage(
        `EasyCrypt (dev): updateWorkspaceFolders rejected ` +
          `(folders=${vscode.workspace.workspaceFolders?.length ?? 0}). ` +
          `Open ${ecRoot.fsPath} manually via "Add Folder to Workspace".`,
      );
    }
    // No reload — workspace folder is added in-place. Continue with
    // normal activation (commands + LSP startup).
  }
  if (noWorkspace) {
    vscode.window.showInformationMessage(
      `EasyCrypt: no workspace open ` +
        `(extensionMode=${context.extensionMode}). ` +
        `Open a folder containing .ec files via File → Open Folder.`,
    );
  }

  context.subscriptions.push(
    vscode.commands.registerCommand('easycrypt.proof.step', handleStep),
    vscode.commands.registerCommand('easycrypt.proof.back', handleBack),
    // execToCursor is now bidirectional — forward = exec, backward =
    // revert. Keep the legacy command name + keybind so existing
    // muscle memory is preserved.
    vscode.commands.registerCommand('easycrypt.proof.execToCursor', handleGotoCursor),
    vscode.commands.registerCommand('easycrypt.proof.revertToCursor', handleRevertToCursor),
    vscode.commands.registerCommand('easycrypt.proof.goals', handleShowGoals),
    vscode.commands.registerCommand('easycrypt.proof.cycleSubgoalNext', handleCycleSubgoalNext),
    vscode.commands.registerCommand('easycrypt.proof.cycleSubgoalPrev', handleCycleSubgoalPrev),
    vscode.commands.registerCommand('easycrypt.proof.restart', handleProofRestart),
    vscode.commands.registerCommand('easycrypt.proof.execAll', handleExecAll),
    vscode.commands.registerCommand('easycrypt.proof.focusCurrentGoal', handleFocusCurrentGoal),
    vscode.commands.registerCommand('easycrypt.proof.tryTactic', handleTryTactic),
    vscode.commands.registerCommand('easycrypt.proof.suggestClosers', handleSuggestClosers),
    vscode.commands.registerCommand('easycrypt.proof.cancel', handleCancel),
    vscode.commands.registerCommand('easycrypt.proof.previewLog.show', handleShowPreviewLog),
    vscode.commands.registerCommand('easycrypt.proof.moveBuilder', handleMoveBuilder),
    vscode.commands.registerCommand('easycrypt.proof.rewriteBuilder', handleRewriteBuilder),
    vscode.commands.registerCommand('easycrypt.proof.applyBuilder', handleApplyBuilder),
    vscode.commands.registerCommand('easycrypt.proof.tacticLauncher', handleTacticBuilderLauncher),
    vscode.commands.registerCommand('easycrypt.proof.applyLemma', handleApplyLemma),
    // Cycle controls for the comparison preview's "new subgoals"
    // pane. Bound to keybinds gated on easycrypt.lemmaPickerOpen so
    // they fire while the picker has focus (clicking the in-webview
    // buttons would steal focus + dismiss the picker).
    vscode.commands.registerCommand(
      'easycrypt.proof.compareCycleNext',
      () => { compareCycleActive(+1); },
    ),
    vscode.commands.registerCommand(
      'easycrypt.proof.compareCyclePrev',
      () => { compareCycleActive(-1); },
    ),
    // Lemma-picker refine-args: hands off to phase-3 builder for
    // the active hit. Bound to Shift+Enter when picker is open.
    vscode.commands.registerCommand(
      'easycrypt.proof.lemmaPickerRefineArgs',
      () => { activeLemmaPickerRefineHandler?.(); },
    ),
    vscode.commands.registerCommand('easycrypt.display.togglePrettify', handleTogglePrettify),
    vscode.commands.registerCommand('easycrypt.display.toggleProgramWrap', handleToggleProgramWrap),
    vscode.commands.registerCommand('easycrypt.proof.print', handlePrint),
    vscode.commands.registerCommand('easycrypt.proof.printSymbolUnderCursor', handlePrintSymbolUnderCursor),
    vscode.commands.registerCommand('easycrypt.proof.searchSymbols', handleSearchSymbols),
    vscode.commands.registerCommand('easycrypt.lsp.restart', handleLspRestart),
    vscode.commands.registerCommand('easycrypt.dev.rebuildAndReload', handleRebuildAndReload),
    vscode.window.onDidChangeVisibleTextEditors(() => refreshAllVisible()),
    vscode.window.onDidChangeActiveTextEditor((editor) => {
      if (!editor) return;
      const uri = editor.document.uri.toString();
      refreshDecorations(uri);
      // Goal pane follows the active editor — when the user switches
      // .ec files, refresh to show the new file's goals (if the pane
      // is open). Skip non-EC editors so switching to a search result
      // / output panel doesn't blow away the goals view.
      if (
        goalsPanel
        && editor.document.languageId === 'easycrypt'
        && goalsForUri !== uri
      ) {
        void fetchAndRenderGoals(uri);
      }
    }),
    // Theme change → re-render webviews so token colors update.
    // Token text + structure are unchanged, but the pre-emitted HTML
    // includes `var(--vscode-...)` references — these update via CSS
    // automatically. The re-render only matters for the prettify
    // setting which depends on tokenizer output. Cheap to do anyway.
    vscode.window.onDidChangeActiveColorTheme(() => {
      if (goalsPanel && goalsForUri) {
        void fetchAndRenderGoals(goalsForUri);
      }
      if (printPanel && lastPrintEntry) {
        // Re-emit current print output via setPrintOutput's pipeline.
        const e = lastPrintEntry;
        void (async () => {
          if (printPanel) printPanel.webview.html = await renderPrintHtml(e);
        })();
      }
    }),
    // Display settings (prettify / replacements / programWrap)
    // toggle → re-render. Same pipeline.
    vscode.workspace.onDidChangeConfiguration((e) => {
      if (!e.affectsConfiguration('easycrypt-tooling.display.prettify')
          && !e.affectsConfiguration('easycrypt-tooling.display.prettify.replacements')
          && !e.affectsConfiguration('easycrypt-tooling.display.programWrap')
          && !e.affectsConfiguration('easycrypt-tooling.display.equivAlignment')) {
        return;
      }
      if (goalsPanel && goalsForUri) {
        void fetchAndRenderGoals(goalsForUri);
      }
      if (printPanel && lastPrintEntry) {
        const entry = lastPrintEntry;
        void (async () => {
          if (printPanel) printPanel.webview.html = await renderPrintHtml(entry);
        })();
      }
    }),
    // Keybinding preset (default | pg) — mirror the setting into a
    // VSCode context key so `package.json`'s `when` clauses can gate
    // the PG-style chord aliases. See `easycrypt-tooling.keybindings.preset`
    // and the parallel keybindings entries gated on
    // `easycrypt.kbdPreset == 'pg'`.
    vscode.workspace.onDidChangeConfiguration((e) => {
      if (!e.affectsConfiguration('easycrypt-tooling.keybindings.preset')) return;
      void applyKbdPresetContext();
    }),
  );
  await startClient();
}

export async function deactivate(): Promise<void> {
  await stopClient();
  if (processedDecoration) {
    processedDecoration.dispose();
    processedDecoration = undefined;
  }
  if (queuedDecoration) {
    queuedDecoration.dispose();
    queuedDecoration = undefined;
  }
  if (goalsPanel) {
    goalsPanel.dispose();
    goalsPanel = undefined;
  }
  if (printPanel) {
    printPanel.dispose();
    printPanel = undefined;
  }
}
