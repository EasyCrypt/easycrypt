import * as fs from 'fs';
import * as path from 'path';
import * as vscode from 'vscode';
import {
  LanguageClient,
  LanguageClientOptions,
  ServerOptions,
  TransportKind,
  Trace
} from 'vscode-languageclient/node';

type ProofResponse = {
  output: string;
  uuid: number;
  mode: string;
  processedEnd: number;
  sentenceStart?: number | null;
  sentenceEnd?: number | null;
};

type QueryResponse = {
  output: string;
};

type DocState = {
  lastOffset: number;
};

let client: LanguageClient | undefined;
let clientReady: Promise<void> | undefined;
let clientOptions: LanguageClientOptions | undefined;
let serverOptions: ServerOptions | undefined;
let goalsPanel: vscode.WebviewPanel | undefined;
let queryPanel: vscode.WebviewPanel | undefined;
let queryStatusBarItem: vscode.StatusBarItem | undefined;
let printStatusBarItem: vscode.StatusBarItem | undefined;
let locateStatusBarItem: vscode.StatusBarItem | undefined;
let outputChannel: vscode.OutputChannel | undefined;
let traceLevel: Trace = Trace.Off;
let lspCommand: string | undefined;
let lspArgs: string[] = [];
let processedDecoration: vscode.TextEditorDecorationType | undefined;
let processingDecoration: vscode.TextEditorDecorationType | undefined;
let errorDecoration: vscode.TextEditorDecorationType | undefined;
let lastEasyCryptEditor: vscode.TextEditor | undefined;
const docStates = new Map<string, DocState>();
let suppressProcessedEdits = false;
let suppressProcessingEdits = false;
let processingDocUri: string | undefined;
let processingSnapshot: string | undefined;
let diagnostics: vscode.DiagnosticCollection | undefined;

function getDocState(doc: vscode.TextDocument): DocState {
  const key = doc.uri.toString();
  const state = docStates.get(key);
  if (state) {
    return state;
  }
  const created = { lastOffset: 0 };
  docStates.set(key, created);
  return created;
}

function escapeHtml(value: string): string {
  return value
    .replace(/&/g, '&amp;')
    .replace(/</g, '&lt;')
    .replace(/>/g, '&gt;');
}

function showGoals(output: string): void {
  showTextPanel('easycryptGoals', 'EasyCrypt Goals', output, {
    panel: goalsPanel,
    setPanel: (panel) => {
      goalsPanel = panel;
    }
  });
}

function showQueryResult(title: string, output: string): void {
  showTextPanel('easycryptQuery', title, output, {
    panel: queryPanel,
    setPanel: (panel) => {
      queryPanel = panel;
    }
  });
}

function showTextPanel(
  viewType: string,
  title: string,
  output: string,
  holder: {
    panel: vscode.WebviewPanel | undefined;
    setPanel: (panel: vscode.WebviewPanel | undefined) => void;
  }
): void {
  let panel = holder.panel;
  if (!panel) {
    panel = vscode.window.createWebviewPanel(
      viewType,
      title,
      { viewColumn: vscode.ViewColumn.Beside, preserveFocus: true },
      { enableFindWidget: true }
    );
    panel.onDidDispose(() => {
      holder.setPanel(undefined);
    });
    holder.setPanel(panel);
  } else {
    panel.title = title;
    panel.reveal(panel.viewColumn, true);
  }

  panel.webview.html = `<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8" />
<meta name="viewport" content="width=device-width, initial-scale=1.0" />
<style>
  body { font-family: Menlo, Monaco, Consolas, "Courier New", monospace; padding: 12px; }
  pre { white-space: pre-wrap; }
</style>
</head>
<body>
<pre>${escapeHtml(output)}</pre>
</body>
</html>`;
}

async function restoreEditorFocus(editor: vscode.TextEditor | undefined): Promise<void> {
  if (!editor) {
    return;
  }
  await vscode.window.showTextDocument(editor.document, {
    viewColumn: editor.viewColumn,
    preserveFocus: false,
    selection: editor.selection
  });
}

function getQuerySeed(editor: vscode.TextEditor): string {
  const selection = editor.document.getText(editor.selection).trim();
  if (selection.length > 0) {
    return selection;
  }
  const wordRange = editor.document.getWordRangeAtPosition(editor.selection.active);
  if (!wordRange) {
    return '';
  }
  return editor.document.getText(wordRange).trim();
}

async function promptQuery(
  editor: vscode.TextEditor,
  kind: 'print' | 'locate' | 'search'
): Promise<string | undefined> {
  return vscode.window.showInputBox({
    title: `EasyCrypt ${kind}`,
    prompt: `Enter an EasyCrypt ${kind} query`,
    value: getQuerySeed(editor),
    ignoreFocusOut: true
  });
}

async function executeQuery(
  editor: vscode.TextEditor,
  method: 'easycrypt/query/print' | 'easycrypt/query/locate' | 'easycrypt/query/search',
  kind: 'print' | 'locate' | 'search',
  title: string,
  query: string
): Promise<void> {
  try {
    outputChannel?.appendLine(`[query] ${kind} ${query}`);
    const result = await requestProof<QueryResponse>(method, {
      uri: editor.document.uri.toString(),
      query
    });
    if (outputHasError(result.output)) {
      handleQueryError(title, result.output, editor);
      await restoreEditorFocus(editor);
      return;
    }
    showQueryResult(title, result.output.trim().length > 0 ? result.output : 'No output.');
    await restoreEditorFocus(editor);
  } catch (err) {
    outputChannel?.appendLine(`[query] ${kind} failed ${String(err)}`);
    vscode.window.showErrorMessage(`EasyCrypt ${kind} failed: ${String(err)}`);
  } finally {
    refreshQueryStatusBar(editor);
  }
}

async function runQuery(
  method: 'easycrypt/query/print' | 'easycrypt/query/locate' | 'easycrypt/query/search',
  kind: 'print' | 'locate' | 'search',
  title: string
): Promise<void> {
  const editor = getEditorForCommand();
  if (!editor) {
    vscode.window.showInformationMessage('EasyCrypt: no active EasyCrypt editor.');
    return;
  }

  const query = (await promptQuery(editor, kind))?.trim();
  if (!query) {
    return;
  }

  await executeQuery(editor, method, kind, title, query);
}

async function handlePrintQuery(): Promise<void> {
  await runQuery('easycrypt/query/print', 'print', 'EasyCrypt Print');
}

async function handleLocateQuery(): Promise<void> {
  await runQuery('easycrypt/query/locate', 'locate', 'EasyCrypt Locate');
}

async function handleSearchQuery(): Promise<void> {
  await runQuery('easycrypt/query/search', 'search', 'EasyCrypt Search');
}

async function handleLocateCurrentQuery(): Promise<void> {
  const editor = getEditorForCommand();
  if (!editor || editor.document.languageId !== 'easycrypt') {
    return;
  }
  const query = getQuerySeed(editor);
  if (!query) {
    return;
  }
  await executeQuery(
    editor,
    'easycrypt/query/locate',
    'locate',
    `EasyCrypt Locate: ${query}`,
    query
  );
}

async function handlePrintCurrentQuery(): Promise<void> {
  const editor = getEditorForCommand();
  if (!editor || editor.document.languageId !== 'easycrypt') {
    return;
  }
  const query = getQuerySeed(editor);
  if (!query) {
    return;
  }
  await executeQuery(
    editor,
    'easycrypt/query/print',
    'print',
    `EasyCrypt Print: ${query}`,
    query
  );
}

async function handleQueryStatusBar(): Promise<void> {
  const editor = getEditorForCommand();
  if (!editor || editor.document.languageId !== 'easycrypt') {
    return;
  }

  const selection = await vscode.window.showQuickPick(
    [
      {
        label: '$(symbol-key) Print Object',
        command: 'easycrypt.query.print'
      },
      {
        label: '$(symbol-file) Locate Object',
        command: 'easycrypt.query.locate'
      },
      {
        label: '$(search) Search Objects',
        command: 'easycrypt.query.search'
      }
    ],
    {
      title: 'EasyCrypt Query',
      placeHolder: 'Choose a query command'
    }
  );

  if (!selection) {
    return;
  }

  await vscode.commands.executeCommand(selection.command);
}

function updateQueryStatusBar(editor: vscode.TextEditor | undefined): void {
  if (!queryStatusBarItem) {
    return;
  }
  if (getStatusBarEditor(editor)) {
    queryStatusBarItem.show();
  } else {
    queryStatusBarItem.hide();
  }
}

function updateLocateStatusBar(editor: vscode.TextEditor | undefined): void {
  if (!locateStatusBarItem) {
    return;
  }
  const targetEditor = getStatusBarEditor(editor);
  if (!targetEditor) {
    locateStatusBarItem.hide();
    return;
  }

  const query = getQuerySeed(targetEditor);
  if (!query) {
    locateStatusBarItem.hide();
    return;
  }

  locateStatusBarItem.text = '$(symbol-file) Locate';
  locateStatusBarItem.tooltip = `EasyCrypt: locate ${query}`;
  locateStatusBarItem.show();
}

function updatePrintStatusBar(editor: vscode.TextEditor | undefined): void {
  if (!printStatusBarItem) {
    return;
  }
  const targetEditor = getStatusBarEditor(editor);
  if (!targetEditor) {
    printStatusBarItem.hide();
    return;
  }

  const query = getQuerySeed(targetEditor);
  if (!query) {
    printStatusBarItem.hide();
    return;
  }

  printStatusBarItem.text = '$(symbol-key) Print';
  printStatusBarItem.tooltip = `EasyCrypt: print ${query}`;
  printStatusBarItem.show();
}

function refreshQueryStatusBar(editor: vscode.TextEditor | undefined): void {
  updateQueryStatusBar(editor);
  updatePrintStatusBar(editor);
  updateLocateStatusBar(editor);
}

function updateProcessedDecoration(editor: vscode.TextEditor | undefined): void {
  if (!editor || !processedDecoration) {
    return;
  }
  const state = getDocState(editor.document);
  const endOffset = state.lastOffset;
  const endPos = editor.document.positionAt(endOffset);
  const startPos = new vscode.Position(0, 0);
  const anchor = new vscode.Range(startPos, startPos);
  const fixed = new vscode.Range(startPos, endPos);
  editor.setDecorations(processedDecoration, [anchor, fixed]);
}

function setProcessingDecoration(editor: vscode.TextEditor | undefined, range: vscode.Range): void {
  if (!editor || !processingDecoration) {
    return;
  }
  editor.setDecorations(processingDecoration, [range]);
}

function clearProcessingDecoration(editor: vscode.TextEditor | undefined): void {
  if (!editor || !processingDecoration) {
    return;
  }
  editor.setDecorations(processingDecoration, []);
}

function setProcessingLock(doc: vscode.TextDocument): void {
  processingDocUri = doc.uri.toString();
  processingSnapshot = doc.getText();
}

function clearProcessingLock(): void {
  processingDocUri = undefined;
  processingSnapshot = undefined;
}

async function restoreProcessingSnapshot(doc: vscode.TextDocument): Promise<void> {
  if (!processingSnapshot) {
    return;
  }
  const lastLine = doc.lineAt(doc.lineCount - 1);
  const fullRange = new vscode.Range(new vscode.Position(0, 0), lastLine.range.end);
  const edit = new vscode.WorkspaceEdit();
  edit.replace(doc.uri, fullRange, processingSnapshot);
  await vscode.workspace.applyEdit(edit);
}

function outputHasError(output: string): boolean {
  return /\[error-\d+-\d+\]/.test(output);
}

function summarizeErrorOutput(output: string): string {
  const line = output.split(/\r?\n/).find((entry) => entry.trim().length > 0);
  if (!line) {
    return 'EasyCrypt reported an error.';
  }
  const cleaned = line.replace(/\[error-\d+-\d+\]/g, '').trim();
  return cleaned.length > 0 ? cleaned : 'EasyCrypt reported an error.';
}

function showGoalsOrError(output: string): void {
  if (output.trim().length > 0) {
    showGoals(output);
  } else {
    showGoals('EasyCrypt reported an error.');
  }
}

function showQueryResultOrError(title: string, output: string): void {
  if (output.trim().length > 0) {
    showQueryResult(title, output);
  } else {
    showQueryResult(title, 'EasyCrypt reported an error.');
  }
}

function parseErrorTag(output: string): { start: number; end: number; message: string } | undefined {
  const match = output.match(/\[error-(\d+)-(\d+)\]/);
  if (!match) {
    return undefined;
  }
  const start = Number(match[1]);
  const end = Number(match[2]);
  if (!Number.isFinite(start) || !Number.isFinite(end)) {
    return undefined;
  }
  const message = output.replace(match[0], '').trim();
  return { start, end, message: message.length > 0 ? message : 'EasyCrypt reported an error.' };
}

function clearErrorDecoration(editor: vscode.TextEditor | undefined): void {
  if (!editor || !errorDecoration) {
    return;
  }
  editor.setDecorations(errorDecoration, []);
}

function clearDiagnostics(doc: vscode.TextDocument): void {
  diagnostics?.delete(doc.uri);
}

function showErrorDecoration(
  editor: vscode.TextEditor | undefined,
  sentenceOffset: number,
  errorStart: number,
  errorEnd: number
): void {
  if (!editor || !errorDecoration) {
    return;
  }
  const start = editor.document.positionAt(sentenceOffset + errorStart);
  const end = editor.document.positionAt(sentenceOffset + Math.max(errorStart + 1, errorEnd));
  editor.setDecorations(errorDecoration, [new vscode.Range(start, end)]);
}

function handleProofError(
  output: string,
  editor: vscode.TextEditor | undefined,
  sentenceOffset?: number
): void {
  const parsed = parseErrorTag(output);
  if (parsed && sentenceOffset !== undefined) {
    showErrorDecoration(editor, sentenceOffset, parsed.start, parsed.end);
    showGoals(parsed.message);
    if (editor && diagnostics) {
      const doc = editor.document;
      const start = doc.positionAt(sentenceOffset + parsed.start);
      const end = doc.positionAt(sentenceOffset + Math.max(parsed.start + 1, parsed.end));
      const range = new vscode.Range(start, end);
      const diag = new vscode.Diagnostic(range, parsed.message, vscode.DiagnosticSeverity.Error);
      diagnostics.set(doc.uri, [diag]);
    }
  } else {
    showGoalsOrError(output.replace(/\[error-\d+-\d+\]/g, '').trim());
  }
}

function handleQueryError(
  title: string,
  output: string,
  editor: vscode.TextEditor | undefined
): void {
  const parsed = parseErrorTag(output);
  clearErrorDecoration(editor);
  if (editor) {
    clearDiagnostics(editor.document);
  }
  if (parsed) {
    showQueryResult(title, parsed.message);
  } else {
    showQueryResultOrError(title, output.replace(/\[error-\d+-\d+\]/g, '').trim());
  }
}

function getEditorForCommand(): vscode.TextEditor | undefined {
  const active = vscode.window.activeTextEditor;
  if (active && active.document.languageId === 'easycrypt') {
    return active;
  }
  return lastEasyCryptEditor;
}

function getStatusBarEditor(editor: vscode.TextEditor | undefined): vscode.TextEditor | undefined {
  if (editor && editor.document.languageId === 'easycrypt') {
    return editor;
  }
  if (lastEasyCryptEditor?.document.languageId === 'easycrypt') {
    return lastEasyCryptEditor;
  }
  return undefined;
}

async function requestProof<T = ProofResponse>(
  method: string,
  params: Record<string, unknown>
): Promise<T> {
  if (!client) {
    throw new Error('EasyCrypt language client is not running.');
  }
  if (clientReady) {
    await clientReady;
  }
  const start = Date.now();
  outputChannel?.appendLine(`[proof] request ${method}`);
  const timeout = setTimeout(() => {
    outputChannel?.appendLine(`[proof] waiting ${method} >3s`);
  }, 3000);
  try {
    const result = await client.sendRequest<T>(method, params);
    const elapsed = Date.now() - start;
    outputChannel?.appendLine(`[proof] response ${method} ${elapsed}ms`);
    return result;
  } catch (err) {
    const elapsed = Date.now() - start;
    outputChannel?.appendLine(`[proof] error ${method} ${elapsed}ms ${String(err)}`);
    throw err;
  } finally {
    clearTimeout(timeout);
  }
}

async function handleStep(): Promise<void> {
  const editor = getEditorForCommand();
  if (!editor) {
    vscode.window.showInformationMessage('EasyCrypt: no active EasyCrypt editor.');
    return;
  }

  const doc = editor.document;
  const state = getDocState(doc);
  const previousOffset = state.lastOffset;
  let sentenceStart: number | null | undefined;
  let sentenceEnd: number | null | undefined;
  let previewProcessedEnd = state.lastOffset;
  try {
    const preview = await requestProof('easycrypt/proof/next', { uri: doc.uri.toString() });
    sentenceStart = preview.sentenceStart ?? null;
    sentenceEnd = preview.sentenceEnd ?? null;
    previewProcessedEnd = preview.processedEnd;
  } catch (err) {
    outputChannel?.appendLine(`[proof] step preview failed ${String(err)}`);
  }

  if (sentenceStart == null || sentenceEnd == null) {
    state.lastOffset = previewProcessedEnd;
    updateProcessedDecoration(editor);
    return;
  }

  if (sentenceStart != null && sentenceEnd != null) {
    const processingRange = new vscode.Range(
      doc.positionAt(sentenceStart),
      doc.positionAt(sentenceEnd)
    );
    setProcessingDecoration(editor, processingRange);
    setProcessingLock(doc);
  }

  try {
    const result = await requestProof('easycrypt/proof/step', { uri: doc.uri.toString() });
    outputChannel?.appendLine(`[proof] step ok uuid=${result.uuid} mode=${result.mode}`);
    state.lastOffset = result.processedEnd;
    if (outputHasError(result.output)) {
      outputChannel?.appendLine(`[proof] step reported error ${result.output}`);
      updateProcessedDecoration(editor);
      if (result.sentenceStart != null) {
        handleProofError(result.output, editor, result.sentenceStart);
      } else {
        handleProofError(result.output, editor, previousOffset);
      }
    } else {
      showGoals(result.output);
      updateProcessedDecoration(editor);
      clearErrorDecoration(editor);
      clearDiagnostics(editor.document);
    }
  } catch (err) {
    outputChannel?.appendLine(`[proof] step failed ${String(err)}`);
    vscode.window.showErrorMessage(`EasyCrypt step failed: ${String(err)}`);
  } finally {
    clearProcessingDecoration(editor);
    clearProcessingLock();
  }
}

async function handleSendRegion(): Promise<void> {
  const editor = getEditorForCommand();
  if (!editor) {
    vscode.window.showInformationMessage('EasyCrypt: no active EasyCrypt editor.');
    return;
  }

  const doc = editor.document;
  const state = getDocState(doc);
  const cursorOffset = doc.offsetAt(editor.selection.active);
  try {
    outputChannel?.appendLine('[proof] jumpToCursor');
    const result = await requestProof('easycrypt/proof/jumpTo', {
      uri: doc.uri.toString(),
      target: cursorOffset
    });
    outputChannel?.appendLine(`[proof] jumpToCursor ok uuid=${result.uuid} mode=${result.mode}`);
    state.lastOffset = result.processedEnd;
    if (outputHasError(result.output)) {
      outputChannel?.appendLine(`[proof] jumpToCursor reported error ${result.output}`);
      updateProcessedDecoration(editor);
      if (result.sentenceStart != null) {
        handleProofError(result.output, editor, result.sentenceStart);
      } else {
        handleProofError(result.output, editor, state.lastOffset);
      }
      return;
    }
    showGoals(result.output);
    updateProcessedDecoration(editor);
    clearErrorDecoration(editor);
    clearDiagnostics(doc);
  } catch (err) {
    outputChannel?.appendLine(`[proof] jumpToCursor failed ${String(err)}`);
    vscode.window.showErrorMessage(`EasyCrypt jump-to-cursor failed: ${String(err)}`);
  } finally {
    clearProcessingDecoration(editor);
    clearProcessingLock();
  }
}

async function handleBack(): Promise<void> {
  const editor = getEditorForCommand();
  if (!editor) {
    vscode.window.showInformationMessage('EasyCrypt: no active EasyCrypt editor.');
    return;
  }

  const state = getDocState(editor.document);
  try {
    outputChannel?.appendLine('[proof] back');
    const result = await requestProof('easycrypt/proof/back', {
      uri: editor.document.uri.toString()
    });
    if (outputHasError(result.output)) {
      outputChannel?.appendLine(`[proof] back reported error ${result.output}`);
      if (result.sentenceStart != null) {
        handleProofError(result.output, editor, result.sentenceStart);
      } else {
        handleProofError(result.output, editor);
      }
    } else {
      state.lastOffset = result.processedEnd;
      outputChannel?.appendLine(`[proof] back ok uuid=${result.uuid} mode=${result.mode}`);
      showGoals(result.output);
      updateProcessedDecoration(editor);
      clearErrorDecoration(editor);
      clearDiagnostics(editor.document);
    }
  } catch (err) {
    outputChannel?.appendLine(`[proof] back failed ${String(err)}`);
    vscode.window.showErrorMessage(`EasyCrypt back failed: ${String(err)}`);
  }
}

async function handleRestart(): Promise<void> {
  const editor = getEditorForCommand();
  if (!editor) {
    vscode.window.showInformationMessage('EasyCrypt: no active EasyCrypt editor.');
    return;
  }
  const state = editor ? getDocState(editor.document) : undefined;
  const previousOffset = state?.lastOffset ?? 0;

  try {
    outputChannel?.appendLine('[proof] restart');
    const result = await requestProof('easycrypt/proof/restart', {
      uri: editor.document.uri.toString()
    });
    outputChannel?.appendLine(`[proof] restart ok uuid=${result.uuid} mode=${result.mode}`);
    if (outputHasError(result.output)) {
      outputChannel?.appendLine(`[proof] restart reported error ${result.output}`);
      handleProofError(result.output, editor);
      if (state) {
        state.lastOffset = previousOffset;
      }
    } else {
      if (state) {
        state.lastOffset = result.processedEnd;
      }
      showGoals(result.output);
      updateProcessedDecoration(editor ?? vscode.window.activeTextEditor);
      clearErrorDecoration(editor ?? vscode.window.activeTextEditor);
      if (editor) {
        clearDiagnostics(editor.document);
      }
    }
  } catch (err) {
    outputChannel?.appendLine(`[proof] restart failed ${String(err)}`);
    vscode.window.showErrorMessage(`EasyCrypt restart failed: ${String(err)}`);
  }
}

async function handleGoals(): Promise<void> {
  try {
    outputChannel?.appendLine('[proof] goals');
    const editor = getEditorForCommand();
    if (!editor) {
      vscode.window.showInformationMessage('EasyCrypt: no active EasyCrypt editor.');
      return;
    }
    const result = await requestProof('easycrypt/proof/goals', {
      uri: editor.document.uri.toString()
    });
    outputChannel?.appendLine(`[proof] goals ok uuid=${result.uuid} mode=${result.mode}`);
    showGoals(result.output);
  } catch (err) {
    outputChannel?.appendLine(`[proof] goals failed ${String(err)}`);
    vscode.window.showErrorMessage(`EasyCrypt goals failed: ${String(err)}`);
  }
}

function resolveServerCommand(
  workspaceFolder: string | undefined,
  cliPath: string
): string | undefined {
  if (cliPath && cliPath.trim().length > 0) {
    return cliPath;
  }

  if (!workspaceFolder) {
    return undefined;
  }

  const exeCandidate = path.join(workspaceFolder, '_build', 'default', 'src', 'ec.exe');
  const unixCandidate = path.join(workspaceFolder, '_build', 'default', 'src', 'ec');
  if (fs.existsSync(exeCandidate)) {
    return exeCandidate;
  }
  if (fs.existsSync(unixCandidate)) {
    return unixCandidate;
  }

  return undefined;
}

function ensureLspArgs(args: string[]): string[] {
  if (args.length > 0 && args[0] === 'lsp') {
    return args;
  }
  return ['lsp', ...args];
}

function startClient(): void {
  if (!clientOptions || !serverOptions) {
    throw new Error('EasyCrypt LSP options are not configured.');
  }
  outputChannel?.appendLine(`[lsp] spawn command=${lspCommand ?? ''} args=${lspArgs.join(' ')}`);
  client = new LanguageClient('easycryptLsp', 'EasyCrypt LSP', serverOptions, clientOptions);
  outputChannel?.appendLine('[lsp] starting client');
  clientReady = client.start();
  void clientReady.then(
    () => outputChannel?.appendLine('[lsp] client ready'),
    (err) => outputChannel?.appendLine(`[lsp] client start failed ${String(err)}`)
  );
  void clientReady.then(() => client?.setTrace(traceLevel));
}

async function restartClient(): Promise<void> {
  if (!serverOptions || !clientOptions) {
    vscode.window.showErrorMessage('EasyCrypt: LSP options are not configured.');
    return;
  }
  const current = client;
  if (current) {
    try {
      await current.stop();
    } catch (err) {
      vscode.window.showWarningMessage(`EasyCrypt: failed to stop LSP (${String(err)}).`);
    }
  }
  startClient();
  outputChannel?.appendLine('[lsp] restarted client');
  vscode.window.showInformationMessage('EasyCrypt: LSP restarted.');
}

export function activate(context: vscode.ExtensionContext): void {
  outputChannel = vscode.window.createOutputChannel('EasyCrypt');
  context.subscriptions.push(outputChannel);
  queryStatusBarItem = vscode.window.createStatusBarItem(vscode.StatusBarAlignment.Left, 100);
  queryStatusBarItem.text = '$(symbol-namespace) EasyCrypt';
  queryStatusBarItem.tooltip = 'EasyCrypt query commands';
  queryStatusBarItem.command = 'easycrypt.query.statusBar';
  context.subscriptions.push(queryStatusBarItem);
  printStatusBarItem = vscode.window.createStatusBarItem(vscode.StatusBarAlignment.Left, 99);
  printStatusBarItem.command = 'easycrypt.query.printCurrent';
  context.subscriptions.push(printStatusBarItem);
  locateStatusBarItem = vscode.window.createStatusBarItem(vscode.StatusBarAlignment.Left, 99);
  locateStatusBarItem.command = 'easycrypt.query.locateCurrent';
  context.subscriptions.push(locateStatusBarItem);
  processedDecoration = vscode.window.createTextEditorDecorationType({
    backgroundColor: 'rgba(120, 140, 180, 0.18)',
    isWholeLine: false,
    rangeBehavior: vscode.DecorationRangeBehavior.ClosedClosed
  });
  context.subscriptions.push(processedDecoration);
  processingDecoration = vscode.window.createTextEditorDecorationType({
    backgroundColor: 'rgba(210, 170, 90, 0.28)',
    isWholeLine: false
  });
  context.subscriptions.push(processingDecoration);

  diagnostics = vscode.languages.createDiagnosticCollection('easycrypt');
  context.subscriptions.push(diagnostics);

  errorDecoration = undefined;

  const workspaceFolder = vscode.workspace.workspaceFolders?.[0]?.uri.fsPath;
  const config = vscode.workspace.getConfiguration('easycrypt');
  const cliPath = config.get<string>('cli.path') ?? '';
  const serverCommand = resolveServerCommand(workspaceFolder, cliPath) ?? 'easycrypt';
  const cliArgs = config.get<string[]>('cli.args') ?? [];
  const serverArgs = ensureLspArgs(cliArgs);
  lspCommand = serverCommand;
  lspArgs = serverArgs;
  const traceSetting = config.get<string>('trace.server') ?? 'off';
  traceLevel =
    traceSetting === 'verbose'
      ? Trace.Verbose
      : traceSetting === 'messages'
        ? Trace.Messages
        : Trace.Off;

  outputChannel.appendLine(`[lsp] serverCommand=${serverCommand}`);
  outputChannel.appendLine(`[lsp] cliPath=${cliPath || '(default)'}`);
  outputChannel.appendLine(`[lsp] cliArgs=${cliArgs.join(' ')}`);
  outputChannel.appendLine(`[lsp] serverArgs=${serverArgs.join(' ')}`);
  outputChannel.appendLine(`[lsp] trace=${traceSetting}`);
  outputChannel.appendLine(
    `[lsp] logFile=${workspaceFolder ? path.join(workspaceFolder, '.easycrypt-lsp.log') : '(inherit)'}`
  );
  outputChannel.show(true);

  if (!resolveServerCommand(workspaceFolder, cliPath)) {
    vscode.window.showWarningMessage(
      "EasyCrypt binary not found in the workspace. Using 'easycrypt' from PATH."
    );
  }

  const lspEnv = {
    ...process.env,
    EASYCRYPT_LSP_LOG: workspaceFolder
      ? path.join(workspaceFolder, '.easycrypt-lsp.log')
      : process.env.EASYCRYPT_LSP_LOG
  };
  const localServerOptions: ServerOptions = {
    command: serverCommand,
    args: serverArgs,
    transport: TransportKind.stdio,
    options: { env: lspEnv }
  };

  const localClientOptions: LanguageClientOptions = {
    documentSelector: [{ language: 'easycrypt' }],
    outputChannel,
    traceOutputChannel: outputChannel
  };

  serverOptions = localServerOptions;
  clientOptions = localClientOptions;
  startClient();
  context.subscriptions.push(
    new vscode.Disposable(() => {
      outputChannel?.appendLine('[lsp] stopping client');
      void client?.stop();
    })
  );
  if (client) {
    client.onDidChangeState((event) => {
      outputChannel?.appendLine(`[lsp] state ${event.oldState} -> ${event.newState}`);
    });
  }

  context.subscriptions.push(
    vscode.commands.registerCommand('easycrypt.proof.step', handleStep),
    vscode.commands.registerCommand('easycrypt.proof.back', handleBack),
    vscode.commands.registerCommand('easycrypt.proof.restart', handleRestart),
    vscode.commands.registerCommand('easycrypt.proof.jumpToCursor', handleSendRegion),
    vscode.commands.registerCommand('easycrypt.proof.goals', handleGoals),
    vscode.commands.registerCommand('easycrypt.query.print', handlePrintQuery),
    vscode.commands.registerCommand('easycrypt.query.locate', handleLocateQuery),
    vscode.commands.registerCommand('easycrypt.query.search', handleSearchQuery),
    vscode.commands.registerCommand('easycrypt.query.statusBar', handleQueryStatusBar),
    vscode.commands.registerCommand('easycrypt.query.printCurrent', handlePrintCurrentQuery),
    vscode.commands.registerCommand('easycrypt.query.locateCurrent', handleLocateCurrentQuery),
    vscode.commands.registerCommand('easycrypt.lsp.restart', restartClient)
  );

  context.subscriptions.push(
    vscode.workspace.onDidCloseTextDocument((doc) => {
      docStates.delete(doc.uri.toString());
    })
  );

  context.subscriptions.push(
    vscode.workspace.onDidChangeTextDocument(async (event) => {
      if (suppressProcessedEdits || suppressProcessingEdits) {
        return;
      }
      if (event.contentChanges.length === 0) {
        return;
      }
      const doc = event.document;
      if (doc.languageId !== 'easycrypt') {
        return;
      }
      if (processingDocUri && processingDocUri === doc.uri.toString()) {
        suppressProcessingEdits = true;
        try {
          await restoreProcessingSnapshot(doc);
        } catch (err) {
          outputChannel?.appendLine(`[proof] processing lock restore failed ${String(err)}`);
        } finally {
          suppressProcessingEdits = false;
        }
        return;
      }
      clearErrorDecoration(vscode.window.activeTextEditor);
      clearDiagnostics(doc);
      const state = getDocState(doc);
      const limit = state.lastOffset;
      const earliestStart = event.contentChanges.reduce((min, change) => {
        const start = change.range ? doc.offsetAt(change.range.start) : 0;
        return Math.min(min, start);
      }, Number.POSITIVE_INFINITY);
      if (!(earliestStart < limit)) {
        return;
      }
      suppressProcessedEdits = true;
      try {
        try {
          const result = await requestProof('easycrypt/proof/jumpTo', {
            uri: doc.uri.toString(),
            target: earliestStart
          });
          state.lastOffset = result.processedEnd;
        } catch (err) {
          outputChannel?.appendLine(`[proof] auto-rewind failed ${String(err)}`);
          vscode.window.showErrorMessage(`EasyCrypt auto-rewind failed: ${String(err)}`);
        }
        updateProcessedDecoration(vscode.window.activeTextEditor);
      } finally {
        suppressProcessedEdits = false;
      }
      return;
    })
  );

  const updateEditorState = (editor: vscode.TextEditor | undefined) => {
    if (editor && editor.document.languageId === 'easycrypt') {
      lastEasyCryptEditor = editor;
    }
    updateProcessedDecoration(editor);
    refreshQueryStatusBar(editor);
    clearErrorDecoration(editor);
    if (editor) {
      clearDiagnostics(editor.document);
    }
  };

  updateEditorState(vscode.window.activeTextEditor);

  context.subscriptions.push(
    vscode.window.onDidChangeTextEditorSelection((event) => {
      refreshQueryStatusBar(event.textEditor);
    })
  );

  context.subscriptions.push(
    vscode.window.onDidChangeActiveTextEditor((editor) => {
      updateEditorState(editor);
    })
  );

}

export async function deactivate(): Promise<void> {
  if (client) {
    await client.stop();
  }
}
