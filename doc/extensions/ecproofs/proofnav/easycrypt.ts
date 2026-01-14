import { StreamLanguage } from "@codemirror/language"
import type { StreamParser } from "@codemirror/language"

type KeywordGroups = Record<string, readonly string[]>
type TagMap = Record<string, string>

const keywords: KeywordGroups = {
  bytac     : ['exact', 'assumption', 'smt', 'coq', 'check', 'edit', 'fix', 'by', 'reflexivity', 'done', 'solve'],
  dangerous : ['admit', 'admitted'],
  global    : ['axiom', 'axiomatized', 'lemma', 'realize', 'proof', 'qed', 'abort', 'goal', 'end', 'from', 'import', 'export', 'include', 'local', 'global', 'declare', 'hint', 'module', 'of', 'const', 'op', 'pred', 'inductive', 'notation', 'abbrev', 'require', 'theory', 'abstract', 'section', 'subtype', 'type', 'class', 'instance', 'print', 'search', 'locate', 'as', 'Pr', 'clone', 'with', 'rename', 'prover', 'timeout', 'why3', 'dump', 'remove', 'exit', 'Top', 'Self'],
  internal  : ['fail', 'time', 'undo', 'debug', 'pragma'],
  prog      : ['forall', 'exists', 'fun', 'glob', 'let', 'in', 'for', 'var', 'proc', 'if', 'is', 'match', 'then', 'else', 'elif', 'match', 'for', 'while', 'assert', 'return', 'res', 'equiv', 'hoare', 'ehoare', 'phoare', 'islossless', 'async'],
  tactic    : ['beta', 'iota', 'zeta', 'eta', 'logic', 'delta', 'simplify', 'cbv', 'congr', 'change', 'split', 'left', 'right', 'case', 'pose', 'gen', 'have', 'suff', 'elim', 'exlim', 'ecall', 'clear', 'wlog', 'idassign', 'apply', 'rewrite', 'rwnormal', 'subst', 'progress', 'trivial', 'auto', 'idtac', 'move', 'modpath', 'field', 'fieldeq', 'ring', 'ringeq', 'algebra', 'replace', 'transitivity', 'symmetry', 'seq', 'wp', 'sp', 'sim', 'skip', 'call', 'rcondt', 'rcondf', 'swap', 'cfold', 'rnd', 'rndsem', 'pr_bounded', 'bypr', 'byphoare', 'byehoare', 'byequiv', 'byupto', 'fel', 'conseq', 'exfalso', 'inline', 'outline', 'interleave', 'alias', 'weakmem', 'fission', 'fusion', 'unroll', 'splitwhile', 'kill', 'eager'],
  tactical  : ['try', 'first', 'last', 'do', 'expect'],
}

const tags: TagMap = {
  bytac     : "annotation",
  dangerous : "invalid",
  global    : "namespace",
  internal  : "invalid",
  prog      : "keyword",
  tactic    : "controlKeyword",
  tactical  : "controlOperator",
}

function buildKeywordTagMap(
  keywords: KeywordGroups,
  tags: TagMap
): Record<string, string> {
  const result: Record<string, string> = {}

  for (const [group, words] of Object.entries(keywords)) {
    const tag = tags[group]
    if (!tag) continue

    for (const word of words) {
      result[word] = tag
    }
  }

  return result
}

const keywordToTag = buildKeywordTagMap(keywords, tags)

const identRE  = /^[a-zA-Z_][A-Za-z0-9_']*/
const numberRE = /^\d+/
const punctRE  = /^[()\[\]{};,.:]/

type State = { commentDepth: number }

function eatNestedComment(stream: any, state: State): void {
  while (!stream.eol()) {
    if (stream.match("(*")) {
      state.commentDepth++
      continue
    }
    if (stream.match("*)")) {
      state.commentDepth--
      if (state.commentDepth <= 0) {
        state.commentDepth = 0
        break
      }
      continue
    }
    stream.next()
  }
}

const parser: StreamParser<State> = {
  name: "easycrypt",
  startState(): State {
    return {commentDepth: 0}
  },
  token(stream: any, state: State): string | null {
    // Nested comment continuation
    if (state.commentDepth > 0) {
      eatNestedComment(stream, state)
      return "comment"
    }

    if (stream.eatSpace()) return null

    // Nested comment start
    if (stream.match("(*")) {
      state.commentDepth = 1
      eatNestedComment(stream, state)
      return "comment"
    }

    // Numbers
    if (stream.match(numberRE)) {
      return "number"
    }

    // Identifiers / keywords
    if (stream.match(identRE)) {
      const word: string = stream.current()
      return keywordToTag[word] ?? "variableName"
    }

    // Punctuation
    if (stream.match(punctRE)) {
      return "punctuation"
    }

    // Always make progress
    stream.next()
    return null
  }
}

export const easycryptHighlight = StreamLanguage.define(parser)
