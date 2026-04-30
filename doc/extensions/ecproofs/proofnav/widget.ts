import {
  EditorState,
  StateEffect,
  StateField,
  Range,
  RangeSet,
} from "@codemirror/state";

import {
  EditorView,
  Decoration,
  keymap,
  gutter,
  GutterMarker,
  lineNumbers,
} from "@codemirror/view";

import { defaultKeymap } from "@codemirror/commands";
import { syntaxHighlighting, HighlightStyle } from "@codemirror/language";
import { tags as t } from "@lezer/highlight"

import { easycryptHighlight } from "./easycrypt";

export type ProofSentence = {
  goals?: string[];
  message?: string | null;
};

export type CreateProofNavigatorOptions = {
  parent: HTMLElement;
  source: string;
  sentenceEnds: number[];
  sentences: ProofSentence[];
  initialSentence?: number;      // allow -1 (before first)
  collapsible?: boolean;         // default true
  initialCollapsed?: boolean;    // default true
  title?: string;                // default "Proof Navigator"
};

export type ProofNavigatorHandle = {
  view: EditorView;
  setSentence: (idx: number, opts?: { scroll?: boolean }) => void;
  getSentence: () => number;
  collapse: () => void;
  expand: () => void;
  toggleCollapsed: () => void;
  isCollapsed: () => boolean;
};

const rtdHighlight: HighlightStyle = HighlightStyle.define([
  { tag: t.keyword, color: "#005a9c", fontWeight: "600" },
  { tag: t.annotation, color: "#a10d2b", fontWeight: "600" },
  { tag: t.invalid, color: "#ff0000", fontWeight: "600" },
  { tag: t.namespace, color: "#b61295", fontWeight: "600" },
  { tag: t.keyword, color: "#005a9c", fontWeight: "600" },
  { tag: t.controlKeyword, color: "#005a9c", fontWeight: "600" },
  { tag: t.controlOperator, color: "#108401", fontWeight: "600" },
  { tag: [t.string, t.special(t.string)], color: "#1a7f37" },
  { tag: t.comment, color: "#6a737d", fontStyle: "italic" },
  { tag: t.number, color: "#b31d28" },
  { tag: t.variableName, color: "#24292f" },
  { tag: [t.operator, t.punctuation], color: "#57606a" },
]);

export function createProofNavigator(opts: CreateProofNavigatorOptions): ProofNavigatorHandle {
  const {
    parent,
    source,
    sentenceEnds,
    sentences,
    initialSentence = -1,
    collapsible = true,
    initialCollapsed = true,
    title = "Proof Navigator",
  } = opts;

  if (!parent) throw new Error("parent is required");
  if (!Array.isArray(sentenceEnds) || sentenceEnds.length === 0) {
    throw new Error("sentenceEnds must be non-empty");
  }
  if (!Array.isArray(sentences) || sentences.length !== sentenceEnds.length) {
    throw new Error("sentences length mismatch");
  }

  function skipWhitespaceForward(pos: number): number {
    while (pos < source.length && /\s/.test(source[pos])) pos++;
    return pos;
  }

  const sentenceStarts = sentenceEnds.map((_, i) =>
    i === 0
      ? skipWhitespaceForward(0)
      : skipWhitespaceForward(sentenceEnds[i - 1])
  );

  const clamp = (x: number, lo: number, hi: number) => Math.max(lo, Math.min(hi, x));

  function sentenceIndexAtPos(pos: number): number {
    let lo = 0;
    let hi = sentenceEnds.length - 1;
    while (lo < hi) {
      const mid = (lo + hi) >> 1;
      if (sentenceEnds[mid] >= pos) hi = mid;
      else lo = mid + 1;
    }
    return lo;
  }

  const root = document.createElement("div");
  root.className = "proofnav proofnav-rtd";
  root.innerHTML = `
    <div class="panel">
      <div class="proofnav__header">
        <div class="proofnav__title">
          ${collapsible ? `
            <button class="proofnav__btn proofnav__btnToggle" data-toggle aria-expanded="true" title="Collapse" type="button">
              <span class="proofnav__chev" aria-hidden="true">▾</span>
              <span class="proofnav__sr" data-toggle-label>Collapse</span>
            </button>
          ` : ""}
          <span data-title></span>
        </div>
      </div>

      <div class="proofnav__body" data-body>
        <div class="proofnav__sentencebar">
          <div class="proofnav__subtitle" data-sentinfo></div>
          <div class="proofnav__controls">
            <button class="proofnav__btn" data-prev>&larr; Prev</button>
            <button class="proofnav__btn" data-next>Next &rarr;</button>
          </div>
        </div>

        <div class="proofnav__editor" data-editor></div>

        <div class="panel">
          <div class="infoBody">
            <div class="box">
              <div class="tabs" data-tabs></div>
              <div class="goal-sep"></div>
              <div data-goalcontent></div>
            </div>
            <div class="box">
              <div data-message></div>
            </div>
          </div>
        </div>
      </div>
    </div>
  `;
  parent.appendChild(root);

  const elTitle = root.querySelector("[data-title]") as HTMLElement;
  elTitle.textContent = title;

  const elEditor = root.querySelector("[data-editor]") as HTMLElement;
  const elTabs = root.querySelector("[data-tabs]") as HTMLElement;
  const elGoalContent = root.querySelector("[data-goalcontent]") as HTMLElement;
  const elMessage = root.querySelector("[data-message]") as HTMLElement;
  const elSentInfo = root.querySelector("[data-sentinfo]") as HTMLElement;
  const elGoalSep = root.querySelector(".goal-sep") as HTMLElement;
  const btnPrev = root.querySelector("[data-prev]") as HTMLButtonElement;
  const btnNext = root.querySelector("[data-next]") as HTMLButtonElement;

  const btnToggle = root.querySelector("[data-toggle]") as HTMLButtonElement | null;
  const elToggleLabel = root.querySelector("[data-toggle-label]") as HTMLElement | null;

  const setSentenceEffect = StateEffect.define<number>();
  const setHoverEffect = StateEffect.define<number | null>(); // number | null

  const sentenceField = StateField.define<number>({
    create() {
      return clamp(initialSentence, -1, sentenceEnds.length - 1);
    },
    update(v, tr) {
      for (const e of tr.effects) {
        if (e.is(setSentenceEffect)) return e.value;
      }
      return v;
    },
  });

  const hoverField = StateField.define<number | null>({
    create() {
      return null;
    },
    update(v, tr) {
      for (const e of tr.effects) {
        if (e.is(setHoverEffect)) return e.value;
      }
      return v;
    },
  });

  const sentenceHighlightField = StateField.define<ReturnType<typeof Decoration.set>>({
    create(state) {
      return buildDecorations(state.field(sentenceField), state.field(hoverField));
    },
    update(deco, tr) {
      const changed =
        tr.docChanged ||
        tr.effects.some((e) => e.is(setSentenceEffect) || e.is(setHoverEffect));
      if (changed) {
        return buildDecorations(tr.state.field(sentenceField), tr.state.field(hoverField));
      }
      return deco.map(tr.changes);
    },
    provide: (f) => EditorView.decorations.from(f),
  });

  function buildDecorations(activeIdx: number, hoverIdx: number | null) {
    const d: Range<Decoration>[] = [];

    if (hoverIdx != null && hoverIdx >= 0 && hoverIdx < sentenceEnds.length) {
      const hs = sentenceStarts[hoverIdx];
      const he = sentenceEnds[hoverIdx];
      if (he > hs) d.push(Decoration.mark({ class: "cm-sentenceHover" }).range(hs, he));
    }

    if (activeIdx >= 0) {
      const start = sentenceStarts[activeIdx];
      const end = sentenceEnds[activeIdx];

      if (start > 0) d.push(Decoration.mark({ class: "cm-sentenceDone" }).range(0, start));
      if (end > start) d.push(Decoration.mark({ class: "cm-sentenceCurrent" }).range(start, end));
    }

    return Decoration.set(d, true);
  }

  const hoverAndClick = EditorView.domEventHandlers({
    mousemove(e, view) {
      const pos = view.posAtCoords({ x: e.clientX, y: e.clientY });
      if (pos == null) {
        root.classList.remove("pn-hovering");
        if (view.state.field(hoverField) != null) {
          view.dispatch({ effects: setHoverEffect.of(null) });
        }
        return false;
      }

      const idx = sentenceIndexAtPos(pos);
      root.classList.add("pn-hovering");
      if (view.state.field(hoverField) !== idx) {
        view.dispatch({ effects: setHoverEffect.of(idx) });
      }
      return false;
    },

    mouseleave(_e, view) {
      root.classList.remove("pn-hovering");
      if (view.state.field(hoverField) != null) {
        view.dispatch({ effects: setHoverEffect.of(null) });
      }
      return false;
    },

    mousedown(e, view) {
      if (e.button !== 0) return false;
      const pos = view.posAtCoords({ x: e.clientX, y: e.clientY });
      if (pos == null) return false;
      setSentence(sentenceIndexAtPos(pos), { scroll: false });
      return true;
    },
  });

  class ActiveSentenceMarker extends GutterMarker {
    toDOM() {
      const span = document.createElement("span");
      span.className = "cm-activeSentenceMarker";
      span.textContent = "▶";
      return span;
    }
  }
  const activeMarker = new ActiveSentenceMarker();

  const activeSentenceGutter = gutter({
    class: "cm-activeSentenceGutter",
    markers: (view) => {
      const idx = view.state.field(sentenceField);
      if (idx < 0) return RangeSet.empty;
      const line = view.state.doc.lineAt(sentenceStarts[idx]).from;
      return RangeSet.of([activeMarker.range(line)]);
    },
    initialSpacer: () => activeMarker,
  });

  const rtdTheme = EditorView.theme({
    "&": {
      backgroundColor: "#fff",
      color: "#404040",
      fontSize: "11px",
    },
    ".cm-content": {
      fontFamily: "var(--pn-mono)",
      fontSize: "11px",
    },
    ".cm-gutters": {
      backgroundColor: "#fbfbfb",
      borderRight: "1px solid #e1e4e5",
      fontSize: "11px",
    },
    ".cm-lineNumbers .cm-gutterElement": {
      padding: "0 8px 0 10px",
      fontSize: "11px",
    }
  });

  const view = new EditorView({
    parent: elEditor,
    state: EditorState.create({
      doc: source,
      extensions: [
        easycryptHighlight,
        syntaxHighlighting(rtdHighlight),
        activeSentenceGutter,
        lineNumbers(),
        keymap.of(defaultKeymap),
        EditorView.editable.of(false),
        EditorState.readOnly.of(true),
        sentenceField,
        hoverField,
        sentenceHighlightField,
        hoverAndClick,
        rtdTheme,
      ],
    }),
  });

  // autosize editor to content
  function autosizeEditor() {
    view.requestMeasure({
      read() {
        return view.contentDOM.scrollHeight;
      },
      write(height) {
        // Small padding to avoid clipping descenders
        elEditor.style.height = `${height + 6}px`;
      }
    });
  }

  requestAnimationFrame(() => requestAnimationFrame(autosizeEditor));

  let activeGoalTab = 0;

  function render(idx: number) {
    if (idx < 0) {
      elSentInfo.textContent = "Before first sentence";
      elTabs.innerHTML = "";
      elGoalContent.innerHTML = `<div class="empty">No goals.</div>`;
      elMessage.innerHTML = `<div class="empty">No message.</div>`;
      elGoalSep.style.display = "none";
      return;
    }

    elSentInfo.textContent = `Sentence ${idx + 1} / ${sentenceEnds.length}`;
    const info = sentences[idx] || {};
    const goals = Array.isArray(info.goals) ? info.goals : [];
    const msg = String(info.message ?? "");

    elTabs.innerHTML = "";
    elGoalContent.innerHTML = "";
    elGoalSep.style.display = goals.length ? "block" : "none";

    if (goals.length === 0) {
      elGoalContent.innerHTML = `<div class="empty">No goals.</div>`;
      activeGoalTab = 0;
    } else {
      activeGoalTab = clamp(activeGoalTab, 0, goals.length - 1);
      goals.forEach((_, i) => {
        const b = document.createElement("button");
        b.className = "tab";
        b.textContent = `Goal ${i + 1}`;
        b.setAttribute("aria-selected", i === activeGoalTab ? "true" : "false");
        b.onclick = () => {
          activeGoalTab = i;
          render(getSentence());
        };
        elTabs.appendChild(b);
      });
      const pre = document.createElement("pre");
      pre.textContent = goals[activeGoalTab] ?? "";
      elGoalContent.appendChild(pre);
    }

    if (msg.trim()) {
      const pre = document.createElement("pre");
      pre.textContent = msg;
      elMessage.innerHTML = "";
      elMessage.appendChild(pre);
    } else {
      elMessage.innerHTML = `<div class="empty">No message.</div>`;
    }
  }

  function scrollTo(idx: number) {
    if (idx < 0) return;
    view.dispatch({ selection: { anchor: sentenceStarts[idx] }, scrollIntoView: true });
  }

  function setSentence(idx: number, { scroll = true }: { scroll?: boolean } = {}) {
    const i = clamp(idx, -1, sentenceEnds.length - 1);

    const effects: StateEffect<unknown>[] = [setSentenceEffect.of(i)];

    if (i < 0) {
      effects.push(setHoverEffect.of(null));
      root.classList.remove("pn-hovering");
    }

    view.dispatch({ effects });
    render(i);
    if (scroll) scrollTo(i);
  }

  function getSentence(): number {
    return view.state.field(sentenceField);
  }

  btnPrev.onclick = () => setSentence(getSentence() - 1);
  btnNext.onclick = () => setSentence(getSentence() + 1);

  function isCollapsed(): boolean {
    return root.classList.contains("pn-collapsed");
  }

  function setCollapsed(collapsed: boolean) {
    if (!collapsible) return;
    if (collapsed) root.classList.add("pn-collapsed");
    else root.classList.remove("pn-collapsed");

    if (btnToggle) btnToggle.setAttribute("aria-expanded", collapsed ? "false" : "true");
    if (elToggleLabel) elToggleLabel.textContent = collapsed ? "Expand" : "Collapse";
    if (btnToggle) btnToggle.title = collapsed ? "Expand" : "Collapse";

    // When expanding, CodeMirror may need a layout refresh + correct height.
    if (!collapsed) {
      requestAnimationFrame(() => {
        autosizeEditor();
        view.requestMeasure();
      });
    }
  }

  function collapse() { setCollapsed(true); }
  function expand() { setCollapsed(false); }
  function toggleCollapsed() { setCollapsed(!isCollapsed()); }

  if (btnToggle) {
    btnToggle.onclick = () => toggleCollapsed();
  }

  setSentence(initialSentence);

  if (collapsible && initialCollapsed) {
    setCollapsed(true);
  }

  return { view, setSentence, getSentence, collapse, expand, toggleCollapsed, isCollapsed };
}
