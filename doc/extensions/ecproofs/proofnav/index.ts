import { createProofNavigator } from "./widget";

type ProofNavData = {
  source: string;
  sentenceEnds: number[];
  sentences: Array<{ goals?: string[]; message?: string | null }>;
  initialSentence?: number;
  title?: string;
};

function mountOne(mount: HTMLElement) {
  const id = mount.id;
  const dataEl = document.getElementById(id + "-data");
  if (!dataEl) return;

  let data: ProofNavData;
  try {
    data = JSON.parse(dataEl.textContent || "{}");
  } catch (e) {
    mount.innerHTML = `<div style="color:#b00;">proofnav: invalid JSON</div>`;
    return;
  }

  const initialSentence = typeof data.initialSentence === "number" ? data.initialSentence : -1;
  const title = typeof data.title === "string" ? data.title : undefined;

  createProofNavigator({
    parent: mount,
    source: data.source,
    sentenceEnds: data.sentenceEnds,
    sentences: data.sentences,
    initialSentence,
    title,
  });
}

function mountAll() {
  const mounts = document.querySelectorAll<HTMLElement>(".proofnav-sphinx .proofnav-mount");
  mounts.forEach(mountOne);
}

if (document.readyState === "loading") {
  document.addEventListener("DOMContentLoaded", mountAll);
} else {
  mountAll();
}
