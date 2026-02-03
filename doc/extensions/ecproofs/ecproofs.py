# --------------------------------------------------------------
from __future__ import annotations
from typing import Any

import docutils as du

import sphinx.application as sa
import sphinx.errors      as se
import sphinx.util        as su

import bisect
import hashlib
import json
import os
import re
import shutil
import subprocess as subp
import tempfile


# ======================================================================
ROOT = os.path.dirname(__file__)

# ======================================================================
logger       = su.logging.getLogger('ecproofs')
store_logger = su.logging.getLogger('ecproofs.store')
cache_logger = su.logging.getLogger('ecproofs.cache')

# ======================================================================
def resolve_output_dir(path: str, outdir: str) -> str:
  if os.path.isabs(path):
    return path
  return os.path.join(outdir, path)

# ======================================================================
class ProofnavNode(du.nodes.General, du.nodes.Element):
  @staticmethod
  def visit_proofnav_node_html(self, node: ProofnavNode):
    pass

  @staticmethod
  def depart_proofnav_node_html(self, node: ProofnavNode):
    uid  = node["uid"]
    json = node["json"]

    html = f"""
<div class="proofnav-sphinx">
  <div id="{uid}" class="proofnav-mount"></div>
  <script type="application/json" id="{uid}-data">{json}</script>
</div>
"""

    self.body.append(html)

# ======================================================================
class EasyCryptError(se.SphinxError):
  category = "easycrypt"

# ======================================================================
class EasyCrypt:
  @staticmethod
  def run(cmd, *, location: Any | None = None):
    try:
      proc = subp.run(
        cmd, check = True, text = True, capture_output = True,
      )
      logger.debug("Command stdout:\n%s", proc.stdout)
      logger.debug("Command stderr:\n%s", proc.stderr)

      return True

    except subp.CalledProcessError as e:
      msg = f"{cmd[0]} exited with code {e.returncode}"

      if e.stdout:
        logger.debug("stdout:\n%s", e.stdout, location = location)
      if e.stderr:
        logger.debug("stderr:\n%s", e.stderr, location = location)

      logs = [x.split(maxsplit = 1) for x in e.stderr.splitlines()]
      logs = [x[1] for x in logs if len(x) == 2 and x[0] == 'E']

      for log in logs:
        logger.error(log, location = location, type = EasyCryptError.category)

      logger.error(msg, location = location, type = EasyCryptError.category)

      raise EasyCryptError(msg) from e

# ======================================================================
class EasyCryptCache:
  ENV_KEY = "ecproofs_cache"

  def __init__(self, cache_dir: str, outdir: str):
    self.cache_root = resolve_output_dir(cache_dir, outdir)

  @staticmethod
  def get_cache(app: sa.Sphinx) -> "EasyCryptCache | None":
    key = EasyCryptCache.ENV_KEY
    if not hasattr(app.env, key):
      setattr(app.env, key, EasyCryptCache.create_cache(app))
    return getattr(app.env, key)

  @staticmethod
  def create_cache(app: sa.Sphinx) -> "EasyCryptCache | None":
    cache_dir = app.config.ecproofs_cache_dir
    if cache_dir is None:
      return None
    return EasyCryptCache(cache_dir, app.outdir)

  def _relpath(self, path: str) -> str:
    try:
      return os.path.relpath(path, self.cache_root)
    except ValueError:
      return path

  def load(self, source: str, *, location: Any | None = None):
    cache_path = self.path_for_source(source)

    if not os.path.exists(cache_path):
      return None

    try:
      with open(cache_path) as ecostream:
        eco = json.load(ecostream)
      cache_logger.info(
        "Loaded EasyCrypt cache %s", self._relpath(cache_path),
        location = location
      )
      return eco

    except OSError as e:
      cache_logger.warning(
        "Failed to read EasyCrypt cache %s: %s", self._relpath(cache_path), e,
        location = location
      )
      return None

  def store(self, source: str, eco: Any, *, location: Any | None = None):
    cache_path = self.path_for_source(source)
    os.makedirs(os.path.dirname(cache_path), exist_ok = True)

    try:
      with open(cache_path, 'w') as outstream:
        json.dump(eco, outstream)
      cache_logger.info(
        "Stored EasyCrypt cache %s", self._relpath(cache_path),
        location = location
      )

    except OSError as e:
      cache_logger.warning(
        "Failed to write EasyCrypt cache %s: %s", self._relpath(cache_path), e,
        location = location
      )

  def path_for_source(self, source: str) -> str:
    digest = hashlib.sha256(source.encode("utf-8")).hexdigest()
    first  = digest[0:2]
    second = digest[2:4]

    return os.path.join(self.cache_root, first, second, f"{digest}.eco")

# ======================================================================
class EasyCryptScriptStore:
  ENV_KEY = "ecproofs_script_store"

  def __init__(self, scripts_dir: str, outdir: str):
    self.scripts_root = resolve_output_dir(scripts_dir, outdir)
    self._counters = {}

  @staticmethod
  def get_store(app: sa.Sphinx) -> "EasyCryptScriptStore | None":
    key = EasyCryptScriptStore.ENV_KEY
    if not hasattr(app.env, key):
      setattr(app.env, key, EasyCryptScriptStore.create_store(app))
    return getattr(app.env, key)

  @staticmethod
  def create_store(app: sa.Sphinx) -> "EasyCryptScriptStore | None":
    scripts_dir = app.config.ecproofs_scripts_dir
    if scripts_dir is None:
      return None
    return EasyCryptScriptStore(scripts_dir, app.outdir)

  @staticmethod
  def source_basename(source_path: str) -> str:
    return os.path.splitext(os.path.basename(source_path))[0] or "document"

  def _relpath(self, path: str) -> str:
    try:
      return os.path.relpath(path, self.scripts_root)
    except ValueError:
      return path

  def _next_script_index(self, source_path: str) -> int:
    index = self._counters.get(source_path, 0) + 1
    self._counters[source_path] = index
    return index

  def save(self, source: str, source_path: str, *, location: Any | None = None):
    base     = self.source_basename(source_path)
    index    = self._next_script_index(source_path)
    filename = f"{base}-{index:03d}.ec"
    outdir   = os.path.join(self.scripts_root, base)
    outpath  = os.path.join(outdir, filename)

    os.makedirs(outdir, exist_ok = True)

    try:
      with open(outpath, 'w') as outstream:
        outstream.write(source)
      store_logger.info(
        "Saved EasyCrypt script %s", self._relpath(outpath),
        location = location
      )
      return outpath

    except OSError as e:
      store_logger.warning(
        "Failed to write EasyCrypt script %s: %s", outpath, e,
        location = location
      )

  def clear_for_source(
    self,
    source_path: str,
    *,
    location: Any | None = None,
  ):
    base = self.source_basename(source_path)
    target_dir = os.path.join(self.scripts_root, base)

    # Defensive: only remove directories under scripts_root.
    abs_target = os.path.realpath(target_dir)
    abs_root = os.path.realpath(self.scripts_root)
    try:
      if os.path.commonpath([abs_target, abs_root]) != abs_root:
        return
    except ValueError:
      return

    if os.path.exists(target_dir):
      try:
        shutil.rmtree(target_dir)
        store_logger.info(
          "Cleared EasyCrypt scripts: %s", self._relpath(target_dir),
          location = location
        )

      except OSError as e:
        store_logger.warning(
          "Failed to clear EasyCrypt scripts: %s: %s", target_dir, e,
          location = location
        )

# ======================================================================
class EasyCryptProofDirective(su.docutils.SphinxDirective):
  TRAP_RE = r'\(\*\s*\$\s*\*\)\s*'

  has_content = True

  option_spec = {
    'title': su.docutils.directives.unchanged,
  }

  def find_trap(self, source: str):
    location = (self.env.docname, self.lineno)

    if (trap := re.search(self.TRAP_RE, source, re.MULTILINE)) is None:
      logger.error(
        'Cannot find the trap',
        location = location, type = EasyCryptError.category)
      raise EasyCryptError

    return trap

  def run_easycrypt(self, source: str):
    location = (self.env.docname, self.lineno)

    cache = EasyCryptCache.get_cache(self.env.app)
    if cache is not None:
      cached = cache.load(source, location = location)
      if cached is not None:
        return cached

    with tempfile.TemporaryDirectory(delete = False) as tmpdir:
      ecfile  = os.path.join(tmpdir, 'input.ec')
      ecofile = os.path.join(tmpdir, 'input.eco')

      with open(ecfile, 'w') as ecstream:
        ecstream.write(source)

      logger.info(
        "Running EasyCrypt command: %s",
        " ".join(['easycrypt', 'compile', '-script', '-pragmas', 'Proofs:weak', '-trace', ecfile]),
        location = location
      )
      EasyCrypt.run(
        ['easycrypt', 'compile', '-script', '-pragmas', 'Proofs:weak', '-trace', ecfile],
        location = location
      )

      with open(ecofile) as ecostream:
        eco = json.load(ecostream)

      if cache is not None:
        cache.store(source, eco, location = location)

      return eco

  def create_widget(self, code: str, sentence: int, eco: Any):
    serial = self.state.document.settings.env.new_serialno("proofnav")
    uid = f"proofnav-{serial}"

    sentences = [
      dict(goals = x["goals"], message = x["messages"])
      for x in eco["trace"][1:]
    ]

    data = dict(
      source       = code,
      sentenceEnds = [x["position"] for x in eco["trace"][1:]],
      sentences    = sentences,
      initialSentence = sentence - 1,
    )

    if 'title' in self.options:
      data['title'] = self.options['title']      

    node = ProofnavNode()
    node["uid"] = uid
    node["json"] = json.dumps(
      data, ensure_ascii = False, separators = (",", ":"), indent = 2)
      
    return node

  def run(self):
    try:
      rawcode = '\n'.join(self.content) + '\n'

      # Find the trap and erase it
      trap = self.find_trap(rawcode)
      code = rawcode[:trap.start()] + rawcode[trap.end():]
      
      # Find the trap sentence number
      sentences = [
        m.end() - 1
        for m in re.finditer(r'\.(\s+|\$)', code)
      ]
      sentence = bisect.bisect_left(sentences, trap.start())

      # Save script for later inspection
      script_store = EasyCryptScriptStore.get_store(self.env.app)
      if script_store is not None:
        script_store.save(
          code,
          self.state.document.current_source,
          location = (self.env.docname, self.lineno),
        )

      # Run EasyCrypt and extract the proof trace
      eco = self.run_easycrypt(code)

      # Create the widget
      node = self.create_widget(code, sentence, eco)
      return [node]
    
    except EasyCryptError:
      self.state.document.settings.env.note_reread()

      fallback = du.nodes.literal_block(
        "[easycrypt failed]",
        "[easycrypt failed]",
      )
      return [fallback]

# ======================================================================
def on_builder_inited(app: sa.Sphinx):
  out_dir = os.path.join(app.outdir, "_static", "proofnav")
  os.makedirs(out_dir, exist_ok = True)

  js  = os.path.join(ROOT, "proofnav", "dist", "proofnav.bundle.js")
  css = os.path.join(ROOT, "proofnav", "proofnav.css")

  if not os.path.exists(js):
    raise se.SphinxError(
      "proofnav: bundle not found. Run the frontend build to generate "
      f"{js}"
    )

  su.fileutil.copy_asset(js, out_dir)
  su.fileutil.copy_asset(js + ".map", out_dir)
  su.fileutil.copy_asset(css, out_dir)

# ======================================================================
def on_source_read(app: sa.Sphinx, docname: str, source: list[str]):
  if (script_store := EasyCryptScriptStore.get_store(app)) is None:
    return
  source_path = app.env.doc2path(docname)
  script_store.clear_for_source(source_path, location = (docname, None))

# ======================================================================
def setup(app: sa.Sphinx) -> su.typing.ExtensionMetadata:
  app.add_node(
    ProofnavNode,
    html = (
      ProofnavNode.visit_proofnav_node_html,
      ProofnavNode.depart_proofnav_node_html,
    )
  )

  app.add_config_value("ecproofs_cache_dir", "_ecproofs_cache", "env")
  app.add_config_value("ecproofs_scripts_dir", "_ecproofs_scripts", "env")

  app.add_js_file("proofnav/proofnav.bundle.js", defer = "defer")
  app.add_css_file("proofnav/proofnav.css")

  app.connect("builder-inited", on_builder_inited)
  app.connect("source-read", on_source_read)

  app.add_directive('ecproof', EasyCryptProofDirective)

  return {
    'version': '0.1',
    'parallel_read_safe': True,
    'parallel_write_safe': True,
  }
