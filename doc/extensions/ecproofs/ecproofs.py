# --------------------------------------------------------------
from __future__ import annotations
from typing import Any

import docutils as du

import sphinx.application as sa
import sphinx.errors      as se
import sphinx.util        as su

import bisect
import json
import os
import re
import subprocess as subp
import tempfile


# ======================================================================
ROOT = os.path.dirname(__file__)

# ======================================================================
logger = su.logging.getLogger(__name__)

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
  def run(cmd, *, location: Any | None = None, warn_only: bool = True):
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
class EasyCryptProofDirective(su.docutils.SphinxDirective):
  TRAP_RE = r'\(\*\s*\$\s*\*\)\s*'

  has_content = True

  option_spec = {
    'title': su.docutils.directives.unchanged,
  }

  def find_trap(self, source: str):
    location = (self.state.document.current_source, self.lineno)

    if (trap := re.search(self.TRAP_RE, source, re.MULTILINE)) is None:
      logger.error(
        'Cannot find the trap',
        location = location, type = EasyCryptError.category)
      raise EasyCryptError

    return trap

  def run_easycrypt(self, source: str):
    location = (self.state.document.current_source, self.lineno)

    with tempfile.TemporaryDirectory(delete = False) as tmpdir:
      ecfile  = os.path.join(tmpdir, 'input.ec')
      ecofile = os.path.join(tmpdir, 'input.eco')

      with open(ecfile, 'w') as ecstream:
        ecstream.write(source)

      EasyCrypt.run(
        ['easycrypt', 'compile', '-script', '-pragmas', 'Proofs:weak', '-trace', ecfile],
        location = location
      )

      with open(ecofile) as ecostream:
        return json.load(ecostream)

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
def setup(app: sa.Sphinx) -> su.typing.ExtensionMetadata:
  app.add_node(
    ProofnavNode,
    html = (
      ProofnavNode.visit_proofnav_node_html,
      ProofnavNode.depart_proofnav_node_html,
    )
  )

  app.add_js_file("proofnav/proofnav.bundle.js", defer = "defer")
  app.add_css_file("proofnav/proofnav.css")

  app.connect("builder-inited", on_builder_inited)

  app.add_directive('ecproof', EasyCryptProofDirective)

  return {
    'version': '0.1',
    'parallel_read_safe': True,
    'parallel_write_safe': True,
  }
