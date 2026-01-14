# --------------------------------------------------------------
from __future__ import annotations

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
class EasyCryptProofDirective(su.docutils.SphinxDirective):
  has_content = True

  option_spec = {
    'title': su.docutils.directives.unchanged,
  }

  def run(self):
    env = self.state.document.settings.env

    rawcode = '\n'.join(self.content) + '\n'

    # Find the trap
    if (trap := re.search(r'\(\*\s*\$\s*\*\)\s*', rawcode, re.MULTILINE)) is None:
      raise se.SphinxError('Cannot find the trap')
    code = rawcode[:trap.start()] + rawcode[trap.end():]
    
    # Find the trap sentence number
    sentences = [
      m.end() - 1
      for m in re.finditer(r'\.(\s+|\$)', code)
    ]
    sentence = bisect.bisect_left(sentences, trap.start())

    # Run EasyCrypt and extract the proof trace
    with tempfile.TemporaryDirectory(delete = False) as tmpdir:
      ecfile  = os.path.join(tmpdir, 'input.ec')
      ecofile = os.path.join(tmpdir, 'input.eco')
      with open(ecfile, 'w') as ecstream:
        ecstream.write(code)
      subp.check_call(
        ['easycrypt', 'compile', '-pragmas', 'Proofs:weak', '-trace', ecfile],
        stdout = subp.DEVNULL,
        stderr = subp.DEVNULL,
      )
      with open(ecofile) as ecostream:
        eco = json.load(ecostream)

    serial = env.new_serialno("proofnav")
    uid = f"proofnav-{serial}"

    # Create widget metadata
    data = dict()

    data["source"] = code
    data["sentenceEnds"] = [x["position"] for x in eco["trace"][1:]]
    data["sentences"] = [
      dict(goals = x["goals"], message = x["messages"])
      for x in eco["trace"][1:]
    ]
    data["initialSentence"] = sentence - 1

    if 'title' in self.options:
      data['title'] = self.options['title']      

    node = ProofnavNode()
    node["uid"] = uid
    node["json"] = json.dumps(
      data, ensure_ascii = False, separators = (",", ":"), indent = 2)

    return [node]

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
