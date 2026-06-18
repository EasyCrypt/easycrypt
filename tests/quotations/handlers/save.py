#!/usr/bin/env python3
"""'ecm4' quotation handler: process a whole quotation using
the m4 macro processor.

The input should consist of the header line (ignored), followed by a
line with the name of an m4 file to be included (trimmed for
whitespace at beginning and end), followed by any number of lines
consisting of the text to be processed by m4 (also trimmed for
whitespace), normally using definitions from the included file.  The
output is trimmed for whitespace at its beginning and end.

The m4 open and close quotation sequences are changed to `<<<` and
`>>>`, and the begin comment sequence is changed to `###` so that the
characters `, ' and # can be used in the m4 filename, contents of the
file, and input lines as normal characters. Consequently, neither <<<,
>>> nor ### should appear in the filename, contents of the file, or
input lines.

The include path for m4 is found in the user environment variable
ECM4PATH, if it is set.

In EasyCrypt, ecm4 should be invoked via a *whole* quotation.

E.g.,

{%! ecm4 foo.m4
Test(a, b, c).
!%}

will cause m4 to include the file foo.m4, and then evaluate the macro
call Test(a, b, c), outputing the result.

For debugging purposes, use

{%!* ecm4 foo.m4
Test(a, b, c).
!%}

in order to see the result of the m4 evaluation in the response buffer.

The output is reported as a single SYNTHESIZED segment mapping to the
whole body: any downstream error points at the quotation region as a
whole.

"""
import sys
import os
import json
import subprocess
import itertools

def main() -> int:
    try:
      raw = sys.stdin.buffer.read().decode("utf-8", "replace")
      nl = raw.find("\n")
      if nl < 0:
        raise ValueError("missing first newline")
      body = (raw[nl + 1:]).strip()
      nl = body.find("\n")
      if nl < 0:
        raise ValueError("missing second newline")
      m4file = (body[:nl]).strip()
      rest = body[nl + 1:]
      m4header = "changequote(<<<, >>>)dnl\nchangecom(<<<###>>>)dnl\n"
      m4header = m4header + "include(" + m4file + ")dnl\n"
      m4input = m4header + rest
      ip = m4input.encode("utf-8")
      m4include = (os.environ.get("ECM4PATH", "")).strip()
      if m4include == "":
        m4cmd = ["m4", "-E"]
      else:
        m4args = list(map(lambda s: ["-I", s], m4include.split(":")))
        m4args = list(itertools.chain.from_iterable(m4args))
        m4cmd = ["m4", "-E"] + m4args
      result = subprocess.run(m4cmd, stdout=subprocess.PIPE,
                              stderr=subprocess.DEVNULL, check=True, input=ip)
      result = (result.stdout.decode("utf-8")).strip()
    except Exception as e:
        sys.stderr.write(f"#ec-error off=0 len={len(body)} message=ecm4: {e}\n")
        return 1
    expanded = result
    segments = [{
        "out":  [0, len(expanded)],
        "in":   [0, len(body)],
        "kind": "synthesized"
    }]
    json.dump({"expanded": expanded, "segments": segments}, sys.stdout)
    sys.stdout.flush()
    return 0

if __name__ == "__main__":
    sys.exit(main())
