#!/usr/bin/env python3
"""Verbatim quotation handler for EasyCrypt.

Protocol (see doc/quotations.rst):
  stdin : "#ec-quote v1 name=... file=... line=L col=C off=O\n" + body
  stdout: a single JSON object { "expanded": <str>, "segments": [...] }

This handler copies the body through unchanged, emitting a single VERBATIM
segment so that any error EasyCrypt reports inside the expansion maps back to
the exact original character.  It is the simplest possible black-box tool and
exercises the column-precise reverse location mapping.
"""
import sys
import json


def main() -> int:
    raw = sys.stdin.buffer.read().decode("utf-8", "replace")
    # split header line from body
    nl = raw.find("\n")
    body = raw[nl + 1:] if nl >= 0 else raw

    expanded = body  # identity
    segments = [{
        "out": [0, len(expanded)],
        "in":  [0, len(body)],
        "kind": "verbatim",
    }]

    json.dump({"expanded": expanded, "segments": segments}, sys.stdout)
    sys.stdout.flush()
    return 0


if __name__ == "__main__":
    sys.exit(main())
