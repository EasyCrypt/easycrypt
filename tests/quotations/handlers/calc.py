#!/usr/bin/env python3
"""'calc' quotation handler: evaluate an integer arithmetic expression and
splice the resulting literal into EasyCrypt source.

A quotation expands to a sentence *fragment*; the surrounding sentence (and
its terminating '.') is written by the user.  So the body is a bare
expression and the expansion is just its value:

    op forty_two = {% calc 6 * 7 %}.
  expands to
    op forty_two = 42.

The literal has no 1:1 origin, so the whole output is reported as a single
SYNTHESIZED segment mapping to the whole body: any downstream error points at
the quotation region as a whole.
"""
import sys
import json


def main() -> int:
    raw = sys.stdin.buffer.read().decode("utf-8", "replace")
    nl = raw.find("\n")
    body = raw[nl + 1:] if nl >= 0 else raw
    expr = body.strip()

    try:
        # integer arithmetic only; no names/builtins
        value = eval(expr, {"__builtins__": {}}, {})  # noqa: S307 (sandboxed)
        if not isinstance(value, int):
            raise ValueError("result is not an integer")
    except Exception as e:  # noqa: BLE001
        sys.stderr.write(f"#ec-error off=0 len={len(body)} message=calc: {e}\n")
        return 1

    expanded = str(value)
    segments = [{
        "out": [0, len(expanded)],
        "in":  [0, len(body)],
        "kind": "synthesized",
    }]

    json.dump({"expanded": expanded, "segments": segments}, sys.stdout)
    sys.stdout.flush()
    return 0


if __name__ == "__main__":
    sys.exit(main())
