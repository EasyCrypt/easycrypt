#!/usr/bin/env python3
"""
Fifo-backed daemon exposing one persistent `easycrypt llm` instance to many
shell callers. Typical use case: an LLM agent (Claude Code, etc.) that
invokes a bash tool *once per tactic* — the agent can't hold stdin/stdout
open across turns, so without a daemon every tactic would re-LOAD the
whole file prefix.

Protocol (matches the JSON line format produced by `ec_send.sh`):

    request  (one line on stdin-fifo):
        {"op": "<op>", "arg": "...", "arg2": "...", "nosmt": bool}

    response (one line on stdout-fifo):
        {"ok": bool, "uuid": N, "resp": "..."}

Supported ops:
    load        arg=path, arg2=line (string or int), optional nosmt: bool
    tactic      arg="proc."
    tactic_multiline  arg="<multi-line body>"   (wraps in <BEGIN>/<DONE>)
    undo
    revert      arg="<uuid-or-name>"
    checkpoint  arg="<name>"
    goals
    goals_all
    search      arg="<pattern>"
    quiet       arg="on"|"off"
    close

Usage:
    # start daemon (in background)
    python3 scripts/llm/daemon.py --cwd /path/to/project \\
        --in-fifo /tmp/ec_in --out-fifo /tmp/ec_out &

    # then drive with scripts/llm/ec_send.sh (see that file for details)

The fifos are created if they don't exist. Only one connected writer and
one connected reader are expected at a time — the client (`ec_send.sh`)
enforces this by opening them sequentially.
"""

import argparse
import json
import os
import sys
import traceback

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from ec_llm import ECLLM  # noqa: E402


def _ensure_fifo(path):
    if not os.path.exists(path):
        os.mkfifo(path)
    elif not os.path.exists(path):  # raced out; recreate
        os.mkfifo(path)


def _handle(req, ec):
    op = req.get("op")
    arg = req.get("arg", "")
    arg2 = req.get("arg2", "")

    if op == "load":
        ok, resp = ec.load(arg, int(arg2), nosmt=bool(req.get("nosmt", False)))
    elif op == "tactic":
        ok, resp = ec.tactic(arg)
    elif op == "tactic_multiline":
        ok, resp = ec.tactic_multiline(arg)
    elif op == "undo":
        ok, resp = ec.undo()
    elif op == "revert":
        ok, resp = ec.revert(arg)
    elif op == "checkpoint":
        ok, resp = ec.checkpoint(arg)
    elif op == "goals":
        resp, ok = ec.goals(), True
    elif op == "goals_all":
        resp, ok = ec.goals_all(), True
    elif op == "search":
        resp, ok = ec.search(arg), True
    elif op == "quiet":
        ok, resp = ec.quiet(on=(arg.lower() == "on"))
    elif op == "close":
        ec.close()
        return {"ok": True, "uuid": ec.uuid, "resp": "bye"}, True
    else:
        return {"ok": False, "uuid": ec.uuid, "resp": f"unknown op: {op}"}, False

    return {"ok": ok, "uuid": ec.uuid, "resp": resp}, False


def main():
    p = argparse.ArgumentParser(description=__doc__.splitlines()[1])
    p.add_argument("--cwd", default=None, help="Project root (default: cwd)")
    p.add_argument("--in-fifo", default="/tmp/ec_in", help="Request fifo path")
    p.add_argument("--out-fifo", default="/tmp/ec_out", help="Response fifo path")
    p.add_argument("--log", default="/tmp/ec_daemon.log", help="Log file")
    p.add_argument("--prover", default=None, help="SMT prover (e.g. Z3)")
    p.add_argument("--timeout", type=int, default=None, help="Per-goal SMT timeout (s)")
    args = p.parse_args()

    _ensure_fifo(args.in_fifo)
    _ensure_fifo(args.out_fifo)

    extra = []
    if args.prover:
        extra += ["-p", args.prover]
    if args.timeout is not None:
        extra += ["-timeout", str(args.timeout)]

    ec = ECLLM(cwd=args.cwd, extra_args=extra)
    with open(args.log, "w") as lf:
        lf.write(f"EC started. uuid={ec.uuid}\n")

    while True:
        try:
            # Opening a fifo for reading blocks until a writer opens it.
            with open(args.in_fifo, "r") as fi:
                line = fi.readline()
            if not line.strip():
                continue
            req = json.loads(line)
            result, should_exit = _handle(req, ec)
            with open(args.out_fifo, "w") as fo:
                fo.write(json.dumps(result) + "\n")
            if should_exit:
                break
        except Exception:
            with open(args.log, "a") as lf:
                lf.write("EXCEPTION: " + traceback.format_exc() + "\n")
            try:
                with open(args.out_fifo, "w") as fo:
                    fo.write(json.dumps({"ok": False, "uuid": -1,
                                         "resp": traceback.format_exc()}) + "\n")
            except Exception:
                pass


if __name__ == "__main__":
    main()
