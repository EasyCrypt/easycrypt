"""
Python binding for the `easycrypt llm` interactive REPL.

Usage:
    from ec_llm import ECLLM

    ec = ECLLM(cwd="path/to/project")    # start REPL in project dir, wait for READY
    ec.load("proofs/foo.ec", 42)          # load through line 42
    ec.load("proofs/foo.ec", 100, nosmt=True)  # fast prefix load, skip SMT
    ec.checkpoint("c0")                   # name current state
    ec.goals()                            # first subgoal + remaining count
    ec.goals_all()                        # all subgoals
    ec.tactic("apply H.")                 # send one tactic (must end with '.')
    ec.revert("c0")                       # instant jump back to saved state
    ec.search("(fdom _)")                 # pattern-based lemma search
    ec.close()

Protocol (from `doc/llm/CLAUDE.md`):
  - Each response ends with a line containing only `<END>`.
  - `OK [uuid:N] ... <END>` — success, uuid incremented.
  - `ERROR [uuid:N] ... <END>` — failure, uuid unchanged.

Run EasyCrypt from a directory that contains (or is under) a valid
`easycrypt.project`, otherwise `LOAD` will not resolve library paths.
"""

import os
import re
import subprocess


class ECLLM:
    """Thin Python wrapper around one `easycrypt llm` process."""

    def __init__(self, cwd=None, extra_args=None, exe="easycrypt"):
        """
        Start an `easycrypt llm` subprocess and block until READY.

        Args:
          cwd: Working directory (should contain / be under easycrypt.project).
               Defaults to os.getcwd().
          extra_args: Extra CLI flags passed to `easycrypt llm`, e.g.
                      `["-p", "Z3", "-timeout", "5"]`.
          exe: Name or path of the EasyCrypt binary (default: `easycrypt`).
        """
        if cwd is None:
            cwd = os.getcwd()
        args = [exe, "llm"]
        if extra_args:
            args.extend(extra_args)
        self.proc = subprocess.Popen(
            args,
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            bufsize=1,
            cwd=cwd,
        )
        self.uuid = 0
        banner = self._read_until_end()
        if "READY" not in banner:
            raise RuntimeError(f"Expected READY, got:\n{banner}")

    # ------------------------------------------------------------------ protocol

    def _read_until_end(self):
        """Read lines until a line that is exactly `<END>` (stripped)."""
        lines = []
        for raw in self.proc.stdout:
            line = raw.rstrip("\n")
            if line.strip() == "<END>":
                break
            lines.append(line)
        return "\n".join(lines)

    def _send(self, command):
        """Send one command line and return the full response body."""
        self.proc.stdin.write(command + "\n")
        self.proc.stdin.flush()
        return self._read_until_end()

    def _parse_status(self, response):
        """Update self.uuid and return True on OK, False on ERROR.

        LOAD responses may include theory/axiom dumps before the status
        line, so we search the entire response.
        """
        m_ok = re.search(r'^OK\s+\[uuid:(\d+)\]', response, re.MULTILINE)
        m_err = re.search(r'^ERROR\s+\[uuid:(\d+)\]', response, re.MULTILINE)
        if m_ok:
            self.uuid = int(m_ok.group(1))
            return True
        if m_err:
            return False
        # Fallback: tolerate early-banner responses
        return response.lstrip().upper().startswith("OK")

    # ------------------------------------------------------------------ commands

    def load(self, path, line, nosmt=False):
        """LOAD `path` through `line`. Returns `(ok, response)`."""
        cmd = f'LOAD "{path}" {line}'
        if nosmt:
            cmd += " -nosmt"
        resp = self._send(cmd)
        return self._parse_status(resp), resp

    def checkpoint(self, name):
        """Save the current uuid under `name` for later REVERT."""
        resp = self._send(f"CHECKPOINT {name}")
        return self._parse_status(resp), resp

    def revert(self, name_or_uuid):
        """Jump back to a named checkpoint or a uuid."""
        resp = self._send(f"REVERT {name_or_uuid}")
        return self._parse_status(resp), resp

    def undo(self):
        """Undo the last successful step."""
        resp = self._send("UNDO")
        return self._parse_status(resp), resp

    def goals(self):
        """Return the first subgoal + remaining count."""
        return self._send("GOALS")

    def goals_all(self):
        """Return all open subgoals."""
        return self._send("GOALS ALL")

    def tactic(self, tac):
        """Send one EasyCrypt statement (must end with `.`). Returns `(ok, response)`."""
        resp = self._send(tac)
        return self._parse_status(resp), resp

    def tactic_multiline(self, body):
        """Send a multi-line EasyCrypt block delimited by `<BEGIN>`/`<DONE>`."""
        payload = "<BEGIN>\n" + body.rstrip() + "\n<DONE>"
        resp = self._send(payload)
        return self._parse_status(resp), resp

    def search(self, pattern):
        """Run `SEARCH pattern` — pattern syntax per the EasyCrypt manual."""
        return self._send(f"SEARCH {pattern}")

    def quiet(self, on=True):
        """Turn automatic goal display after each tactic on/off."""
        resp = self._send("QUIET ON" if on else "QUIET OFF")
        return self._parse_status(resp), resp

    def close(self):
        """Terminate the subprocess (sends QUIT, then waits)."""
        try:
            self.proc.stdin.write("QUIT\n")
            self.proc.stdin.flush()
            self.proc.stdin.close()
        except (BrokenPipeError, ValueError):
            pass
        try:
            self.proc.wait(timeout=5)
        except subprocess.TimeoutExpired:
            self.proc.kill()

    # Context manager support
    def __enter__(self):
        return self

    def __exit__(self, exc_type, exc, tb):
        self.close()


# -------------------------------------------------------------------------- CLI

def _main():
    import argparse
    p = argparse.ArgumentParser(
        description="Quick LOAD check: compile a file through a line and report status."
    )
    p.add_argument("file", help="EasyCrypt source file (relative to --cwd)")
    p.add_argument("line", type=int, help="Line number to load through")
    p.add_argument("--cwd", default=None, help="Project root (default: cwd)")
    p.add_argument("--nosmt", action="store_true", help="Skip SMT during LOAD")
    p.add_argument("--timeout", type=int, default=None, help="Per-goal SMT timeout (s)")
    p.add_argument("--prover", default=None, help="SMT prover (e.g. Z3)")
    p.add_argument("--quiet", action="store_true", help="Suppress response body")
    args = p.parse_args()

    extra = []
    if args.prover:
        extra += ["-p", args.prover]
    if args.timeout is not None:
        extra += ["-timeout", str(args.timeout)]

    with ECLLM(cwd=args.cwd, extra_args=extra) as ec:
        ok, resp = ec.load(args.file, args.line, nosmt=args.nosmt)
        status = "OK" if ok else "ERROR"
        print(f"{status} uuid={ec.uuid}")
        if not args.quiet:
            print(resp)
    raise SystemExit(0 if ok else 1)


if __name__ == "__main__":
    _main()
