#!/bin/bash
# Send one JSON request to the EasyCrypt LLM daemon, print the response.
#
# Usage:
#   ec_send.sh '{"op":"tactic","arg":"proc."}'       # inline JSON
#   ec_send.sh --file /path/to/request.json          # JSON from file
#
# The --file form is useful for tactic payloads containing shell-meta
# characters (e.g. EC escapes like /\\) that would otherwise need
# elaborate quoting.
#
# Fifo paths default to /tmp/ec_in, /tmp/ec_out and can be overridden via
# env vars EC_IN_FIFO, EC_OUT_FIFO. The daemon must already be running
# and listening on the same fifos.
set -eu

IN_FIFO="${EC_IN_FIFO:-/tmp/ec_in}"
OUT_FIFO="${EC_OUT_FIFO:-/tmp/ec_out}"

if [ "${1:-}" = "--file" ]; then
  REQ=$(cat "$2")
else
  REQ="$1"
fi

# Write in background so we can read the response; fifos block until both
# ends are connected.
printf '%s\n' "$REQ" > "$IN_FIFO" &
WRITER=$!
RESP=$(cat "$OUT_FIFO")
wait "$WRITER"

python3 -c "import sys, json
r = json.loads(sys.argv[1])
print('OK' if r['ok'] else 'ERR', 'uuid=', r['uuid'])
print(r['resp'])" "$RESP"
