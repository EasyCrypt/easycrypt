#!/usr/bin/env bash
#
# QUICK-BUNDLE — beta-1 bundled .vsix builder (darwin-arm64 only).
#
# Quarantined dirty bundling. The proper script (cross-platform,
# CI-hookable, full resolver-chain wiring) is the ~1 day follow-up
# documented in HANDOFF-VSCODE-FIRST.md § G. Until that lands,
# this single-purpose script copies pre-built `ec` and `ecd` into
# <vscode>/bin/darwin-arm64/, codesigns them, and runs vsce.
#
# To clean up: delete this script + vscode/scripts/, delete
# vscode/src/quickBundle.ts, drop the quickBundleBinary() calls
# in extension.ts, and replace with the proper bundling pipeline.
#
# Usage (run from the worktree root, after a successful `make`):
#
#   vscode/scripts/quick-bundle.sh
#
# Output:
#   vscode/easycrypt-tooling-bundled-darwin-arm64.vsix
#
# Requires: vsce on PATH (in our nix devshell once vsce is added),
# darwin-arm64 host (we're not cross-bundling).

set -euo pipefail

if [[ "$(uname -s)" != "Darwin" ]] || [[ "$(uname -m)" != "arm64" ]]; then
  echo "quick-bundle.sh: darwin-arm64 only (got $(uname -s)/$(uname -m))" >&2
  exit 1
fi

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
VSCODE_DIR="$(cd "${SCRIPT_DIR}/.." && pwd)"
WORKTREE_DIR="$(cd "${VSCODE_DIR}/.." && pwd)"

EC_SRC="${WORKTREE_DIR}/ec.native"
ECD_SRC="${WORKTREE_DIR}/_build/default/ecd.native"

if [[ ! -e "${EC_SRC}" ]]; then
  echo "quick-bundle.sh: ec.native not found at ${EC_SRC}; run \`make\` first" >&2
  exit 1
fi
if [[ ! -e "${ECD_SRC}" ]]; then
  echo "quick-bundle.sh: ecd.native not found at ${ECD_SRC}; run \`make\` first" >&2
  exit 1
fi

BIN_DIR="${VSCODE_DIR}/bin/darwin-arm64"
mkdir -p "${BIN_DIR}"

# Resolve symlinks so we copy the actual ELF/Mach-O.
cp -f "$(readlink -f "${EC_SRC}" 2>/dev/null || echo "${EC_SRC}")" "${BIN_DIR}/ec.native"
cp -f "$(readlink -f "${ECD_SRC}" 2>/dev/null || echo "${ECD_SRC}")" "${BIN_DIR}/ecd.native"
chmod +x "${BIN_DIR}/ec.native" "${BIN_DIR}/ecd.native"

# Codesign so Gatekeeper doesn't quarantine on launch. `-s -` is
# ad-hoc signing — fine for first-circle beta; CI-grade signing
# lives with the proper bundling work.
codesign -f -s - "${BIN_DIR}/ec.native"
codesign -f -s - "${BIN_DIR}/ecd.native"

# EC's EcRelocate resolves theories/etc/styles as siblings of the
# binary when invoked as `ec.native` (the eclocal path). Mirror
# the source-tree layout next to the bundled binary so a freshly
# spawned EC subprocess sees its prelude on disk.
THEORIES_SRC="${WORKTREE_DIR}/theories"
ETC_SRC="${WORKTREE_DIR}/etc"
STYLES_SRC="${WORKTREE_DIR}/assets/styles"

if [[ ! -d "${THEORIES_SRC}" ]]; then
  echo "quick-bundle.sh: theories/ not found at ${THEORIES_SRC}" >&2
  exit 1
fi

rm -rf "${BIN_DIR}/theories" "${BIN_DIR}/etc" "${BIN_DIR}/assets"
cp -R "${THEORIES_SRC}" "${BIN_DIR}/theories"
[[ -d "${ETC_SRC}" ]] && cp -R "${ETC_SRC}" "${BIN_DIR}/etc"
[[ -d "${STYLES_SRC}" ]] && { mkdir -p "${BIN_DIR}/assets" && cp -R "${STYLES_SRC}" "${BIN_DIR}/assets/styles"; }

cd "${VSCODE_DIR}"
npm install
npm run compile

# QUICK-BUNDLE: strip devDeps so the .vsix only carries runtime
# packages. Without this, .vscodeignore's `**` minus devDeps would
# need a hand-maintained allowlist of every transitive runtime
# dep — fragile (we already hit minimatch, semver, ...). After
# the package step we restore the full tree for further dev.
npm prune --production
OUTPUT="${VSCODE_DIR}/easycrypt-tooling-bundled-darwin-arm64.vsix"
vsce package --target darwin-arm64 --out "${OUTPUT}"
npm install

echo
echo "Done: ${OUTPUT}"
ls -lh "${OUTPUT}"
