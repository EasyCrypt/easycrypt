#!/usr/bin/env bash
# boundary-lint.sh — enforce that tooling/**/dune (libraries ...) stanzas
# reference only libraries listed in tooling/.boundary-allowlist.
#
# Rationale: the daemon must talk to EasyCrypt only through the `ec llm`
# subprocess. Linking EC internals would violate the split plan and
# bypass the UPSTREAM.md discipline. See doc/commit-conventions.md.
#
# Exit 0 on clean; exit 1 on violations.

set -euo pipefail

repo_root="$(git rev-parse --show-toplevel)"
allowlist="$repo_root/tooling/.boundary-allowlist"

if [[ ! -f "$allowlist" ]]; then
  echo "boundary-lint: missing allowlist at $allowlist" >&2
  exit 2
fi

allowed_file=$(mktemp)
trap 'rm -f "$allowed_file"' EXIT
grep -vE '^\s*(#|$)' "$allowlist" | awk '{print $1}' > "$allowed_file"

status=0

# Extract (libraries ...) content. Permissive: handles multi-line,
# single-line, and bare-stanza forms. Stops at the first closing paren,
# which is sufficient for the dune forms we write.
extract_libs() {
  perl -0777 -ne '
    while (/\(\s*libraries\s+([^)]*)\)/sg) {
      my $block = $1;
      $block =~ s/\s+/ /g;
      print "$block\n";
    }
  ' "$1"
}

violations=0

while IFS= read -r dune_file; do
  libs=$(extract_libs "$dune_file")
  for lib in $libs; do
    [[ -z "$lib" ]] && continue
    # Skip dune sub-expressions (e.g. `(select ...)`, `(re_export ...)`)
    # that aren't plain library names.
    [[ "$lib" == *"("* || "$lib" == *")"* ]] && continue
    if ! grep -qFx "$lib" "$allowed_file"; then
      printf '%s: uses library %q, not in %s\n' \
        "${dune_file#$repo_root/}" "$lib" "${allowlist#$repo_root/}" >&2
      violations=$((violations + 1))
    fi
  done
done < <(find "$repo_root/tooling" -name 'dune' -type f 2>/dev/null || true)

if [[ $violations -gt 0 ]]; then
  echo "" >&2
  echo "boundary-lint: $violations violation(s)." >&2
  echo "If the dependency is legitimate, add it to ${allowlist#$repo_root/} in the same commit." >&2
  status=1
fi

if [[ $status -eq 0 ]]; then
  echo "boundary-lint: clean."
fi

exit $status
