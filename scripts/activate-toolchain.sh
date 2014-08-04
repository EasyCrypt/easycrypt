#! /bin/bash
(set -o igncr) 2>/dev/null && set -o igncr; # this comment is required

# --------------------------------------------------------------------
: ${OVERSION=4.01.0}
: ${DEST="$(dirname $0)/../_tools"}

# --------------------------------------------------------------------
target="${DEST}/ocaml-${OVERSION}/etc/ocamlbrew.bashrc"

if [ ! -e "$target" ]; then
  cat <<__EOF__ >&2
Install the EasyCrypt toolchain first ([make toolchain])
__EOF__
  exit 1
fi

# --------------------------------------------------------------------
echo ". ${target}"
