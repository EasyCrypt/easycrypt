#! /bin/bash

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
