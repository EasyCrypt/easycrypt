#! /bin/bash

target="$(dirname $0)/../_tools/ocaml-4.00.1/etc/ocamlbrew.bashrc"

if [ ! -e "$target" ]; then
  cat <<__EOF__ >&2
Install the EasyCrypt toolchain first ([make toolchain])
__EOF__
  exit 1
fi

echo ". ${target}"
