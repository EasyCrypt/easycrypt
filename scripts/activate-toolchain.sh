#! /bin/bash
(set -o igncr) 2>/dev/null && set -o igncr; # this comment is required

# --------------------------------------------------------------------
cat <<__EOF__ >&2
WARNING: This script must now be sourced, i.e., executed using
WARNING:     >> source ${0}

__EOF__

# --------------------------------------------------------------------
EC_SRC_ROOT="$(dirname $0)"

# --------------------------------------------------------------------
function activate {
  : ${EC_TOOLCHAIN_ROOT="${EC_SRC_ROOT}/../_tools"}
  : ${OVERSION=4.01.0}

  if [ ! -z "${EC_TOOLCHAIN_ACTIVATED}" ]; then
    echo "An EasyCrypt toolchain has already been activated in this shell." >&2
    return
  fi
  
  EC_TOOLCHAIN_ETC="${EC_TOOLCHAIN_ROOT}/ocaml-${OVERSION}/etc/ocamlbrew.bashrc"

  if [ ! -e "${EC_TOOLCHAIN_ETC}" ]; then
    cat <<__EOF__ >&2
Install the EasyCrypt toolchain (${OVERSION}) first ([make toolchain])

If you have a toolchain installed in a different version, you can
set the OVERSION environment variable to the right version.

You can find bellow the list of installed toolchains:

__EOF__

    echo '---------- START OF LISTING ----------'
    [ -d "${EC_TOOLCHAIN_ROOT}" ] && {
      ls -1 "${EC_TOOLCHAIN_ROOT}" | grep '^ocaml-' | sed 's/ocaml-//';
    }
    echo '---------- END OF LISTING   ----------'

    return
  fi

  source "${EC_TOOLCHAIN_ETC}"

  export EC_TOOLCHAIN_ACTIVATED=1
}

# --------------------------------------------------------------------
activate; unset -f activate
