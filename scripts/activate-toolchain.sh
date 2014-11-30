#! /bin/bash
                                               # this comment is required
if [ -n "$BASH" ]; then                        # ------------------------
  (set -o igncr) 2>/dev/null && set -o igncr;  # ------------------------
fi                                             # ------------------------

# --------------------------------------------------------------------
_OVERSION=${OVERSION:-4.02.1}

# --------------------------------------------------------------------
cat <<__EOF__ >&2
WARNING: This script must now be sourced, i.e., executed using
WARNING:     >> source ./scripts/activate-toolchain.sh

__EOF__

# --------------------------------------------------------------------
if [ "$EC_SRC_ROOT" = "" ]; then
  if [ "$BASH_SOURCE" != "" ]; then
    _EC_SRC_ROOT="$(dirname $BASH_SOURCE)"
  else
    _EC_SRC_ROOT="$(dirname $0)"
  fi
else
  _EC_SRC_ROOT="${EC_SRC_ROOT}"
fi

# --------------------------------------------------------------------
_EC_TOOLCHAIN_ROOT="${EC_TOOLCHAIN_ROOT:-${_EC_SRC_ROOT}/../_tools}"

# --------------------------------------------------------------------
activate () {
  local oversion="${_OVERSION}"
  local toolchain_root="${_EC_TOOLCHAIN_ROOT}"
  local toolchain_etc="${toolchain_root}/ocaml-${oversion}/etc/ocamlbrew.bashrc"

  if [ ! -z "${EC_TOOLCHAIN_ACTIVATED}" ]; then
    echo "An EasyCrypt toolchain has already been activated in this shell." >&2
    return
  fi

  if [ ! -e "${toolchain_etc}" ]; then
    cat <<__EOF__ >&2
Install the EasyCrypt toolchain (${oversion}) first ([make toolchain])

If you have a toolchain installed in a different version, you can
set the OVERSION environment variable to the right version.

You can find below the list of installed toolchains:

__EOF__

    echo '---------- START OF LISTING ----------' >&2
    [ -d "${toolchain_root}" ] && {
      ls -1 "${toolchain_root}" | grep '^ocaml-' | sed 's/ocaml-//';
    }
    echo '---------- END OF LISTING   ----------' >&2

    return
  fi

  . "${toolchain_etc}"

  export EC_TOOLCHAIN_ACTIVATED=1
}

# --------------------------------------------------------------------
activate

unset -f activate
unset _EC_SRC_ROOT
unset _EC_TOOLCHAIN_ROOT
unset _OVERSION
