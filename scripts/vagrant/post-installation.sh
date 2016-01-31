#! /bin/sh

set -e

# --------------------------------------------------------------------
msg () { echo $* >&2; }

# --------------------------------------------------------------------
[ $# -eq 2 ] || exit 1

pname="$1"; mode="$2"

# --------------------------------------------------------------------
msg "Installing dependencies from Ubuntu packages."

sudo DEBIAN_FRONTEND=noninteractive apt-get install \
  -yy git m4 opam libgmp-dev libpcre3-dev pkg-config emacs24

# --------------------------------------------------------------------
msg "Initializing opam."

opam init -a --compiler=4.02.1
eval `opam config env`

opam repository add easycrypt git://github.com/EasyCrypt/opam.git
opam update

# --------------------------------------------------------------------
msg "Installing EasyCrypt and dependencies from OPAM packages."

opam install ec-toolchain ec-provers
why3 config --detect

# --------------------------------------------------------------------
if [ "$mode" = "cloned" ]; then
  msg "Installing EasyCrypt from opam."

  opam install -q -y easycrypt ec-proofgeneral

  cat >/home/easycrypt/.emacs <<EOF
(when (fboundp 'electric-indent-mode) (electric-indent-mode -1))
  (setq proof-output-tooltips nil)
(load-file "~/.opam/4.02.1/share/ec-proofgeneral/generic/proof-site.el")
EOF

  msg "Your vagrant box is ready to be exported."
fi

# --------------------------------------------------------------------
if [ "$mode" = "shared" ]; then
  msg "Building EasyCrypt from shared directory."

  make -C "${pname}"
  make -C "${pname}/proofgeneral" local

  msg "Now use vagrant ssh -- -X and make pg"
fi
