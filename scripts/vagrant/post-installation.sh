#! /bin/sh

set -e

# --------------------------------------------------------------------
msg () { echo $* >&2; }

# --------------------------------------------------------------------
pname="$1"

# --------------------------------------------------------------------
msg "Installing dependencies from Ubuntu packages."

sudo DEBIAN_FRONTEND=noninteractive apt-get install \
  -qq -yy m4 opam libgmp-dev libpcre3-dev pkg-config emacs24

# --------------------------------------------------------------------
msg "Initializing opam."

opam init -q -a --compiler=4.02.1
eval `opam config env`

opam repository add easycrypt git://github.com/EasyCrypt/opam.git
opam update

# --------------------------------------------------------------------
msg "Installing EasyCrypt and dependencies from OPAM packages."

opam install easycrypt ec-provers ec-proofgeneral
why3 config --detect
cat >/home/vagrant/.emacs <<EOF
(when (fboundp 'electric-indent-mode) (electric-indent-mode -1))
  (setq proof-output-tooltips nil)
(load-file "~/.opam/4.02.1/share/ec-proofgeneral/generic/proof-site.el")
EOF

# # --------------------------------------------------------------------
# msg "Installing EasyCrypt dependencies from OPAM packages."
# 
# opam install -q -y ec-toolchain ec-provers
# why3 config --detect
# 
# # --------------------------------------------------------------------
# msg "Building EasyCrypt."
# 
# make -C "${pname}"
# make -C "${pname}/proofgeneral" local

# --------------------------------------------------------------------
msg "Now use vagrant ssh -- -X and make pg"
