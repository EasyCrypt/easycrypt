#! /bin/sh

set -e

# --------------------------------------------------------------------
msg () { echo $* >&2; }

# --------------------------------------------------------------------
[ $# -eq 2 ] || exit 1

pname="$1"; mode="$2"

# --------------------------------------------------------------------
OVERSION=4.02.1

# --------------------------------------------------------------------
msg "Installing dependencies from Ubuntu packages."

sudo apt-get update
sudo DEBIAN_FRONTEND=noninteractive apt-get upgrade
sudo DEBIAN_FRONTEND=noninteractive apt-get install \
  -yy git m4 opam libgmp-dev libpcre3-dev pkg-config emacs24
apt-get clean

# --------------------------------------------------------------------
msg "Initializing opam."

opam init -a --compiler="${OVERSION}"
eval `opam config env`

opam repository add easycrypt git://github.com/EasyCrypt/opam.git
opam update

# --------------------------------------------------------------------
msg "Installing EasyCrypt and dependencies from OPAM packages."

opam install ec-toolchain
opam install ec-toolchain ec-provers
why3 config --detect

# --------------------------------------------------------------------
if [ ! -e ~/.emacs.rc ]; then mkdir ~/.emacs.rc; fi

cat >~/.emacs.rc/emacs-pkg-install.el <<EOF
(require 'package)
(package-initialize)

(add-to-list 'package-archives
             '("melpa" . "http://melpa.milkbox.net/packages/") t)

(setq url-http-attempt-keepalives nil)
(package-refresh-contents)
(package-install pkg-to-install)
EOF

einstall () {
  emacs --batch --eval "(defconst pkg-to-install '${1})" \
        -l ~/.emacs.rc/emacs-pkg-install.el
}

# --------------------------------------------------------------------
if [ "$mode" = "cloned" ]; then
  msg "Installing EasyCrypt from opam."

  opam install -y easycrypt ec-proofgeneral

  einstall opam

  cat >~/.emacs <<EOF
;; Disable eletric indent
(when (fboundp 'electric-indent-mode) (electric-indent-mode -1))
  (setq proof-output-tooltips nil)

;; MELPA
(require 'package)
(package-initialize)

(add-to-list 'package-archives
             '("melpa" . "http://melpa.milkbox.net/packages/") t)

;; Opam
(require 'opam)
(opam-init)

;; ProofGeneral
(setq proof-output-tooltips nil)
(load-file "~/.opam/${OVERSION}/share/ec-proofgeneral/generic/proof-site.el")
EOF

  msg "Your vagrant box is ready to be exported."
fi

# --------------------------------------------------------------------
if [ "$mode" = "shared" ]; then
  msg "Building EasyCrypt from shared directory."

  make -C "${pname}"
  make -C "${pname}/proofgeneral" local

  msg "You can now use your vagrant/easycryptxbox by typing:"
  msg ">> vagrant ssh -- -X -- make -C easycrypt pg"
fi
