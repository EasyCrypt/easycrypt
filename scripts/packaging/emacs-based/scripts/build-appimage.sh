#! /bin/bash

# --------------------------------------------------------------------
umask 077

# --------------------------------------------------------------------
EMACS_U=https://github.com/probonopd/Emacs.AppImage/releases/download/AppImage/Emacs-25.1-glibc2.17-x86-64.AppImage
EMACS_L=Emacs-25.1-glibc2.17-x86-64.AppImage

# --------------------------------------------------------------------
BLD=_build-linux
PKG=package/easycrypt
APP=appimage

# --------------------------------------------------------------------
[ -e cache ] || mkdir cache

if [ ! -e ${BLD}/${PKG} ]; then
  echo "Build easycrypt (for linux) first" >&2
  exit 1
fi

if [ -e ${BLD}/${APP} ]; then
  echo "Delete ${BLD}/${APP} first." >&2
  exit 1
fi

# --------------------------------------------------------------------
set -ex

# --------------------------------------------------------------------
mkdir -p ${BLD}/${APP}/EasyCrypt
cp -r ${BLD}/${PKG}/. ${BLD}/${APP}/EasyCrypt
cp -r config/${APP}/* ${BLD}/${APP}/easycrypt/

# --------------------------------------------------------------------
if [ ! -e cache/${EMACS_L} ]; then
  wget -O cache/${EMACS_L} ${EMACS_U}
fi

cp cache/${EMACS_L} ${BLD}/${APP}/EasyCrypt/bin/Emacs.AppImage
chmod +x ${BLD}/${APP}/EasyCrypt/bin/Emacs.AppImage
chmod +x ${BLD}/${APP}/EasyCrypt/AppRun
