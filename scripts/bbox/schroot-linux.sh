#! /bin/bash

# --------------------------------------------------------------------
function usage {
  echo "Usage: $0 [linux32|linux64]" >&2
}

# --------------------------------------------------------------------
if [ $# -ne 1 ]; then usage; exit 1; fi

case $1 in
    linux32)
	NAME=linux32
	FLAVOR=i386
	;;
    linux64)
	NAME=linux64
	FLAVOR=amd64
	;;
    *)
	usage; exit 1
esac

JOBS=2
SRVROOT=/srv/schroot/${NAME}
MIRROR=http://ftp.fr.debian.org/debian/

# --------------------------------------------------------------------
schroot="schroot -d /root -c ${NAME} --"
opam="opam config --root=/opt/ocaml exec -- env OPAMJOBS=${JOBS}"

# --------------------------------------------------------------------
set -ex

[ -e /etc/schroot/chroot.d/$NAME.conf ] || \
  install -v -m 0644 -o root -g root chroot.d/${NAME}.conf /etc/schroot/chroot.d/

cdebootstrap --arch ${FLAVOR} stable ${SRVROOT} ${MIRROR}
 
${schroot} apt-get update
${schroot} apt-get install -y zsh

install -v -m 0644 -o root -g root -t ${SRVROOT}/etc/zsh/ /etc/zsh/z*
install -v -m 0644 -o root -g root /etc/DIR_COLORS ${SRVROOT}/etc/

install -v -m 0600 -o root -g root apt-sources/ocaml-debian-7.key ${SRVROOT}/root/
install -v -m 0644 -o root -g root apt-sources/ocaml.list ${SRVROOT}/etc/apt/sources.list.d/
 
${schroot} apt-key add ocaml-debian-7.key
${schroot} apt-get update
${schroot} apt-get install -y build-essential m4 git ocaml opam
${schroot} apt-get clean
${schroot} opam init --root=/opt/ocaml --no-setup
${schroot} ${opam} opam repository add ec https://ci.easycrypt.info/opam-1.2.0
${schroot} ${opam} opam install -v -y ec-toolchain
${schroot} git clone git://ci.easycrypt.info/easycrypt.git
${schroot} ${opam} make -C easycrypt
