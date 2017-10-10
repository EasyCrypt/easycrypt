#! /bin/bash

# --------------------------------------------------------------------
umask 077

# --------------------------------------------------------------------
function patchrpath {
  patchelf/src/patchelf --set-rpath '$ORIGIN:$ORIGIN/../lib' "${1}"
}

# --------------------------------------------------------------------
BLD=_build-linux
PKG=package/easycrypt

if [ -e ${BLD} ]; then
  echo "Delete ${BLD} first." >&2
  exit 1
fi

mkdir ${BLD}; cd ${BLD}

# --------------------------------------------------------------------
set -ex

# --------------------------------------------------------------------
# Install patchrpath

git clone --depth=1 https://github.com/NixOS/patchelf.git

( set -e; cd patchelf; autoreconf -i -f && ./configure && make )

# --------------------------------------------------------------------
# Build OPAM

export OPAMROOT="${PWD}/_opam"
export OPAMJOBS=${OPAMJOBS:-2}
export OPAMYES=true
export OCAMLBUILD_JOBS=${OPAMJOBS}
export ECNAME=${ECNAME:-$(date +'%d-%m-%Y')}

opam init -n
eval `opam config env`
opam repository add easycrypt git://github.com/EasyCrypt/opam.git
opam update

# --------------------------------------------------------------------
# Build EasyCrypt

if [ -z "${ECBRANCH}" ]; then
  git clone --depth=1 https://github.com/EasyCrypt/easycrypt.git
else
  git clone -b "${ECBRANCH}" --depth=1 https://github.com/EasyCrypt/easycrypt.git
fi

opam install --deps-only easycrypt
make -C easycrypt

# --------------------------------------------------------------------
# Build provers

provers="alt-ergo eprover z3"

opam install ${provers}

# --------------------------------------------------------------------
# Create package

mkdir -p ${PKG}
mkdir -p ${PKG}/etc
mkdir -p ${PKG}/bin
mkdir -p ${PKG}/lib
mkdir -p ${PKG}/share

# --------------------------------------------------------------------
cp ../config/etc/* ${PKG}/etc/

# --------------------------------------------------------------------
mkdir -p ${PKG}/{lib,share}/easycrypt
mkdir -p ${PKG}/share/

cp easycrypt/ec.native ${PKG}/bin/easycrypt
cp easycrypt/system/callprover ${PKG}/bin/
cp -r easycrypt/theories ${PKG}/lib/easycrypt/

patchrpath ${PKG}/bin/easycrypt

# --------------------------------------------------------------------
mkdir -p ${PKG}/{lib,share}/why3

cp -r _opam/system/lib/why3/plugins ${PKG}/lib/why3/
cp -r _opam/system/lib/why3/why3-cpulimit ${PKG}/bin/
cp -r _opam/system/share/why3 ${PKG}/share/

# --------------------------------------------------------------------
for name in ${provers}; do
  cp _opam/system/bin/${name} ${PKG}/bin/
  patchrpath ${PKG}/bin/${name}
done

# --------------------------------------------------------------------
mkdir pg && ( set -e; cd pg; \
  git clone --depth=1 https://github.com/ProofGeneral/PG.git; \
  rm -rf PG/.git && make -C PG clean )

mkdir -p ${PKG}/share/easycrypt/pg
cp ../config/proofgeneral/emacs.rc ${PKG}/share/easycrypt/pg/
mv pg/PG ${PKG}/share/easycrypt/pg/ProofGeneral

# --------------------------------------------------------------------
cp ../config/scripts/run-easycrypt ${PKG}/

# --------------------------------------------------------------------
ldd ${PKG}/bin/* | fgrep '=>' | \
    egrep -w 'libgmp|libpcre' | awk '{print $3}' | sort -u | \
    xargs -r -I '{}' -- cp '{}' ${PKG}/lib/
