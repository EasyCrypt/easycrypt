#! /bin/bash

# --------------------------------------------------------------------
umask 077

# --------------------------------------------------------------------
set -ex

# --------------------------------------------------------------------
[ ! -e _build ] || exit 1
mkdir _build && cd _build

# --------------------------------------------------------------------
# Build OPAM

export OPAMROOT="${PWD}/_opam"
export OPAMJOBS=2
export OCAMLBUILD_JOBS=${OPAMJOBS}

opam init -n
eval `opam config env`
opam repository add easycrypt git://github.com/EasyCrypt/opam.git
opam update

# --------------------------------------------------------------------
# Build EasyCrypt

git clone --depth=1 https://github.com/EasyCrypt/easycrypt.git

opam install -v -y ec-toolchain
make -C easycrypt

# --------------------------------------------------------------------
# Build provers

opam install -v -y alt-ergo eprover # ec-provers

# --------------------------------------------------------------------
# Create package

mkdir -p package/easycrypt
mkdir -p package/easycrypt/etc
mkdir -p package/easycrypt/bin
mkdir -p package/easycrypt/lib
mkdir -p package/easycrypt/share

# --------------------------------------------------------------------
cp ../config/etc/* package/easycrypt/etc/

# --------------------------------------------------------------------
mkdir -p package/easycrypt/{lib,share}/easycrypt
mkdir -p package/easycrypt/share/

cp easycrypt/ec.native package/easycrypt/bin/easycrypt
cp easycrypt/system/callprover package/easycrypt/bin/
cp -r easycrypt/theories package/easycrypt/lib/easycrypt/

## --------------------------------------------------------------------
mkdir -p package/easycrypt/{lib,share}/why3

cp -r _opam/system/lib/why3/plugins package/easycrypt/lib/why3/
cp -r _opam/system/lib/why3/why3-cpulimit package/easycrypt/bin/
cp -r _opam/system/share/why3 package/easycrypt/share/

# --------------------------------------------------------------------
provers="alt-ergo eprover"

for name in ${provers}; do
  cp _opam/system/bin/${name} package/easycrypt/bin/
done

# --------------------------------------------------------------------
for name in easycrypt ${provers}; do
  dlls=$(otool -L package/easycrypt/bin/${name} \
    | fgrep .dylib | fgrep -v '@executable_path' \
    | egrep libgmp | awk '{print $1}')
  for dll in ${dlls}; do
    cp "${dll}" package/easycrypt/lib
    chmod +w "package/easycrypt/lib/$(basename ${dll})"
    install_name_tool -change \
      "${dll}" "@executable_path/../lib/$(basename ${dll})" \
      package/easycrypt/bin/${name}
  done
done

# --------------------------------------------------------------------
ECV=24.5-1

mkdir emacs && ( set -e; cd emacs; \
  curl -LO http://emacsformacosx.com/emacs-builds/Emacs-${ECV}-universal.dmg;
  7z x Emacs-${ECV}-universal.dmg; 7z x 4.hfs;
  mv Emacs/Emacs.app ../package/easycrypt/share )

find package/easycrypt/share/Emacs.app/Contents/MacOS/Emacs \
    -type f -exec chmod +x '{}' ';'

# --------------------------------------------------------------------
PGV=4.2

mkdir pg && ( set -e; cd pg; \
  curl -LO http://proofgeneral.inf.ed.ac.uk/releases/ProofGeneral-${PGV}.tgz;
  gtar -xof ProofGeneral-${PGV}.tgz;
  make -C ProofGeneral-${PGV} clean )

make PGROOT="$(pwd)/pg/ProofGeneral-${PGV}" -C easycrypt/proofgeneral install

mkdir -p package/easycrypt/share/easycrypt/pg

cp ../config/proofgeneral/emacs.rc package/easycrypt/share/easycrypt/pg/
mv pg/ProofGeneral-${PGV} package/easycrypt/share/easycrypt/pg/ProofGeneral

# --------------------------------------------------------------------
cp ../config/scripts/run-easycrypt package/easycrypt/

# --------------------------------------------------------------------
BZIP2=-9 gtar -C package --owner=0 --group=0 -cjf \
    easycrypt-$(date +'%d-%m-%Y').tbz2 easycrypt
