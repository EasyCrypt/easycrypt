#! /bin/bash

# --------------------------------------------------------------------
umask 077

# --------------------------------------------------------------------
BLD=_build-macos
PKG=package/easycrypt
APP=EasyCrypt.app

if [ -e ${BLD} ]; then
  echo "Delete ${BLD} first." >&2
  exit 1
fi

mkdir ${BLD}; cd ${BLD}

# --------------------------------------------------------------------
set -ex

# --------------------------------------------------------------------
# Build OPAM

export OPAMROOT="${PWD}/_opam"
export OPAMJOBS=2
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

# --------------------------------------------------------------------
mkdir -p ${PKG}/{lib,share}/why3

cp -r _opam/system/lib/why3/plugins ${PKG}/lib/why3/
cp -r _opam/system/lib/why3/why3-cpulimit ${PKG}/bin/
cp -r _opam/system/share/why3 ${PKG}/share/

# --------------------------------------------------------------------
for name in ${provers}; do
  cp _opam/system/bin/${name} ${PKG}/bin/
done

# --------------------------------------------------------------------
for name in easycrypt ${provers}; do
  dlls=$(otool -L ${PKG}/bin/${name} \
    | fgrep .dylib | fgrep -v '@executable_path' \
    | egrep 'libgmp|libpcre' | awk '{print $1}')
  for dll in ${dlls}; do
    cp "${dll}" ${PKG}/lib
    chmod +w "${PKG}/lib/$(basename ${dll})"
    install_name_tool -change \
      "${dll}" "@executable_path/../lib/$(basename ${dll})" \
      ${PKG}/bin/${name}
  done
done

# --------------------------------------------------------------------
ECV=25.1

mkdir emacs && ( set -e; cd emacs; \
  curl -LO http://emacsformacosx.com/emacs-builds/Emacs-${ECV}-universal.dmg;
  7z x Emacs-${ECV}-universal.dmg || true;
  mv Emacs/Emacs.app ../${PKG}/share )

chmod +x package/easycrypt/share/Emacs.app/Contents/MacOS/Emacs*

# --------------------------------------------------------------------
mkdir pg && ( set -e; cd pg; \
  git clone --depth=1 https://github.com/ProofGeneral/PG.git; \
  rm -rf PG/.git && make -C PG clean )

mkdir -p ${PKG}/share/easycrypt/pg
cp ../config/proofgeneral/emacs.rc ${PKG}/share/easycrypt/pg/
mv pg/PG ${PKG}/share/easycrypt/pg/ProofGeneral

# --------------------------------------------------------------------
rm -rf ${APP}

mkdir -p ${APP}/Contents
mkdir -p ${APP}/Contents/{MacOS,Resources}

cp -r ${PKG}/. ${APP}/Contents/Resources
cp ../config/icons/easycrypt.icns ${APP}/Contents/Resources

cat >${APP}/Contents/Info.plist <<EOF
<?xml version="1.0" encoding="UTF-8"?>
<!DOCTYPE plist PUBLIC "-//Apple//DTD PLIST 1.0//EN" "http://www.apple.com/DTDs/PropertyList-1.0.dtd">
<plist version="1.0">
  <dict>
    <key>CFBundleExecutable</key>
    <string>easycrypt</string>
    <key>CFBundleGetInfoString</key>
    <string>EasyCrypt</string>
    <key>CFBundleIconFile</key>
    <string>easycrypt</string>
    <key>CFBundleName</key>
    <string>EasyCrypt</string>
    <key>CFBundlePackageType</key>
    <string>APPL</string>
    <key>CFBundleSignature</key>
    <string>4242</string>
  </dict>
</plist>
EOF

cat >${APP}/Contents/MacOS/easycrypt <<EOF
#! /usr/bin/python

# --------------------------------------------------------------------
import sys, os

# --------------------------------------------------------------------
def _main():
    mydir = os.path.dirname(__file__)
    mydir = os.path.join(*[mydir, '../Resources'])
    mydir = os.path.realpath(mydir)

    def resource(x):
        return os.path.join(*([mydir] + x.split('/')))

    emacs = resource('share/Emacs.app/Contents/MacOS/Emacs')
    args  = []

    args.extend(['-l', resource('share/easycrypt/pg/ProofGeneral/generic/proof-site.el')])
    args.extend(['-l', resource('share/easycrypt/pg/emacs.rc')])
    args.extend(['--no-init-file', '--no-site-file', '--debug-init'])

    os.chdir(mydir)
    os.putenv('PATH', '%s%s%s' % (os.path.join(mydir, 'bin'), \\
                                  os.pathsep, \\
                                  os.environ.get('PATH', '')))    
    os.execvp(emacs, [emacs] + args)

# --------------------------------------------------------------------
if __name__ == '__main__':
    _main()
EOF

chmod +x ${APP}/Contents/MacOS/easycrypt
