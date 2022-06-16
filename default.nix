with import <nixpkgs> {};

if !lib.versionAtLeast why3.version "1.4" then
  throw "please update your nixpkgs channel: nix-channel --update"
else
let why3_local =
  if !lib.versionOlder why3.version "1.5" then
  why3.overrideAttrs (o: rec {
    version = "1.4.1";
    src = fetchurl {
      url = "https://why3.gitlabpages.inria.fr/releases/${o.pname}-${version}.tar.gz";
      sha256 = "sha256:1rqyypzlvagrn43ykl0c5wxyvnry5fl1ykn3xcvlzgghk96yq3jq";
    };
  })
  else why3
; in
let why3 = why3_local; in
  stdenv.mkDerivation {
    name = "easycrypt-1.0";
    src = ./.;
    buildInputs = [ why3 ] ++ (with ocamlPackages; [
      ocaml
      findlib
      batteries
      dune_2
      dune-build-info
      dune-site
      inifiles
      menhir
      menhirLib
      merlin
      yojson
      zarith
    ]);
    installFlags = [ "PREFIX=$(out)" ];
  }
