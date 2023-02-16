with import <nixpkgs> {};

if !lib.versionAtLeast why3.version "1.4" then
  throw "please update your nixpkgs channel: nix-channel --update"
else
let why3_local =
  if !lib.versionAtLeast why3.version "1.5" then
  why3.overrideAttrs (o: rec {
    version = "1.5.0";
    src = fetchurl {
      url = "https://why3.gitlabpages.inria.fr/releases/${o.pname}-${version}.tar.gz";
      sha256 = "sha256:0qjh49pyqmg3xi09fn4lyzz23i6h18y9sgc8ayscvx3bwr3vcqhr";
    };
  })
  else why3
; in
let why3 = why3_local; in

let merlin = 
    ocamlPackages.merlin.overrideAttrs (o: {
    doCheck = false;
    }); in

  stdenv.mkDerivation {
    name = "easycrypt-1.0";
    src = ./.;
    buildInputs = [ why3 merlin] ++ (with ocamlPackages; [
      ocaml
      findlib
      batteries
      camlp-streams
      dune_3
      dune-build-info
      dune-site
      inifiles
      menhir
      menhirLib
      yojson
      zarith
    ]);
    installFlags = [ "PREFIX=$(out)" ];
  }
