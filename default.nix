with import <nixpkgs> {};

if !lib.versionAtLeast why3.version "1.4" then
  throw "please update your nixpkgs channel: nix-channel --update"
else
  stdenv.mkDerivation {
    pname = "easycrypt";
    version = "local";

    src = ./.;

    buildInputs = [ git why3 ] ++ (with ocamlPackages; [
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
