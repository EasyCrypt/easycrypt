{ withProvers ? false, devDeps ? [] }:

with import <nixpkgs> {};

let provers =
  if withProvers then [
    alt-ergo
    z3
  ] else []; in

stdenv.mkDerivation {
  pname = "easycrypt";
  version = "git";
  src = ./.;

  buildInputs = [ git ] ++ (with ocamlPackages; [
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
    why3
    zarith
  ]);

  propagatedBuildInputs = [ why3 ]
    ++ devDeps
    ++ provers;

  installPhase = ''
    runHook preInstall
    dune install --prefix $out -p $pname
    runHook postInstall
  '';
}
