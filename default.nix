{ withProvers ? false, devDeps ? [] }:

with import <nixpkgs> {};

let provers =
  if withProvers then [
    alt-ergo
    cvc4
    cvc5
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
    cmdliner
    dune_3
    dune-build-info
    dune-site
    hex
    inifiles
    iter
    menhir
    menhirLib
    ppxlib
    ppx_deriving
    ppx_deriving_yojson
    progress
    yojson
    why3
    zarith
  ]);

  propagatedBuildInputs = devDeps ++ provers;

  installPhase = ''
    runHook preInstall
    dune install --prefix $out -p $pname
    runHook postInstall
  '';
}
