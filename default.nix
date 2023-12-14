{ withProvers ? false, devDeps ? [] }:

with import <nixpkgs> {};

let provers =
  if withProvers then [
    alt-ergo
    cvc4
    cvc5
    z3
  ] else []; in

let why3-pin =
  why3.overrideAttrs (o : rec {
    version = "1.6.0";
    src = fetchurl {
      url = "https://why3.gitlabpages.inria.fr/releases/${o.pname}-${version}.tar.gz";
      sha256 = "sha256-hFvM6kHScaCtcHCc6Vezl9CR7BFbiKPoTEh7kj0ZJxw=";
    };
  });
in

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
    iter
    menhir
    menhirLib
    ppxlib
    ppx_deriving
    progress
    yojson
    zarith
  ]);

  propagatedBuildInputs = [ why3-pin ]
    ++ devDeps
    ++ provers;

  installPhase = ''
    runHook preInstall
    dune install --prefix $out -p $pname
    runHook postInstall
  '';
}
