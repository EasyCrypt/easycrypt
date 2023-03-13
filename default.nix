{ withProvers ? false, devDeps ? [] }:

with import <nixpkgs> {};

let why3_local =
  why3.overrideAttrs (o : rec {
    version = "1.5.1";
    src = fetchurl {
      url = "https://why3.gitlabpages.inria.fr/releases/${o.pname}-${version}.tar.gz";
      sha256 = "sha256-vNR7WeiSvg+763GcovoZBFDfncekJMeqNegP4fVw06I=";
    };
  });
in
let why3 = why3_local; in

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
