{ withProvers ? false, devDeps ? [] }:

with import <nixpkgs> {};

let alt-ergo-pin = callPackage scripts/nix/alt-ergo/default.nix { nixpkgs = <nixpkgs>; };
in

let cvc4-pin = callPackage scripts/nix/cvc4/default.nix { nixpkgs = <nixpkgs>; };
in

let cvc5-pin = callPackage scripts/nix/cvc5/default.nix { nixpkgs = <nixpkgs>; };
in

let z3-pin = callPackage scripts/nix/z3/default.nix { nixpkgs = <nixpkgs>; };
in

let provers =
  if withProvers then [
    cvc4-pin
    cvc5-pin
    z3-pin
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
    menhir
    menhirLib
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
