{ withProvers ? false, devDeps ? [] }:

with import <nixpkgs> {};

let alt-ergo-pin =
  alt-ergo.overrideAttrs (o : rec {
    version = "2.4.2";
    src = fetchFromGitHub {
      owner = "OCamlPro";
      repo = "alt-ergo";
      rev = version;
      hash = "sha256-8pJ/1UAbheQaLFs5Uubmmf5D0oFJiPxF6e2WTZgRyAc=";
    };
  });
in

let cvc4-pin = cvc4; in

let z3-pin = z3_4_12; in

let provers =
  if withProvers then [
    alt-ergo-pin
    cvc4-pin
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
