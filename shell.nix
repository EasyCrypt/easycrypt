{ withProvers ? true, devDeps ? [] }:

with import <nixpkgs> {};

let provers =
  if withProvers then [
    alt-ergo
    z3
  ] else []; in

pkgs.mkShell {
  buildInputs = devDeps ++ [ git ] ++ (with ocamlPackages; [
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
    merlin
    yojson
    why3
    zarith
  ]) ++ (with python3Packages; [
    pyyaml
  ]);
}
