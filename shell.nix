{ withProvers ? true, devDeps ? [] }:

with import <nixpkgs> {};

let ec = callPackage ./default.nix { inherit withProvers devDeps; };
in

pkgs.mkShell {
  buildInputs = ec.buildInputs
  ++ ec.propagatedBuildInputs
  ++ (with python3Packages; [
    pyyaml
  ]);
}
