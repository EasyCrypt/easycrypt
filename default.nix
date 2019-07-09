with import <nixpkgs> {};

stdenv.mkDerivation {
  name = "easycrypt-1.0";
  src = ./.;
  buildInputs = [ ]
    ++ (with ocamlPackages; [ ocaml findlib ocamlbuild batteries menhir merlin zarith inifiles why3 ])
    ;
}
