with import <nixpkgs> {};

let why3_for_ec = stdenv.lib.overrideDerivation why3 (o: {
  name = "why3-0.87.3";
  src = fetchurl {
    url = "https://gforge.inria.fr/frs/download.php/file/36398/why3-0.87.3.tar.gz";
    sha256 = "1fn9v6w1ilkrm2n4rz31w8qvjnchyvwxiqs67z3f59b5k99wb2ka";
  };
});
in

stdenv.mkDerivation {
  name = "easycrypt-1.0";
  src = ./.;
  buildInputs = [ ]
    ++ (with ocamlPackages; [ ocaml findlib ocamlbuild batteries menhir merlin zarith inifiles why3_for_ec ])
    ;
}
