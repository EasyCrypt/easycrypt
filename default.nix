with import <nixpkgs> {};

let why3_for_ec = stdenv.lib.overrideDerivation why3 (o: {
  name = "why3-0.87.3";
  src = fetchurl {
    url = "https://gforge.inria.fr/frs/download.php/file/36398/why3-0.87.3.tar.gz";
    sha256 = "1fn9v6w1ilkrm2n4rz31w8qvjnchyvwxiqs67z3f59b5k99wb2ka";
  };
  buildInputs = (with ocaml-ng.ocamlPackages_4_04; [
    ocaml findlib lablgtk ocamlgraph zarith menhir ]) ++
    stdenv.lib.optionals (ocamlPackages.ocaml == coq.ocaml ) [
      coq coq.camlp5
    ];
});
in

stdenv.mkDerivation rec {
  name = "easycrypt-${version}";
  version = "1.0";
  src = ./.;
  buildInputs = [ z3 alt-ergo ]
  ++ (with ocaml-ng.ocamlPackages_4_04; [ ocaml findlib ocamlbuild batteries menhir merlin zarith inifiles why3_for_ec ])
  ++ (with python27Packages; [ python pyyaml ]);
  makeFlags = [ "PREFIX=$(out)" ];
  preBuild = ''
    patchShebangs scripts/install
    patchShebangs scripts/testing
    patchShebangs scripts/packaging/emacs-based/scripts
    patchShebangs scripts/docker/test-box/hooks/build
  '';
}
