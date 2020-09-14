with import <nixpkgs> {};

let why3_1_2 = why3.overrideAttrs (o: {
  name = "why3-1.2.1";
  src = fetchurl {
    url = "https://gforge.inria.fr/frs/download.php/file/38185/why3-1.2.1.tar.gz";
    sha256 = "014gkwisjp05x3342zxkryb729p02ngx1hcjjsrplpa53jzgz647";
  };
  patches = [
    # Compatibility with js_of_ocaml 3.5
    (fetchpatch {
      url = "https://gitlab.inria.fr/why3/why3/commit/269ab313382fe3e64ef224813937314748bf7cf0.diff";
      sha256 = "0i92wdnbh8pihvl93ac0ma1m5g95jgqqqj4kw6qqvbbjjqdgvzwa";
    })
  ];
}); in

stdenv.mkDerivation {
  name = "easycrypt-1.0";
  src = ./.;
  buildInputs = [ ]
    ++ (with ocamlPackages; [ ocaml findlib ocamlbuild (batteries.overrideAttrs (o: { doCheck = false; })) menhir merlin zarith inifiles why3_1_2 yojson])
    ;
  installFlags = [ "PREFIX=$(out)" ];
}
