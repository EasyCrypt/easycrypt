with import <nixpkgs> {};

let why314 = why3.overrideAttrs (x:
   { name = "why3.14";
     src = fetchurl {
       url = "https://gforge.inria.fr/frs/download.php/file/38425/why3-1.4.0.tar.gz";
       sha256 = "0lw0cpx347zz9vvwqibmbxgs80fsd16scgk3isscvwxnajpc3rv8";
      };
     postPatch = "";
   }); in

stdenv.mkDerivation {
  name = "easycrypt-1.0";
  src = ./.;
  buildInputs = [ ]
    ++ (with ocamlPackages; [ ocaml findlib ocamlbuild (batteries.overrideAttrs (o: { doCheck = false; })) menhir merlin zarith inifiles why314 yojson])
    ;
  installFlags = [ "PREFIX=$(out)" ];
}
