with import <nixpkgs> {};

stdenv.mkDerivation {
  name = "easycrypt-1.0";
  src = ./.;
  buildInputs = [ ]
    ++ (with ocamlPackages; [ ocaml findlib ocamlbuild (batteries.overrideAttrs (o: { doCheck = false; })) menhir merlin zarith inifiles why3 yojson])
    ;
  installFlags = [ "PREFIX=$(out)" ];
}
