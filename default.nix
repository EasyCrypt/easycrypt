with import <nixpkgs> {};

if !lib.versionAtLeast why3.version "1.4" then
  throw "please update your nixpkgs channel: nix-channel --update"
else
stdenv.mkDerivation {
  name = "easycrypt-1.0";
  src = ./.;
  buildInputs = [ why3 ]
    ++ (with ocamlPackages; [ ocaml findlib ocamlbuild batteries menhir menhirLib merlin zarith inifiles yojson elpi])
    ;
  installFlags = [ "PREFIX=$(out)" ];
}
