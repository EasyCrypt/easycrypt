with import <nixpkgs> {};

let 
alt-ergo = (import (pkgs.fetchzip {
    url = "https://github.com/nixos/nixpkgs/archive/7138a338b58713e0dea22ddab6a6785abec7376a.zip";
    # Please update this hash with the one nix says on the first build attempt
    sha256 = "1asgl1hxj2bgrxdixp3yigp7xn25m37azwkf3ppb248vcfc5kil3";
  }) { }).alt-ergo;
  in 

stdenv.mkDerivation {
  name = "easycrypt-1.0";
  src = ./.;
  buildInputs = [ ]
    ++ (with alt-ergo; [alt-ergo])
    ++ (with ocamlPackages; [ ocaml findlib ocamlbuild (batteries.overrideAttrs (o: { doCheck = false; })) menhir merlin zarith inifiles why3 yojson])
    ;
  installFlags = [ "PREFIX=$(out)" ];
}
