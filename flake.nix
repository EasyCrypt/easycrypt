{
  inputs = {
    opam-nix.url = "github:tweag/opam-nix";

    flake-utils.url = "github:numtide/flake-utils";

    stable.url = "github:nixos/nixpkgs/24.05";
    nixpkgs.follows = "opam-nix/nixpkgs";

  };

  outputs = { self, flake-utils, opam-nix, nixpkgs, ... }@inputs:
    let package = "easycrypt"; in

    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};

        on = opam-nix.lib.${system};

        devPackagesQuery = {
          merlin = "*";
          ocaml-lsp-server = "*";
          ocamlformat = "*";
        };

        query = devPackagesQuery // {
          ocaml-base-compiler = "5.4.1";
        };

        scope = on.buildOpamProject' { } ./. query;

        overlay = final: prev: {
          ${package} = prev.${package}.overrideAttrs (oa: {
            nativeBuildInputs = oa.nativeBuildInputs
              ++ pkgs.lib.optionals pkgs.stdenv.isDarwin [ pkgs.darwin.sigtool ];
            postInstall = ''
              ln -s "$out/lib/ocaml/$opam__ocaml__version/site-lib/easycrypt" $out/lib/
            '';
            doNixSupport = false;
          });
          conf-pkg-config = prev.conf-pkg-config.overrideAttrs (oa: {
            nativeBuildInputs = oa.nativeBuildInputs ++ [pkgs.pkg-config];
          });
          conf-git = prev.conf-git.overrideAttrs (oa: {
            nativeBuildInputs = oa.nativeBuildInputs ++ [pkgs.git];
          });
          alt-ergo = prev.alt-ergo.overrideAttrs (oa: {
            nativeBuildInputs = oa.nativeBuildInputs
              ++ pkgs.lib.optionals pkgs.stdenv.isDarwin [ pkgs.darwin.sigtool ];
          });
        };

        scope' = scope.overrideScope overlay;

        # Packages from devPackagesQuery
        devPackages = builtins.attrValues
          (pkgs.lib.getAttrs (builtins.attrNames devPackagesQuery) scope');

        # The main package containing the executable
        main = pkgs.symlinkJoin {
          name = "main";
          paths = [ scope'.${package} scope'.why3 ];
        };

        mkAltErgo = version:
          ((on.queryToScope { } (query // { alt-ergo = version; })).overrideScope overlay).alt-ergo;
      in rec {
        legacyPackages = scope';

        packages = rec {
          z3 = pkgs.z3;
          cvc5 = pkgs.cvc5;
          altErgo = mkAltErgo "2.6.3";

          provers = pkgs.symlinkJoin {
            name = "provers";
            paths = [ altErgo z3 cvc5 ];
          };

          with_provers = pkgs.symlinkJoin {
            name = "with-provers";
            paths = [ main provers ];
          };

          default = main;
        };

        devShells.default = pkgs.mkShell {
          inputsFrom = [ scope'.easycrypt ];
          buildInputs =
              devPackages
           ++ [ pkgs.git scope'.why3 packages.provers ]
           ++ (with pkgs.python3Packages; [ pyyaml ]);
        };
      });
}
