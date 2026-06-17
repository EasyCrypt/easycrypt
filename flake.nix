{
  inputs = {
    opam-nix.url = "github:tweag/opam-nix";

    flake-utils.url = "github:numtide/flake-utils";

    nixpkgs.url = "github:nixos/nixpkgs/24.05";
    stable.url = "github:nixos/nixpkgs/24.05";
    nixpkgs.follows = "opam-nix/nixpkgs";

    prover_cvc4_1_8 = {
      url = "github:CVC4/CVC4-archived/1.8";
      flake = false;
    };

    prover_cvc5_1_0_9 = {
      url = "github:cvc5/cvc5/cvc5-1.0.9";
      flake = false;
    };

    prover_z3_4_12_6 = {
      url = "github:z3prover/z3/z3-4.12.6";
      flake = false;
    };
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
          ocaml-base-compiler = "4.14.2";
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

        # Create provers packages
        mkProverPackage = pkg: version:
          pkgs.${pkg}.overrideAttrs (_: {
            inherit version;
            src = inputs."${"prover_" + pkg + "_" + builtins.replaceStrings ["."] ["_"] version}";
          });

        mkAltErgo = version:
          ((on.queryToScope { } (query // { alt-ergo = version; })).overrideScope overlay).alt-ergo;
      in rec {
        legacyPackages = scope';

        packages = rec {
          z3 = mkProverPackage "z3" "4.12.6";
          cvc4 = mkProverPackage "cvc4" "1.8";
          cvc5 = mkProverPackage "cvc5" "1.0.9";
          altErgo = mkAltErgo "2.4.3";

          provers = pkgs.symlinkJoin {
            name = "provers";
            paths = [ altErgo z3 cvc4 cvc5 ];
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
