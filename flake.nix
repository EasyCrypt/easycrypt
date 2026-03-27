{
  nixConfig = {
    extra-substituters = [
      "https://easycrypt.cachix.org"
    ];
    extra-trusted-public-keys = [
      "easycrypt.cachix.org-1:d0hAur+ZAUIM7rAi1TlG2ZCra6AXS50CggshQcT6f7g="
    ];
  };
  inputs = {
    opam-nix.url = "github:tweag/opam-nix";

    flake-utils.url = "github:numtide/flake-utils";
    treefmt-nix.url = "github:numtide/treefmt-nix";

    nixpkgs.follows = "opam-nix/nixpkgs";
    emacs-overlay.url = "github:nix-community/emacs-overlay";

    prover_cvc4_1_8 = {
      url = "github:CVC4/CVC4-archived/1.8";
      flake = false;
    };

    prover_cvc5_1_3_0 = {
      url = "github:cvc5/cvc5/cvc5-1.3.0";
      flake = false;
    };

    prover_z3_4_14_1 = {
      url = "github:z3prover/z3/z3-4.14.1";
      flake = false;
    };
  };

  outputs = {
    flake-utils,
    opam-nix,
    nixpkgs,
    emacs-overlay,
    treefmt-nix,
    ...
  } @ inputs: let
    package = "easycrypt";
  in
    flake-utils.lib.eachDefaultSystem (
      system: let
        overlays = [(import emacs-overlay)];
        pkgs = import nixpkgs {inherit system overlays;};
        treefmtEval = treefmt-nix.lib.evalModule pkgs {
          projectRootFile = "flake.nix";

          # Enable formatters
          programs.alejandra.enable = true;
          # programs.ocamlformat.enable = true; # TODO: Enable when we have a repo .ocamlformat

          # Add any extra formatters here (for MD, docs, whatever)
        };

        on = opam-nix.lib.${system};

        devPackagesQuery = {
          merlin = "*";
          ocaml-lsp-server = "*";
          ocamlformat = "*";
        };

        query =
          devPackagesQuery
          // {
            ocaml-base-compiler = "5.3.0";
          };

        opamSource = pkgs.lib.cleanSourceWith {
          src = ./.;
          filter = path: type:
            type
            == "directory"
            || pkgs.lib.strings.hasSuffix ".opam" path
            || builtins.baseNameOf path == "dune-project"
            || builtins.baseNameOf path == "dune";
        };

        scope = on.buildOpamProject' {} opamSource query;

        overlay = _final: prev: {
          ${package} = prev.${package}.overrideAttrs (oa: {
            src = pkgs.lib.cleanSource ./.;
            nativeBuildInputs =
              oa.nativeBuildInputs ++ pkgs.lib.optionals pkgs.stdenv.isDarwin [pkgs.darwin.sigtool];
            postInstall = ''
              ln -s "$out/lib/ocaml/$opam__ocaml__version/site-lib/easycrypt" $out/lib/
            '';
            doNixSupport = false;
          });
          conf-zlib = prev.conf-zlib.overrideAttrs (
            _finalAttrs: prevAttrs: {
              nativeBuildInputs = prevAttrs.nativeBuildInputs ++ (with pkgs; [pkg-config]);
            }
          );
          conf-git = prev.conf-git.overrideAttrs (
            _finalAttrs: prevAttrs: {
              nativeBuildInputs = prevAttrs.nativeBuildInputs ++ (with pkgs; [git]);
              buildInputs = prevAttrs.buildInputs ++ (with pkgs; [git]);
            }
          );
          alt-ergo = prev.alt-ergo.overrideAttrs (
            _finalAttrs: prevAttrs: {
              nativeBuildInputs = prevAttrs.nativeBuildInputs ++ (with pkgs; [darwin.sigtool]);
            }
          );
        };

        scope' = scope.overrideScope overlay;

        # Packages from devPackagesQuery
        devPackages = builtins.attrValues (pkgs.lib.getAttrs (builtins.attrNames devPackagesQuery) scope');

        # The main package containing the executable
        main = pkgs.symlinkJoin {
          name = "main";
          paths = [
            scope'.${package}
            scope'.why3
          ];
        };

        # Create provers packages
        mkProverPackage = pkg: version:
          pkgs.${pkg}.overrideAttrs (_: {
            inherit version;
            src = inputs."${"prover_" + pkg + "_" + builtins.replaceStrings ["."] ["_"] version}";
          });

        mkAltErgo = version: (on.queryToScope {} (query // {alt-ergo = version;})).alt-ergo;

        devTools = with pkgs;
          [
            (emacsWithPackagesFromUsePackage {
              config = ''(setq easycrypt-prog-name "ec.native")'';
              defaultInitFile = true;
              alwaysEnsure = true;
              package = pkgs.emacs;
              extraEmacsPackages = epkgs: [epkgs.proof-general];
            })
            bashInteractive
            git
            difftastic
          ]
          ++ lib.optionals (!stdenv.isDarwin) [perf-tools];

        ecShell = "${pkgs.bashInteractive + "/bin/bash"}";
        ecShellHook = ''
          export SHELL=${ecShell}
          export PATH=$PATH:`realpath .`
        '';
      in rec {
        legacyPackages = scope';

        packages = rec {
          z3 = mkProverPackage "z3" "4.14.1";
          cvc4 = mkProverPackage "cvc4" "1.8";
          cvc5 = mkProverPackage "cvc5" "1.3.0";
          altErgo = mkAltErgo "2.4.2";

          provers = pkgs.symlinkJoin {
            name = "provers";
            paths =
              [
                altErgo
                z3
                cvc5
              ]
              ++ (pkgs.lib.optionals (!pkgs.stdenv.isDarwin) [cvc4]); # Cvc4 build is broken in MacOS
          };

          with_provers = pkgs.symlinkJoin {
            name = "with-provers";
            paths = [
              main
              provers
            ];
          };

          default = main;
        };

        devShells.barebones = pkgs.mkShell {
          inputsFrom = [scope'.easycrypt];
          buildInputs = devPackages ++ [scope'.why3] ++ (with pkgs.python3Packages; [pyyaml]);
        };

        devShells.noProvers = pkgs.mkShell {
          inputsFrom = [
            scope'.easycrypt
            devShells.barebones
          ];
          buildInputs = devTools;
          SHELL = ecShell;
          shellHook = ecShellHook;
        };

        devShells.withDevTools = pkgs.mkShell {
          inputsFrom = [
            scope'.easycrypt
            devShells.noProvers
          ];
          buildInputs = [packages.provers];
          SHELL = ecShell;
          shellHook = ecShellHook;
        };

        formatter = treefmtEval.config.build.wrapper;
      }
    );
}
