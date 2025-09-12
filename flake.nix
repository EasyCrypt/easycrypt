{
  inputs = {
    opam-nix.url = "github:tweag/opam-nix";

    flake-utils.url = "github:numtide/flake-utils";

    nixpkgs.url = "github:nixos/nixpkgs/release-24.11";
    stable.url = "github:nixos/nixpkgs/release-24.11";
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
          ocaml-base-compiler = "4.14.1";
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
	  conf-zlib = prev.conf-zlib.overrideAttrs (finalAttrs: prevAttrs: rec {
            nativeBuildInputs = prevAttrs.nativeBuildInputs 
              ++ (with pkgs; [ pkg-config ]);
          });
          conf-git = prev.conf-git.overrideAttrs (finalAttrs: prevAttrs: rec {
            nativeBuildInputs = prevAttrs.nativeBuildInputs
              ++ (with pkgs; [ git ]);
            buildInputs = prevAttrs.buildInputs
              ++ (with pkgs; [ git ]);
          });
          alt-ergo = prev.alt-ergo.overrideAttrs (finalAttrs: prevAttrs: rec {
            nativeBuildInputs = prevAttrs.nativeBuildInputs
            ++ (with pkgs; [ darwin.sigtool ]);
          });
	  frama-c = prev.frama-c.overrideAttrs (finalAttrs: prevAttrs: rec {
	    configureFlags = (prevAttrs.configureFlags or []) ++  ["--prefix=${prev.frama-c}/lib"];
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

        mkAltErgo = version: (on.queryToScope { } (query // { alt-ergo = version; })).alt-ergo;

        devTools = 
	  (let 
	    overlays = [ (import inputs.emacs-overlay) ];
	    pkgs = import nixpkgs {
	      inherit system overlays;
	    };
	  in
	    (with pkgs; [
	      (emacsWithPackagesFromUsePackage {
		config = ''(setq easycrypt-prog-name "ec.native")'';
		defaultInitFile = true;
		alwaysEnsure = true;
		package = pkgs.emacs;
		extraEmacsPackages = epkgs: [ epkgs.proof-general ];
	      })
	      bashInteractive
	      git 
	      difftastic
	    ])
	    ++
	    pkgs.lib.optionals (!pkgs.stdenv.isDarwin) [ pkgs.pperf-tools ]
	);
      in rec {
        legacyPackages = scope';

        packages = rec {
          z3 = mkProverPackage "z3" "4.14.1";
          cvc4 = mkProverPackage "cvc4" "1.8";
          cvc5 = mkProverPackage "cvc5" "1.3.0";
          altErgo = mkAltErgo "2.4.2";

          provers = pkgs.symlinkJoin {
            name = "provers";
            paths = [ 
	    #  altErgo 
	      z3 
	    #  cvc4 
	      cvc5 
	    ];
          };

          with_provers = pkgs.symlinkJoin {
            name = "with-provers";
            paths = [ main provers ];
          };

          default = main;
        };

        devShells.barebones = pkgs.mkShell {
          inputsFrom = [ scope'.easycrypt ];
          buildInputs =
            devPackages
            ++ [ scope'.why3 ]
            ++ (with pkgs.python3Packages; [ pyyaml ]);
        };

	devShells.noProvers = pkgs.mkShell rec {
	  inputsFrom = [ scope'.easycrypt ];
	  buildInputs = 
	     devPackages
	  ++ devTools
	  ++ [ scope'.why3 ]
	  ++ (with pkgs.python3Packages; [ pyyaml ]);
	  SHELL = ''${pkgs.bashInteractive + "/bin/bash"}'';
	  shellHook = builtins.replaceStrings ["\n"] [" "] ''
	    export SHELL=${SHELL} &&
	    export PATH=$PATH:`realpath .`
	  '';
	};

	devShells.withDevTools = pkgs.mkShell rec {
	  inputsFrom = [ scope'.easycrypt ];
	  buildInputs = 
	     devPackages
 	  ++ devTools
	  ++ [ scope'.why3 packages.provers ]
	  ++ (with pkgs.python3Packages; [ pyyaml ]);
	  SHELL = ''${pkgs.bashInteractive + "/bin/bash"}'';
	  shellHook = builtins.replaceStrings ["\n"] [" "] ''
	    export SHELL=${SHELL} &&
	    export PATH=$PATH:`realpath .`
	  '';
	};
      });
}
