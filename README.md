EasyCrypt: Computer-Aided Cryptographic Proofs
====================================================================

[![Build Status](https://travis-ci.org/EasyCrypt/easycrypt.svg?branch=1.0)](https://travis-ci.org/EasyCrypt/easycrypt)

EasyCrypt is a toolset for reasoning about relational properties of
probabilistic computations with adversarial code. Its main application
is the construction and verification of game-based cryptographic
proofs.

Table of Contents
--------------------------------------------------------------------

 * [EasyCrypt: Computer-Aided Cryptographic Proofs](#easycrypt-computer-aided-cryptographic-proofs)
    - [Installation requirements](#installation-requirements)
    - [Via OPAM](#via-opam)
      - [Installing requirements using OPAM (POSIX systems)](#installing-requirements-using-opam-posix-systems)
      - [Installing requirements using OPAM (non-POSIX systems)](#installing-requirements-using-opam-non-posix-systems)
    - [Via NIX](#via-nix)
 * [Configuring Why3](#configuring-why3)
 * [Installing/Compiling EasyCrypt](#installingcompiling-easycrypt)
 * [Proof General Front-End](#proof-general-front-end)
    - [Installing using opam](#installing-using-opam)
    - [Installing from sources](#installing-from-sources)


Installation requirements
--------------------------------------------------------------------

EasyCrypt uses the following third-party tools/libraries:

 * OCaml (>= 4.05)

     Available at http://caml.inria.fr/

 * OCamlbuild

 * Why3 (>= 1.3)

     Available at <http://why3.lri.fr/>

     Why3 must be installed with a set a provers.
     See <http://why3.lri.fr/#provers>

     Why3 libraries must be installed (make byte && make install-lib)

 * Menhir <http://gallium.inria.fr/~fpottier/menhir/>

 * OCaml Batteries Included <http://batteries.forge.ocamlcore.org/>

 * OCaml PCRE (>= 7) <https://github.com/mmottl/pcre-ocaml>

 * OCaml Zarith <https://forge.ocamlcore.org/projects/zarith>

 * OCaml ini-files <http://archive.ubuntu.com/ubuntu/pool/universe/o/ocaml-inifiles/>

On POSIX/Win32 systems (GNU/Linux, *BSD, OS-X), we recommend that users
install EasyCrypt and all its dependencies via `opam`.

Via OPAM
--------------------------------------------------------------------

### Installing requirements using OPAM 2 (POSIX systems)

Opam can be easily installed from source or via your packages manager:

  * On Ubuntu and derivatives:

      ```
      $> add-apt-repository ppa:avsm/ppa
      $> apt-get update
      $> apt-get install ocaml ocaml-native-compilers camlp4-extra opam
      ```

  * On Fedora/OpenSUSE:

      ```
      $> sudo dnf update
      $> sudo dnf install ocaml ocaml-docs ocaml-camlp4-devel opam
      ```

  * On MacOSX using brew:

      ```
      $> brew install ocaml opam
      ```

Once `opam` and `ocaml` has been successfully installed run the following:

```
$> opam init
$> eval $(opam env)
```

For any issues encountered installing `opam` see:

  * [https://opam.ocaml.org/doc/Install.html] for detailed opam installation instructions.

  * [https://opam.ocaml.org/doc/Usage.html] for how to initialize opam.

You can then install all the needed dependencies via the opam OCaml
packages manager.

  0. Optionally, switch to a dedicated compiler for EasyCrypt:

      ```
      $> opam switch create easycrypt $OVERSION
      ```

      where `$OVERSION` is a valid OCaml version (e.g. ocaml-base-compiler.4.07.0)

  1. Add the EasyCrypt package from repository:

      ```
      $> opam pin -yn add easycrypt https://github.com/EasyCrypt/easycrypt.git
      ```

  2. Optionally, use opam to install the system dependencies:

      ```
      $> opam install depext
      $> opam depext easycrypt
      ```

  3. Install EasyCrypt's dependencies:

      ```
      $> opam install --deps-only easycrypt
      $> opam install alt-ergo
      ```

     If you get errors about ocamlbuild failing because it's already
     installed, the check can be skipped with the following:

      ```
      CHECK_IF_PREINSTALLED=false opam install --deps-only easycrypt
      ```

  4. You can download extra provers at the following URLs:

     * Z3: [https://github.com/Z3Prover/z3]
     * CVC4: [https://cvc4.github.io/]

### Installing requirements using OPAM (non-POSIX systems)

You can install all the needed dependencies via the opam OCaml packages manager.

  1. Install the opam Ocaml packages manager, following the instructions at:

     https://fdopen.github.io/opam-repository-mingw/installation/

  2. Add the EasyCrypt package from repository:

      ```
      $> opam pin -yn add easycrypt https://github.com/EasyCrypt/easycrypt.git
      ```

  3. Use opam to install the system dependencies:

      ```
      $> opam install depext depext-cygwinports
      $> opam depext easycrypt
      ```

  4. Install EasyCrypt's dependencies:

      ```
      $> opam install --deps-only easycrypt
      $> opam install alt-ergo
      ```

  5. You can download extra provers at the following URLs:

     * Z3: [https://github.com/Z3Prover/z3]
     * CVC4: [https://cvc4.github.io/]


Via NIX
--------------------------------------------------------------------

First, install the [Nix package manager](https://nixos.org/) by
following [these instructions](https://nixos.org/manual/nix/stable/#chap-installation).

Then, at the root of the EasyCrypt source tree, type:

    ```
    $> nix-shell
    ```
    
These should install all the required dependencies. From there, simply
run:

    ```
    $> make
    ```
    
to compile EasyCrypt.

Configuring Why3
====================================================================

Before running EasyCrypt and after the installation/removal/update
of an SMT prover, you need to (re)configure Why3.

```
$> why3 config --detect --full-config
```

EasyCrypt is using the default Why3 location, i.e. ~/.why3.conf.
If you have several versions of Why3 installed, it may be impossible
to share the same configuration file among them. EasyCrypt via the
option -why3, allows you to load a Why3 configuration file from a
custom location. For instance:

```
$> why3 config --detect -C $WHY3CONF.conf
$> ./ec.native -why3 $WHY3CONF.conf
```

where `$WHY3CONF` must be replaced by some custom location.


Installing/Compiling EasyCrypt
====================================================================

If installing from source, running

```
$> make
$> make install
```

builds and install EasyCrypt (under the binary named `easycrypt`),
assuming that all dependencies have been successfully installed. If
you choose not to install EasyCrypt system wide, you can use the
binary `ec.native` that is located at the root of the source tree.

It is possible to change the installation prefix by setting the
environment variable PREFIX:

```
$> make PREFIX=/my/prefix install
```

EasyCrypt comes also with an opam package. Running

```
$> opam install easycrypt
```

installs EasyCrypt and its dependencies via opam. In that case, the
EasyCrypt binary is named `easycrypt`.


Proof General Front-End
====================================================================

EasyCrypt mode has been integrated upstream. Please, go
to <https://github.com/ProofGeneral/PG> and follow the instructions.
