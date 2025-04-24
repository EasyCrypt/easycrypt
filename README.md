EasyCrypt: Computer-Aided Cryptographic Proofs
====================================================================

EasyCrypt is a toolset for reasoning about relational properties of
probabilistic computations with adversarial code. Its main application
is the construction and verification of code-based, game-playing
cryptographic security proofs, but it's capable of more general formal verification tasks.
Another important application of EasyCrypt is proving the functional correctness
of low-level implementations—particularly those in
[Jasmin](https://github.com/jasmin-lang/jasmin)—against high-level specifications.

EasyCrypt is part of the [Formosa Crypto project](https://formosa-crypto.org/).


TODO: move the following

While using EasyCrypt directly from the command line can be sufficient for
verifying existing proof scripts, it's highly recommended to install a suitable front-end
when engaging in anything more than that (even for simply inspecting and interacting
with proof scripts). At present, the only available front-end is based on Emacs's
[Proof General](https://github.com/ProofGeneral/PG).
However, a VSCode-based front-end is currently in development.

Table of Contents
--------------------------------------------------------------------

 * [EasyCrypt: Computer-Aided Cryptographic Proofs](#easycrypt-computer-aided-cryptographic-proofs)
    - [Table of Contents](#table-of-contents)
* [Installation](#installation)
    - [Via OPAM (Recommended)](#via-opam-recommended)
    - [Via NIX](#via-nix)
    - [From Scratch](#installation-requirements)
        - [Installation requirements](#installation-requirements)
 * [Configuring Why3](#configuring-why3)
    - [Note on prover versions](#note-on-prover-versions)
 * [Installing/Compiling EasyCrypt](#installingcompiling-easycrypt)
 * [Proof General Front-End](#proof-general-front-end)
    - [Installing using opam](#installing-using-opam)
    - [Installing from sources](#installing-from-sources)


# Installation
--------------------------------------------------------------------
There are multiple ways of installing EasyCrypt and its [dependencies](#dependencies).
The recommended way is by simply installing everything
[via OPAM](#via-opam-recommended), a package manager for OCaml (the programming
language in which EasyCrypt is written). Other installation methods we cover here
are [via NIX](#via-nix) and [from scratch](#from-scratch).

## Via OPAM (Recommended)
Installation via OPAM consists of three steps:
1. [Installing and initializing OPAM](#installing-and-initializing-opam)
2. [Installing EasyCrypt's dependencies via OPAM](#installing-easycrypt-via-opam)
3. [Installing EasyCrypt via OPAM](#installing-easycrypt-via-opam)

If you already have a working installation of OPAM on your system, feel free to skip ahead
to [installing EasyCrypt's dependencies via OPAM](#installing-easycrypts-dependencies-via-opam)!

### Installing and initializing OPAM
*This section takes most of its instructions from the [official installation guide
for OPAM](https://opam.ocaml.org/doc/Install.html) and
[the installation guide for OCaml](https://ocaml.org/docs/installing-ocaml) .
If you have any problems, make sure to check out those guides first.*

On most operating systems, the recommended way to install and initialize OPAM is by first
installing it via the package manager, and then initialize it manually; [we cover this
approach first](#using-the-package-manager). Alternatively, OPAM provides a
script that automatically installs and initializes the latest binary distribution for
your operating system; [we cover this approach second](#using-opams-script).

(For even more possible alternatives, consult the [official installation guide
for OPAM](https://opam.ocaml.org/doc/Install.html#Using-your-system-39-s-package-manager))

#### Using the package manager
##### Installation
Open up a terminal and issue the command listed below for your operating system.
You might need elevated privileges to execute the command (which you might
achieve by, e.g., prepending `sudo` to the command).
If your operating system is not listed, consult the [official installation guide
for OPAM](https://opam.ocaml.org/doc/Install.html#Using-your-system-39-s-package-manager),
or consider [the alternative way of installing and initializing OPAM described below](#using-opams-script).

* Debian/Ubuntu:

```
apt-get install opam
```

*Note, the Debian/Ubuntu package has the OCaml compiler as a recommended dependency, which is
installed by default. If you don't want this, issue the following command instead of the above one.*

```
apt-get install --no-install-recommends opam
```

* Arch:

```
pacman -S opam
```

* Fedora/OpenSUSE:

```
dnf install opam
```

* macOS:
  - Homebrew:

  ```
  brew install opam
  ```
  - MacPorts:

  ```
  port install opam
  ```

* OpenBSD:

```
pkg_add opam
```

* FreeBSD:

```
pkg install ocaml-opam
```

* Windows:

```
winget install Git.Git OCaml.opam
```

##### Initialization
After installing OPAM, it has to be initialized.
This is as simple as issuing the following command in your terminal.

```
opam init
```

This launches a script that may take several minutes to complete. This script will inform/prompt
you about updating your configuration such that your environment will be setup
correctly, both in the current and future sessions. So, make sure to read the script's
output and follow its instructions!

This may involve issuing more commands in the terminal, typically something along the lines of

```
eval $(opam env)
```

for Unix-like systems; something along the lines of

```
for /f \"tokens=*\" %i in ('opam env') do @%i
```

for Windows using Windows Command Prompt; and something along the lines of

```
(& opam env) -split '\r?\n' | ForEach-Object { Invoke-Expression $_ }
```

for Windows using PowerShell.

After the script finishes running and you have followed its instructions, you are ready to
proceed to [installing EasyCrypt's dependencies via OPAM](#installing-easycrypts-dependencies-via-opam)

#### Using OPAM's script
An alternative to [installing OPAM via the package manager and initializing it manually](#using-the-package-manager)
is using the script provided by OPAM to automatically perform both installation (of a binary distribution for your
operating system) as well as initialization.

Before proceeding, if you are on a Unix-like system (including macOS), you need to install the
following software/system packages: `gcc`, `build-essential`, `curl`, `bubblewrap`, and `unzip`.
(Depending on your system, these packages might be named slightly differently.)

Then, open up a terminal and issue the command listed below for your situation/operating system.

(If nothing matches your situation/operating system, consult the [official installation guide
for OPAM](https://opam.ocaml.org/doc/Install.html#Using-your-system-39-s-package-manager) for other potential alternatives)

* Unix-like system:

```
bash -c "sh <(curl -fsSL https://opam.ocaml.org/install.sh)"
```

* Windows (using PowerShell):

```
Invoke-Expression "& { $(Invoke-RestMethod https://opam.ocaml.org/install.ps1) }
```

If you are having trouble with fetching the script, simply download the relevant script
from <https://raw.githubusercontent.com/ocaml/opam/master/shell/install.sh> (for Unix-based systems)
or <https://raw.githubusercontent.com/ocaml/opam/master/shell/install.ps1> (for Windows systems), and run the script directly.

After downloading the relevant binary distribution, this script will automatically start
initializing OPAM, which may several minutes to complete. At this point, the script
will inform/prompt you about updating your configuration such that your
environment will be setup correctly, both in the current and future sessions.
So, make sure to read the script's output and follow its instructions!

This may involve issuing more commands in the terminal, typically something along the lines of

```
eval $(opam env)
```

for Unix-like systems; something along the lines of

```
for /f \"tokens=*\" %i in ('opam env') do @%i
```

for Windows using Windows Command Prompt; and something along the lines of

```
(& opam env) -split '\r?\n' | ForEach-Object { Invoke-Expression $_ }
```

for Windows using PowerShell.

After the script finishes running and you have followed its instructions, you are ready to
proceed to [installing EasyCrypt's dependencies via OPAM](#installing-easycrypts-dependencies-via-opam)

### Installing EasyCrypt's dependencies via OPAM

### Installing EasyCrypt via OPAM

## From scratch
Dependencies
--------------------------------------------------------------------
TODO: Move this
EasyCrypt uses the following third-party tools/libraries:

 * OCaml (>= 4.08)

     Available at https://ocaml.org/

 * OCamlbuild

 * Why3 (>= 1.7.x, < 1.8)

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
      $> opam install opam-depext
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
$> make nix-build
```

Once completed, you will find the EasyCrypt binary in `result/bin`.

You can also run

```
$> make nix-build-with-provers
```

to install EasyCrypt along with a set of provers.


For getting a development environment, you can run:

```
$> make nix-develop
```

These will install all the required dependencies, a set of provers and
will then drop you into a shell. From there, simply run `make` to
compile EasyCrypt.

Note on Prover Versions
--------------------------------------------------------------------

Why3 and SMT solvers are independent pieces of software with their
own version-specific interactions. Obtaining a working SMT setup may
require installing specific versions of some of the provers.

At the time of writing, we depend on Why3 1.7.x, which supports the
following prover versions:

 * Alt-Ergo 2.5.2
 * CVC4 1.8
 * CVC5 1.0.8
 * Z3 4.12.x

`alt-ergo` can be installed using opam, if you do you can use pins to
select a specific version (e.g, `opam pin alt-ergo 2.5.2`).

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

EasyCrypt comes also with an opam package. Running

```
$> opam install easycrypt
```

installs EasyCrypt and its dependencies via opam. In that case, the
EasyCrypt binary is named `easycrypt`.

Configuring Why3
====================================================================

Initially, and after the installation/removal/update of SMT provers,
you need to (re)configure Why3 via the following `easycrypt` command:

```
$> easycrypt why3config
```

EasyCrypt stores the Why3 configuration file under

```
$XDG_CONFIG_HOME/easycrypt/why3.conf
```

EasyCrypt allows you, via the option -why3, to load a Why3
configuration file from a custom location. For instance:

```
$> easycrypt why3config -why3 $WHY3CONF.conf
$> easycrypt -why3 $WHY3CONF.conf
```

where `$WHY3CONF` must be replaced by some custom location.

Proof General Front-End
====================================================================

EasyCrypt mode has been integrated upstream. Please, go
to <https://github.com/ProofGeneral/PG> and follow the instructions.

Examples
====================================================================

Examples of how to use EasyCrypt are in the `examples` directory. You
will find basic examples at the root of this directory, as well as a
more advanced example in the `MEE-CBC` sub-directory and a tutorial on
how to use the complexity system in `cost` sub-directory.
