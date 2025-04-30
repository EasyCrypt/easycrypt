
# EasyCrypt: Computer-Aided Cryptographic Proofs

---

EasyCrypt is a toolset for reasoning about relational properties of
probabilistic computations with adversarial code. Its main application
is the construction and verification of code-based, game-playing
cryptographic security proofs, but it's capable of more general formal verification tasks.
Another important application of EasyCrypt is proving the functional correctness
of low-level implementations—particularly those in
[Jasmin](https://github.com/jasmin-lang/jasmin)—against high-level specifications.

EasyCrypt is part of the [Formosa Crypto project](https://formosa-crypto.org/).

## Table of Contents

* [EasyCrypt: Computer-Aided Cryptographic Proofs](#easycrypt-computer-aided-cryptographic-proofs)
    * [Table of Contents](#table-of-contents)
* [Installation](#installation)
    * [Via OPAM (Recommended)](#via-opam-recommended)
        * [Quick and Dirty](#quick-and-dirty)
        * [Installing and Initializing OPAM](#installing-and-initializing-opam)
        * [Installing EasyCrypt's Dependencies via OPAM](#installing-easycrypts-dependencies-via-opam)
        * [Installing EasyCrypt via OPAM](#installing-easycrypt-via-opam)
    * [Via NIX](#via-nix)
    * [From Source](#from-source)
        * [Installing EasyCrypt's Dependencies From Source](#installing-easycrypts-dependencies-from-source)
        * [Installing EasyCrypt From Source](#installing-easycrypt-from-source)
* [Setup and Configuration](#setup-and-configuration)
    * [Why3 and SMT Solvers](#why3-and-smt-solvers)
        * [Compatibility](#compatibility)
        * [Configuring Why3](#configuring-why3)
    * [Front-Ends](#front-ends)
        * [Proof General (Emacs)](#proof-general-emacs)
        * [Visual Studio Code](#visual-studio-code)
* [Useful Resources](#useful-resources)
    * [Examples](#examples)

# Installation

---

There are multiple ways of installing EasyCrypt and its [dependencies](#installing-easycrypts-dependencies-from-source).
The recommended way is by simply installing everything
[via OPAM](#via-opam-recommended), a package manager for OCaml (the programming
language in which EasyCrypt is written). Other installation methods we cover here
are [via NIX](#via-nix) and [from source](#from-source). Whichever installation
method you choose, don't forget to do the [(post-installation)
setup and configuration](#setup-and-configuration)!

## Via OPAM (Recommended)

Installation via OPAM consists of three steps:
1. [Installing and Initializing OPAM](#installing-and-initializing-opam)
2. [Installing EasyCrypt's Dependencies via OPAM](#installing-easycrypt-via-opam)
3. [Installing EasyCrypt via OPAM](#installing-easycrypt-via-opam)

If you already have a working installation of OPAM on your system, you can skip ahead
to [installing EasyCrypt's dependencies via OPAM](#installing-easycrypts-dependencies-via-opam).

### Quick and Dirty

For the impatient, the following is a short list of instructions without
further explanations, nuances, or caveats (but lots of useful links!).
Use at your own risk.

1. [Install OPAM](https://opam.ocaml.org/doc/Install.html). Common methods are:
   * [Via your package manager](https://opam.ocaml.org/doc/Install.html#Using-your-system-39-s-package-manager)
   by running `<package-install-command> <opam-package>` (e.g., `apt-get install opam` for Debian/Ubuntu).
   * [Via one of OPAM's installation scripts](https://opam.ocaml.org/doc/Install.html#Binary-distribution)
   by downloading and running [this script on Unix-like systems](https://raw.githubusercontent.com/ocaml/opam/master/shell/install.sh)
   or [this script on Windows systems using PowerShell](https://raw.githubusercontent.com/ocaml/opam/master/shell/install.ps1).
2. [Initialize OPAM](https://opam.ocaml.org/doc/Usage.html#opam-init) by running `opam init`.
(Make sure to read the output and follow the instructions!)
3. Optional, but recommended:
   1. [Create a dedicated OPAM switch](https://ocaml.org/docs/opam-switch-introduction#creating-a-new-switch)
   by running `opam switch create <switch-name> <compiler-version>`.
   (Alternatively, you can run`opam switch --empty create <switch-name>` to forego specifying a
   compiler version and have OPAM pick one itself during the installation of
   EasyCrypt's dependencies.)
   2. [Activate the dedicated switch](https://ocaml.org/docs/opam-switch-introduction#creating-a-new-switch)
   by running `opam switch set <switch-name>`.
   (Make sure to read the output and follow the instructions!)
4. Add EasyCrypt's OPAM package by running
`opam pin -yn add easycrypt https://github.com/EasyCrypt/easycrypt.git`
(This requires `git`, so [make sure you have that installed first](https://git-scm.com/downloads))
5. Install EasyCrypt's dependencies by running `opam install --deps-only easycrypt`.
If you have an OPAM version <2.1 (which you can find out by running `opam --version`),
you have to precede this by running `opam install opam-depext`and `opam depext easycrypt`.
(Make sure to read the output and follow the instructions!)
6. Install SMT solvers that are [compatible with the current version of Why3 used by EasyCrypt](#compatibility).
For example, you can install Alt-Ergo version 2.5.2 by running `opam install alt-ergo.2.5.2`.
7. Install EasyCrypt itself by running `opam install easycrypt`.
Alternatively, if you want to have more control over the version you use,
install EasyCrypt from source by cloning this repository and running
`make` followed by `make install`.
8. [Configure Why3](#configuring-why3) by running `easycrypt why3config`.
9. Install a [front-end](#front-ends).


### Installing and Initializing OPAM

*This section takes most of its instructions from the [official installation guide
for OPAM](https://opam.ocaml.org/doc/Install.html) and
[the installation guide for OCaml](https://ocaml.org/docs/installing-ocaml).
If you have any problems, make sure to check out those guides first.*

On most operating systems, the recommended way of installing OPAM is by using the
package manager; [we cover this approach first](#using-the-package-manager).
Alternatively, OPAM provides a script that automatically installs the latest binary distribution for
your system; [we cover this approach second](#using-opams-script).
(For even more possible alternatives, consult the [official installation guide
for OPAM](https://opam.ocaml.org/doc/Install.html#Using-your-system-39-s-package-manager))

After installing OPAM, it needs to be initialized to actually get it to work;
[we'll cover that right after installation](#initialization).

#### Installation

#### Using the package manager

Search for your operating system in the list below and expand its section to
find the relevant instructions for installing OPAM.
If your operating system is not listed, consult the [official installation guide
for OPAM](https://opam.ocaml.org/doc/Install.html#Using-your-system-39-s-package-manager).

<details>

<summary>Debian/Ubuntu</summary>

Run the following command to install OPAM. You might need elevated privileges
to execute the command (which may be achieved in different ways; a common way
is prepending `sudo` to the command).

*Note, the Debian/Ubuntu package has the OCaml compiler as a recommended dependency,
which will be installed by default. If you don't want this,
run `apt-get install --no-install-recommends opam` instead of the following command.*

```
apt-get install opam
```

Once OPAM has been installed, move on to [initialize it](#initialization).

</details>

<details>

<summary>Arch</summary>

Run the following command to install OPAM. You might need elevated privileges
to execute the command (which may be achieved in different ways; a common way
is prepending `sudo` to the command).

```
pacman -S opam
```

Once OPAM has been installed, move on to [initialize it](#initialization).

</details>

<details>

<summary>Fedora/OpenSUSE</summary>

Run the following command to install OPAM. You might need elevated privileges
to execute the command (which may be achieved in different ways; a common way
is prepending `sudo` to the command).

```
dnf install opam
```

Once OPAM has been installed, move on to [initialize it](#initialization).

</details>

<details>

<summary>macOS (Homebrew and MacPorts)</summary>

Run one of the following commands to install OPAM. You might need elevated privileges to execute the command (which may be achieved in different ways; a common way is
prepending `sudo` to the command).

- Homebrew:

  ```
  brew install opam
  ```

- MacPorts:

  ```
  port install opam
  ```

Once OPAM has been installed, move on to [initialize it](#initialization).

</details>

<details>

<summary>OpenBSD</summary>

Run the following command to install OPAM. You might need elevated privileges
to execute the command (which may be achieved in different ways; a common way
is prepending `sudo` to the command).

```
pkg_add opam
```

Once OPAM has been installed, move on to [initialize it](#initialization).

</details>

<details>

<summary>FreeBSD</summary>

Run the following command to install OPAM. You might need elevated privileges
to execute the command (which may be achieved in different ways; a common way
is prepending `sudo` to the command).

```
pkg install ocaml-opam
```

Once OPAM has been installed, move on to [initialize it](#initialization).

</details>

<details>

<summary>Windows</summary>

Run the following command to install OPAM. You might need elevated privileges
to execute the command (which may be achieved in different ways; a common way
is opening the terminal with "Run as administrator").

```
winget install Git.Git OCaml.opam
```

Once OPAM has been installed, move on to [initialize it](#initialization).

</details>

##### Using OPAM's script

An alternative to [installing OPAM via the package manager](#using-the-package-manager)
is using one of the dedicated scripts provided by OPAM to automatically install
the relevant binary distribution for your system.

Search for your system/situation in the list below and expand its
section to find the relevant instructions for launching OPAM's script.
(If nothing matches your system/situation, consult the [official installation guide
for OPAM](https://opam.ocaml.org/doc/Install.html))

<details>

<summary>Unix-like system (including macOS)</summary>

Before proceeding, you need to ensure you have the following system packages:
`gcc`, `build-essential`, `curl`, `bubblewrap`, and `unzip`.
(Depending on your exact system, these packages might be named slightly differently).

Then, launch OPAM's script by running the following command.

```
bash -c "sh <(curl -fsSL https://opam.ocaml.org/install.sh)"
```

Alternatively, simply download the relevant script
from <https://raw.githubusercontent.com/ocaml/opam/master/shell/install.sh>
and run it directly.

This script will automatically detect your system's configuration
and install the relevant binary distribution. At some point, the
script might inform/prompt you about things like the desired
installation location. So, make sure to read the script's output
and follow along! (Often, the defaults suffice, but exceptions exist.
[For example, on on Ubuntu 24.04, you might want to set the
installation location to `/usr/bin`](https://github.com/ocaml/opam/issues/5968#issuecomment-2384914938))

Once the script has finished running *and* you have read and
followed its instructions, move on to [initialize OPAM](#initialization).

</details>

<details>

<summary>Windows system (using PowerShell)</summary>

Launch OPAM's script by running the following command.

```
Invoke-Expression "& { $(Invoke-RestMethod https://opam.ocaml.org/install.ps1) }
```

Alternatively, simply download the relevant script
from <https://raw.githubusercontent.com/ocaml/opam/master/shell/install.ps1>
and run it directly.


This script will automatically detect your system's configuration
and install the relevant binary distribution. At some point, the
script might inform/prompt you about things like the desired
installation location. So, make sure to read the script's output
and follow along!

Once the script has finished running *and* you have read and
followed its instructions, move on to [initialize OPAM](#initialization).
</details>


#### Initialization

After installing OPAM, it has to be initialized; this can be done by running
the following command.

```
opam init
```

This launches a program that may take several minutes to complete.
This program will inform/prompt you about things like updating your
configuration such that your environment will be setup
correctly (both in the current and future sessions). So, make sure to read the
program's output and follow its instructions!

These instructions may involve running more commands, typically including
something along the lines of

```
eval $(opam env)
```

for Unix-like systems; something along the lines of

```
for /f \"tokens=*\" %i in ('opam env') do @%i
```

for Windows systems using Windows Command Prompt; and something along the lines of

```
(& opam env) -split '\r?\n' | ForEach-Object { Invoke-Expression $_ }
```

for Windows systems using PowerShell.

Once the program has finished running *and* you have read and followed its instructions,
move on to [install EasyCrypt's dependencies via OPAM](#installing-easycrypts-dependencies-via-opam)

### Installing EasyCrypt's Dependencies via OPAM

At this stage, you should have a working OPAM installation which, by default,
contains a single [switch](https://ocaml.org/docs/opam-switch-introduction).
(This should, e.g., be the case if you followed [the installation and initialization
instructions above](#installing-and-initializing-opam) and didn't deviate from the defaults.)
A switch is OPAM's take on an isolated environment, similar to Python's `virtualenv`.

To ensure nothing interferes with your EasyCrypt installation (and your EasyCrypt
installation doesn't interfere with anything else!),
you can create a dedicated switch called `easycrypt` by running the following command.
(Optionally, you can specify a specific OCaml compiler to be used
for the switch by appending the compiler version to the command and leaving out the
`--empty` option; you can list the available compilers by
issuing `opam switch list-available`.)

```
opam switch --empty create easycrypt
```

Then, activate the switch by issuing the following command.

```
opam switch set easycrypt
```

These commands might inform/prompt you about properly setting up
your environment. Make sure to read the output and follow
the instructions!

(You can check which switch is currently active by issuing `opam switch list`.
The currently active switch will have an arrow in the left-most column of the output.)

Once you have activated the switch dedicated to EasyCrypt, run the following
command to add the EasyCrypt package. *Note that this requires `git`, so
[make sure you have that installed first](https://git-scm.com/downloads).*

```
opam pin -yn add easycrypt https://github.com/EasyCrypt/easycrypt.git
```

The next step will install all of EasyCrypt's (missing) dependencies.
OPAM can both recognize and install everything automatically, including
potentially missing system dependencies, but might need some additional
setup depending on the version. To find out which version of OPAM you have,
run the following command.

```
opam --version
```

If you have a version below 2.1 (i.e., 2.0.X or lower), expand the section below
to find relevant instructions. *If you have a version greater than or equal to 2.1.X,
you do not have to do this.*

<details>

<summary>Installing System Dependencies with OPAM version <2.1</summary>

First, install OPAM's "system dependency manager plugin" by
running the following command.

  ```
  opam install opam-depext
  ```

Again, this command might inform/prompt you about properly setting up
your environment. Make sure to read the output and follow
the instructions!

Then, let OPAM discover and install any missing system dependencies by running
the following command. Here, you might be informed/prompted about installing these
dependencies via the appropriate mechanisms for your system (typically your package manager).
So, make sure to read the command's output and follow its instructions!

  ```
  opam depext easycrypt
  ```

</details>

Let OPAM discover and install all of EasyCrypt's dependencies by running
the following command. Note that, if you have an OPAM version >= 2.1,
this command will also discover and install any missing system dependencies.
In this case, you might be informed/prompted about installing these dependencies
via the appropriate mechanisms for your system (often your package manager).
So, make sure to read the command's output and follow its instructions!

```
opam install --deps-only easycrypt
```

Finally, install at least one
[SMT solver compatible with the current version of Why3 used by EasyCrypt](#compatibility).
One such solver is Alt-Ergo, which happens to be packaged by OPAM.
While this is strictly speaking not a dependency of EasyCrypt, you can run the
following command to install (the right version of) Alt-Ergo via OPAM and keep things simple.

```
opam install alt-ergo.2.5.2
```

(If you accidentally installed a different version of Alt-Ergo, you can change
to version 2.5.2 by running `opam pin alt-ergo 2.5.2`)

At this point, you may move on to [install EasyCrypt via OPAM](#installing-easycrypt-via-opam).
However, if you want, you can install additional SMT solvers,
which allows you to pick-and-choose between solvers on the fly
(or use them all at the same time!).
Common solvers that are
[compatible with the current version of Why3 used by EasyCrypt are listed below](#compatibility).

### Installing EasyCrypt via OPAM

Having installed EasyCrypt's dependencies and some suitable
SMT solver(s), you might actually still consider [installing EasyCrypt from
source](#installing-easycrypt-from-source), even if you
did the rest via OPAM. (You might, for example, want this to
have more direct control over the version of EasyCrypt you use.)
Otherwise, install EasyCrypt (via OPAM) by running the following command.

```
opam install easycrypt
```

If everything went according to plan, you now have everything you need to
run EasyCrypt! However, before you get ahead of yourself, move to the
[(post-installation) setup and configuration](#setup-and-configuration) to
make sure everything works as it should.

## Via NIX

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

## From Source

### Installing EasyCrypt's Dependencies From Source

EasyCrypt uses the following third-party tools/libraries:

 * OCaml, version >= 4.08

     Available at https://ocaml.org/

 * OCamlbuild

 * Why3, version 1.8

     Available at <http://why3.lri.fr/>

     Why3 must be installed with a set a provers.
     See <http://why3.lri.fr/#provers>

     Why3 libraries must be installed (make byte && make install-lib)

 * Menhir <http://gallium.inria.fr/~fpottier/menhir/>

 * OCaml Batteries Included <http://batteries.forge.ocamlcore.org/>

 * OCaml PCRE (>= 7) <https://github.com/mmottl/pcre-ocaml>

 * OCaml Zarith <https://forge.ocamlcore.org/projects/zarith>

 * OCaml ini-files <http://archive.ubuntu.com/ubuntu/pool/universe/o/ocaml-inifiles/>

### Installing EasyCrypt From Source

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

# Setup and Configuration

---

After [installing EasyCrypt and its dependencies](#installation), some basic setup
and configuration is still needed to make everything work properly.
Specifically, if you didn't yet install at least one
[suitable SMT solver, you should do that first](#compatibility).
Then, it is crucial you [configure Why3](#configuring-why3)
to allow EasyCrypt to interface with the installed SMT solvers.
Lastly, if you want to do anything more than merely verifying existing
proof scripts from the command-line, it's strongly recommended to
[install a suitable front-end](#frontends) (even for very simple
inspection and interaction with proof scripts).

## Why3 and SMT Solvers

---

### Compatibility

Why3 and SMT solvers are independent pieces of software with their
own version-specific interactions. Obtaining a working setup may
require installing specific versions of some of the solvers.

At present, EasyCrypt depends on Why3 1.8, which (at least)
supports the following (versions of) SMT solvers.

* [Alt-Ergo](https://alt-ergo.ocamlpro.com/), version 2.5.2
* [CVC4](https://cvc4.github.io/), version 1.8
* [CVC5](https://cvc5.github.io/), version 1.0.8
* [Z3](https://github.com/Z3Prover/z3), version 4.12.X

Alt-Ergo is packaged by OPAM, and (the above version) can be installed by running
the following command.

```
opam install alt-ergo.2.5.2
```

If you have already installed a different version of Alt-Ergo, you can
switch to the above version by running `opam pin alt-ergo 2.5.2`.

### Configuring Why3

After the installation, removal, and/or update of SMT provers you plan to use
with EasyCrypt, you should (re)configure Why3 by running the following command.

```
easycrypt why3config
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

## Front-Ends

---

While using EasyCrypt directly from the command line can be sufficient for
verifying existing proof scripts, it's highly recommended to install a suitable front-end
when engaging in anything more than that (even for simply inspecting and interacting
with proof scripts). At present, the only available front-end is based on Emacs's
[Proof General](https://github.com/ProofGeneral/PG).
However, a front-end for VSCode is currently in development.

### Proof-General (Emacs)

EasyCrypt mode has been integrated upstream. Please, go
to <https://github.com/ProofGeneral/PG> and follow the instructions.

### Visual Studio Code

Coming soon.


# Useful Resources

---

## Examples

---

Examples of how to use EasyCrypt are in the `examples` directory. You
will find basic examples at the root of this directory, as well as a
more advanced example in the `MEE-CBC` sub-directory and a tutorial on
how to use the complexity system in `cost` sub-directory.
