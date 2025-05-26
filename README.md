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

- [EasyCrypt: Computer-Aided Cryptographic Proofs](#easycrypt-computer-aided-cryptographic-proofs)
  - [Table of Contents](#table-of-contents)
- [Installation](#installation)
- [Setup and Configuration](#setup-and-configuration)
  - [Why3 and SMT Solvers](#why3-and-smt-solvers)
    - [Compatibility](#compatibility)
       - [Configuring Why3](#configuring-why3)
    - [Front-Ends](#front-ends)
      - [Proof General (Emacs)](#proof-general-emacs)
      - [Visual Studio Code](#visual-studio-code)
- [Useful Resources](#useful-resources)
  - [Examples](#examples)

# Installation

---

There are several ways to install EasyCrypt and its dependencies.
The recommended method is to use OPAM, a package manager for OCaml (the programming
language EasyCrypt is written in). This guide provides a brief overview of that process.
For more detailed instructions, caveats, and alternative installation
methods, please refer to [INSTALL.md](INSTALL.md). Also, if you encounter any issues,
be sure to consult
[the list of known installation quirks and corresponding troubleshooting tips](https://github.com/EasyCrypt/easycrypt/wiki/%5BSetup%5D-Installation-Quirks).


> **Note:** The last two steps covered here are actually part of the (post-installation)
> setup and configuration, which is further detailed [below](#setup-and-configuration).

1. [Install OPAM](https://opam.ocaml.org/doc/Install.html).  
   Common methods include:
   * [Via your package manager](https://opam.ocaml.org/doc/Install.html#Using-your-system-39-s-package-manager).  
   Run `<package-install-command> <opam-package>` (e.g., `apt-get install opam` for Debian/Ubuntu).
   * [Via one of OPAM's installation scripts](https://opam.ocaml.org/doc/Install.html#Binary-distribution).  
   Download and run [this script on Unix-like systems](https://raw.githubusercontent.com/ocaml/opam/master/shell/install.sh)
   or [this script on Windows systems using PowerShell](https://raw.githubusercontent.com/ocaml/opam/master/shell/install.ps1).
2. [Initialize OPAM](https://opam.ocaml.org/doc/Usage.html#opam-init).  
   Run `opam init` (and make sure to read the output and follow any instructions).
3. Optional, but recommended:
   1. [Create a dedicated OPAM switch](https://ocaml.org/docs/opam-switch-introduction#creating-a-new-switch).  
   Run `opam switch --empty create <switch-name>`.  
   (Alternatively, run `opam switch create <switch-name> <compiler-version>` to pick a specific
   compiler version yourself, instead of letting OPAM pick one for you during the installation
   of EasyCrypt's dependencies.)
   2. [Activate the dedicated switch](https://ocaml.org/docs/opam-switch-introduction#creating-a-new-switch).  
   Run `opam switch set <switch-name>` (and make sure to read the output and follow any instructions).
4. Add EasyCrypt's OPAM package.  
   Run `opam pin -yn add easycrypt https://github.com/EasyCrypt/easycrypt.git`.
   (This requires `git`, so [make sure you have that installed first](https://git-scm.com/downloads).)
5. Install EasyCrypt's dependencies.  
   Run `opam install --deps-only easycrypt`.
   - If your OPAM version is below 2.1 (which you can find out by running `opam --version`), first
     run `opam install opam-depext` and `opam depext easycrypt`, in that order
     (and make sure to read the output and follow any instructions).
6. Install [compatible SMT solvers](#compatibility).  
   For example, to install Alt-Ergo version 2.6.0, run `opam install alt-ergo.2.6.0`.
7. Install EasyCrypt.  
   Run `opam install easycrypt`.  
   (Alternatively, install from source by cloning or downloading this repository,
   navigating to its root, and running `make` followed by `make install`.)
8. [Configure Why3](#configuring-why3).  
   Run `easycrypt why3config`.
9. Install a [front-end](#front-ends).

# Setup and Configuration

---

After [installing EasyCrypt and its dependencies](#installation), some
additional setup and configuration are required to ensure everything works
properly. First, if you haven't yet installed at least one
[suitable SMT solver](#compatibility), you should do that first.
Then, it's crucial to [configure Why3](#configuring-why3)
so that EasyCrypt can interface with the installed SMT solvers.
Lastly, if you want to do more than just verify existing
proof scripts from the command-line, it's strongly recommended to
[install a suitable front-end](#frontends). Even for very simple
inspection and interaction with proof scripts, having a front-end
is highly recommended.

## Why3 and SMT Solvers

### Compatibility

Why3 and SMT solvers are independent pieces of software with their
own version-specific interactions. Setting up a working environment may require
installing specific versions of some solvers.

EasyCrypt currently depends on Why3, version >= 1.8 and < 1.9, which supports
the following recommended SMT solvers:

* [Alt-Ergo](https://alt-ergo.ocamlpro.com) (version 2.6.0)
* [CVC5](https://cvc5.github.io) (version 1.0.8)
* [Z3](https://github.com/Z3Prover/z3) (version 4.12.x)

Alt-Ergo is available via OPAM. To install version 2.6.0, run

```
opam install alt-ergo.2.6.0
```

If you've installed a different version of Alt-Ergo, you can switch to version
2.6.0 by running `opam pin alt-ergo 2.6.0`.

### Configuring Why3

After installing, removing, or updating any SMT solvers you plan to use with
EasyCrypt, you should (re)configure Why3 to reflect these changes.

You can do this manually, or let EasyCrypt handle it using the `why3config`
sub-command:

```
easycrypt why3config
```

By default, EasyCrypt saves the generated Why3 configuration file
to `$XDG_CONFIG_HOME/easycrypt/why3.conf` on Unix-like systems (falling
back to `$HOME/.config/easycrypt/why3.conf` if `$XDG_CONFIG_HOME` is unset),
and to `%HOME%\Local Settings\easycrypt\why3.conf` on Windows systems.

If you'd prefer to store the configuration file elsewhere, pass
the desired path (represented by `<configuration-file>` below) to the `-why3` option:

```
easycrypt why3config -why3 <configuration-file>
```

Note that EasyCrypt does not remember custom configuration paths: Unless
told otherwise, it will only search in some default locations
(including the standard generation path and certain system-wide locations).
To run EasyCrypt with a Why3 configuration file stored in a non-default location,
again use the `-why3` option to pass the path to the file:

```
easycrypt -why3 <configuration-file>
```

(In this case, you’re simply running EasyCrypt with
the specified configuration file, not generating
a new one—hence the omission of the `why3config` sub-command.)

## Front-Ends

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

Work in progress.


# Useful Resources

---

## Examples

Examples of how to use EasyCrypt are in the `examples` directory. You
will find basic examples at the root of this directory, as well as a
more advanced example in the `MEE-CBC` sub-directory and a tutorial on
how to use the complexity system in `cost` sub-directory.
