
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
    * [Via Nix](#via-nix)
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

There are several ways to install EasyCrypt and its [dependencies](#installing-easycrypts-dependencies-from-source).
The recommended method is to simply install everything
[using OPAM](#via-opam-recommended), a package manager for OCaml (the programming
language EasyCrypt is written in). Other installation methods include
[using Nix](#via-nix) and [directly from source](#from-source). Whichever
method you choose, be sure to follow the [(post-installation)
setup and configuration instructions](#setup-and-configuration)!

## Via OPAM (Recommended)

Installation via OPAM consists of three steps:
1. [Installing and Initializing OPAM](#installing-and-initializing-opam)
2. [Installing EasyCrypt's Dependencies via OPAM](#installing-easycrypt-via-opam)
3. [Installing EasyCrypt via OPAM](#installing-easycrypt-via-opam)

If you already have a working installation of OPAM on your system, you can skip ahead
to [installing EasyCrypt's dependencies via OPAM](#installing-easycrypts-dependencies-via-opam).

### Quick and Dirty

For the impatient, the following is a concise list of instructions without
further explanations or caveats (but lots of useful links).
Use at your own risk!

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
   Run `opam switch set <switch-name>` (and make sure to read the output and follow any instructions!)
4. Add EasyCrypt's OPAM package.  
   Run `opam pin -yn add easycrypt https://github.com/EasyCrypt/easycrypt.git`.
   (This requires `git`, so [make sure you have that installed first](https://git-scm.com/downloads).)
5. Install EasyCrypt's dependencies.  
   Run `opam install --deps-only easycrypt`.
   - If your OPAM version is below 2.1 (which you can find out by running `opam --version`), first
     run `opam install opam-depext` and `opam depext easycrypt`, in that order
     (and make sure to read the output and follow any instructions).
6. Install [compatible SMT solvers](#compatibility).  
   For example, install Alt-Ergo version 2.5.2 by running `opam install alt-ergo.2.5.2`.
7. Install EasyCrypt.  
   Run `opam install easycrypt`.
   Alternatively, install from source by cloning or downloading this repository
   and running `make` followed by `make install`.
8. [Configure Why3](#configuring-why3).  
   Run `easycrypt why3config`.
9. Install a [front-end](#front-ends).


### Installing and Initializing OPAM

> **Note:** This section takes most of its instructions from [the official OPAM
> installation guide](https://opam.ocaml.org/doc/Install.html) and [the OCaml
> installation guide](https://ocaml.org/docs/installing-ocaml). If you encounter
> any issues, be sure to consult those resources first.

On most operating systems, the recommended way to install OPAM is through
your system's package manager—[we'll cover this approach first](#using-the-package-manager).
Alternatively, OPAM provides scripts that automatically install the latest binary distribution for
your system—[we'll cover this method second](#using-opams-scripts).
(For additional installation methods, consult the
[the official OPAM installation guide](https://opam.ocaml.org/doc/Install.html#Using-your-system-39-s-package-manager))

After installing OPAM, it must be
initialized—[we'll cover that immediately after installation](#initialization).

#### Installation

#### Using the package manager

Search for your operating system in the list below and expand its section to
view the relevant instructions for installing OPAM.
If your operating system is not listed, refer to
[the official OPAM installation guide](https://opam.ocaml.org/doc/Install.html#Using-your-system-39-s-package-manager).

<details>

<summary>Debian/Ubuntu</summary>

To install OPAM, run the following command. You may need elevated privileges
to do so—commonly by prefixing the command with `sudo`, though other methods
may apply depending on your system.

> **Note:** The Debian/Ubuntu `opam` package includes the OCaml compiler as a
> *recommended* dependency, which is installed by default. If you wish to avoid 
> this, run `apt-get install --no-install-recommends opam` instead.

```
apt-get install opam
```

Once OPAM is installed, proceed to the [initialization step](#initialization).

</details>

<details>

<summary>Arch</summary>

To install OPAM, run the following command. You may need elevated privileges
to do so—commonly by prefixing the command with `sudo`, though other methods
may apply depending on your system.

```
pacman -S opam
```

Once OPAM is installed, proceed to the [initialization step](#initialization).

</details>

<details>

<summary>Fedora/OpenSUSE</summary>

To install OPAM, run the following command. You may need elevated privileges
to do so—commonly by prefixing the command with `sudo`, though other methods
may apply depending on your system.

```
dnf install opam
```

Once OPAM is installed, proceed to the [initialization step](#initialization).

</details>

<details>

<summary>macOS (Homebrew and MacPorts)</summary>

To install OPAM, run one of the following commands. You may need elevated privileges
to do so—commonly by prefixing the command with `sudo`, though other methods
may apply depending on your system.

- Homebrew:

  ```
  brew install opam
  ```

- MacPorts:

  ```
  port install opam
  ```

Once OPAM is installed, proceed to the [initialization step](#initialization).

</details>

<details>

<summary>OpenBSD</summary>

To install OPAM, run the following command. You may need elevated privileges
to do so—commonly by prefixing the command with `sudo`, though other methods
may apply depending on your system.

```
pkg_add opam
```

Once OPAM is installed, proceed to the [initialization step](#initialization).

</details>

<details>

<summary>FreeBSD</summary>

To install OPAM, run the following command. You may need elevated privileges
to do so—commonly by prefixing the command with `sudo`, though other methods
may apply depending on your system.

```
pkg install ocaml-opam
```

Once OPAM is installed, proceed to the [initialization step](#initialization).

</details>

<details>

<summary>Windows</summary>

To install OPAM, run the following command. You may need elevated privileges
to do so—commonly by opening the terminal as an administrator ("Run as administrator"),
though other methods may apply depending on your system.

```
winget install Git.Git OCaml.opam
```

Once OPAM is installed, proceed to the [initialization step](#initialization).

</details>

##### Using OPAM's scripts

An alternative to [installing OPAM via the package manager](#using-the-package-manager)
is to use one of the dedicated scripts provided by OPAM. These scripts automatically install
the appropriate binary distribution for your system.

Search for your system/situation in the list below and expand the
corresponding section to view instructions for running the relevant script.
If none of the options match your system/situation, refer to
[the official OPAM installation guide](https://opam.ocaml.org/doc/Install.html)
for more alternatives.

<details>

<summary>Unix-like system (including macOS)</summary>

Before proceeding, make sure the following system packages are installed:
`gcc`, `build-essential`, `curl`, `bubblewrap`, and `unzip`.
(Depending on your system, the exact packages names may vary slightly).

To launch OPAM's script, run the following command:

```
bash -c "sh <(curl -fsSL https://opam.ocaml.org/install.sh)"
```

Alternatively, you can download the script manually
from <https://raw.githubusercontent.com/ocaml/opam/master/shell/install.sh>
and run it directly.

This script will automatically detect your system's configuration
and install the appropriate binary distribution. At some point,
it may prompt you to confirm options like the installation location.
Be sure to read the output carefully and follow all instructions!

> While the defaults usually suffice, exceptions exist.
> For example, [on Ubuntu 24.04, you might want to set the
> installation location to `/usr/bin`](https://github.com/ocaml/opam/issues/5968#issuecomment-2384914938).

Once the script has completed *and* you've followed any additional
instructions, proceed to [initialize OPAM](#initialization).

</details>

<details>

<summary>Windows system (using PowerShell)</summary>

To launch OPAM's script, run the following command (in PowerShell):

```
Invoke-Expression "& { $(Invoke-RestMethod https://opam.ocaml.org/install.ps1) }
```

Alternatively,  you can download the script manually
from <https://raw.githubusercontent.com/ocaml/opam/master/shell/install.ps1>
and run it directly.

This script will automatically detect your system's configuration
and install the appropriate binary distribution. At some point,
it may prompt you to confirm options like the installation location.
Be sure to read the output carefully and follow all instructions!

Once the script has completed *and* you've followed any additional
instructions, proceed to [initialize OPAM](#initialization).

</details>


#### Initialization

After installing OPAM, initialize it by running the following command:

```
opam init
```

This command launches a program that may take several minutes to complete.
At some point, it may provide additional instructions to ensure a
working setup. Be sure to read the output carefully and follow all instructions!

Typically, these instructions involve running a command to configure your
environment for both the current and future sessions. The exact command
depends on your system, but usually looks something like

```
eval $(opam env)
```

for Unix-like systems; something like

```
for /f \"tokens=*\" %i in ('opam env') do @%i
```

for Windows systems using Windows Command Prompt; and something like

```
(& opam env) -split '\r?\n' | ForEach-Object { Invoke-Expression $_ }
```

for Windows systems using PowerShell.

Once the program has finished *and* you've followed its instructions,
proceed to [install EasyCrypt's dependencies](#installing-easycrypts-dependencies-via-opam).

### Installing EasyCrypt's Dependencies via OPAM

At this stage, you should have a working OPAM installation. By default, such an installation
contains a single [switch](https://ocaml.org/docs/opam-switch-introduction).)
A switch is OPAM's take on an isolated environment, similar to Python's `virtualenv`.
To avoid conflicts with your EasyCrypt installation (and vice versa),
it's recommended to create a dedicated switch.

You can create a new switch called `easycrypt` by running the following command.
(Optionally, you can specify a specific OCaml compiler for the switch by
appending the compiler version to the command and leaving out the `--empty`
option; you can list the available compilers by running `opam switch list-available`.
The compiler version must be >= 4.08 and < 5.0)

```
opam switch --empty create easycrypt
```

Once the switch is created, activate it with

```
opam switch set easycrypt
```

Make sure to read the output and follow any additional instructions provided by these commands!

(To check which switch is currently active, run `opam switch list`.
The active switch will be marked with an arrow on the left-hand side.)

Then, add the EasyCrypt package to your switch by running the following command.
> **Note:** This requires `git`, so [make sure you have that installed first](https://git-scm.com/downloads).

```
opam pin -yn add easycrypt https://github.com/EasyCrypt/easycrypt.git
```

At this point, you need to install EasyCrypt's (missing) dependencies.
OPAM can automatically detect and install all required dependencies, including any
system dependencies, but might need some additional setup depending on the version.
To check your OPAM version, run

```
opam --version
```

If your OPAM version is **below 2.1** (i.e., 2.0.x or lower), expand the section below
to view necessary setup instructions. *If your versions is 2.1.x or higher,
you do not have to do this.*

<details>

<summary>Installing System Dependencies with OPAM Version < 2.1</summary>

First, install OPAM's "system dependency manager plugin" with

  ```
  opam install opam-depext
  ```

This may provide additional instructions to setup your environment properly—be
sure to read the output carefully and follow any instructions.

Then, run the following command to let OPAM detect and install missing system dependencies:

  ```
  opam depext easycrypt
  ```

This may prompt you to install certain dependencies via your system's package
manager or some other appropriate mechanism. Be sure to read the output carefully
and follow any instructions!

</details>

Let OPAM detect and install EasyCrypt's dependencies by running the following
command.

```
opam install --deps-only easycrypt
```

If your OPAM version is **2.1 or higher**, this command will also detect
and install any missing *system* dependencies. In this case,
you may be prompted to install these dependencies via your
system's package manager or some other appropriate mechanism.
Be sure to read the output carefully and follow any instructions!

Finally, install at least one
[SMT solver compatible with the current version of Why3 used by EasyCrypt](#compatibility).
A common choice is Alt-Ergo, which is conveniently packaged by OPAM.
Although it's not a direct dependency of EasyCrypt (and you're free
to use a different compatible SMT solver), the simplest option is to
install the correct version of Alt-Ergo via OPAM by running

```
opam install alt-ergo.2.5.2
```

(If you accidentally installed a different version of Alt-Ergo, you can change
to version 2.5.2 by running `opam pin alt-ergo 2.5.2`)

At this point, you can proceed to [install EasyCrypt](#installing-easycrypt-via-opam).
However, if you wish, you can also install additional SMT solvers.
This allows you to pick and choose between multiple solvers, or use them simultaneously.
A list of compatible solvers is available [below](#compatibility).

### Installing EasyCrypt via OPAM

Having installed EasyCrypt's dependencies and at least one suitable
SMT solver, you may still want to [install EasyCrypt from
source](#installing-easycrypt-from-source)—even if you used
OPAM for the rest. This can be useful if you want more direct control
over the version of EasyCrypt you're using.

Otherwise, to install EasyCrypt via OPAM, run the following command:

```
opam install easycrypt
```

If everything went according to plan, you now have everything you need to
run EasyCrypt! But before you get ahead of yourself, make sure to complete the
[(post-installation) setup and configuration](#setup-and-configuration) to
ensure everything works as expected.

## Via Nix

> **Note:** As this is not the recommended installation method and is
> considered more advanced, we don't go into much detail here.
> If you are looking for a more guided installation
> process, consider [installing via OPAM](#via-opam-recommended) instead.

Ensure you have [Nix's package manager](https://nixos.org/) installed.
You can do so by following [the official installation guide](https://nixos.org/manual/nix/stable/#chap-installation).

Next, clone or download this repository and navigate to its root.

At this point, you have a few options.
Find the item that best matches your situation
and expand the corresponding section to view the relevant
instructions.

<details>

<summary>Build EasyCrypt without SMT solvers</summary>

To build EasyCrypt without any SMT solvers, run the following command:

```
make nix-build
```

Once the build is complete, you'll find the EasyCrypt binary
in the `result/bin` directory.

</details>

<details>

<summary>Build EasyCrypt along with a set of SMT solvers</summary>

To build EasyCrypt along with a set of SMT solvers, run the following command:

```
make nix-build-with-provers
```

Once the build is complete, you'll find the EasyCrypt binary
in the `result/bin` directory.

</details>

<details>

<summary>Setup a development environment with all required dependencies and SMT solvers</summary>
  To setup a development environment, run the following command:

  ```
  make nix-develop
  ```

  This installs all required dependencies and SMT solvers, and drops you in a
  shell afterward. From there, run `make` to build EasyCrypt.

</details>

## From Source

> **Note:** As this is not the recommended installation method and is
> considered more advanced, we don't go into much detail here and primarily
> refer to external sources. If you are looking for a more guided installation
> process, consider [installing via OPAM](#via-opam-recommended) instead.

### Installing EasyCrypt's Dependencies From Source

EasyCrypt uses the following third-party tools/libraries:

- [OCaml](https://github.com/ocaml/ocaml), version >= 4.08 and < 5.0
  Further useful resources:
  - <https://ocaml.org/install>.
- [OCamlbuild](https://github.com/ocaml/ocamlbuild)  
- [Why3](https://gitlab.inria.fr/why3/why3), version 1.8 and < 1.9
  Why3's libraries are required as well (typically installed by running something like `make byte && make install-lib`).
  Although not a strict dependency, you may want to already install
  [some of the compatible SMT solvers](#compatible) as well (you'll need at least one in the end.)
  Further useful resources:
  - <https://www.why3.org/>
  - <https://www.why3.org/#provers>
- [Menhir](https://gitlab.inria.fr/fpottier/menhir/)  
  Further useful resources:
  - <https://gallium.inria.fr/~fpottier/menhir/>
- [Caml Batteries Included](http://batteries.forge.ocamlcore.org/)
- OCaml PCRE, version >= 7 <https://github.com/mmottl/pcre-ocaml>
- OCaml Zarith <https://forge.ocamlcore.org/projects/zarith>
- OCaml ini-files, version >= 1.2 <http://archive.ubuntu.com/ubuntu/pool/universe/o/ocaml-inifiles/>

### Installing EasyCrypt From Source

If installing from source, running

```
make
make install
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

After [installing EasyCrypt and its dependencies](#installation), some
additional setup and configuration are required to ensure everything works
properly. First, if you haven't yet installed
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

EasyCrypt currently depends on Why3 version 1.8, which supports the following
versions of SMT solvers:

* [Alt-Ergo](https://alt-ergo.ocamlpro.com/), version 2.5.2
* [CVC4](https://cvc4.github.io/), version 1.8
* [CVC5](https://cvc5.github.io/), version 1.0.8
* [Z3](https://github.com/Z3Prover/z3), version 4.12.x

Alt-Ergo is available via OPAM. To install version 2.5.2, run the following command:

```
opam install alt-ergo.2.5.2
```

If you've installed a different version of Alt-Ergo, you can switch to version
2.5.2 by running `opam pin alt-ergo 2.5.2`.

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

EasyCrypt does not remember custom configuration paths. Unless
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

Coming soon.


# Useful Resources

---

## Examples

Examples of how to use EasyCrypt are in the `examples` directory. You
will find basic examples at the root of this directory, as well as a
more advanced example in the `MEE-CBC` sub-directory and a tutorial on
how to use the complexity system in `cost` sub-directory.
