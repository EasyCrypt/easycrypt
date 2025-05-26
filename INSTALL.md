# Installation

---

There are several ways to install EasyCrypt and its dependencies.
The recommended method is to [use OPAM](#via-opam-recommended), a package
manager for OCaml (the programming language EasyCrypt is written in).
Other installation methods include [using Nix](#via-nix)
and [directly from source](#from-source). Whichever
method you choose, be sure to follow the
[(post-installation) setup and configuration instructions](README.md#setup-and-configuration)
afterward!

> **Note:** We maintain a [list of known installation quirks
> and corresponding troubleshooting tips](https://github.com/EasyCrypt/easycrypt/wiki/%5BSetup%5D-Installation-Quirks). 
> If you encounter any issues during installation, be sure to consult that document for assistance.

## Table of Contents

- [Installation](#installation)
  - [Via OPAM (Recommended)](#via-opam-recommended)
    - [Installing and Initializing OPAM](#installing-and-initializing-opam)
    - [Installing EasyCrypt's Dependencies via OPAM](#installing-easycrypts-dependencies-via-opam)
    - [Installing EasyCrypt via OPAM](#installing-easycrypt-via-opam)
  - [Via Nix](#via-nix)
  - [From Source](#from-source)
    - [Installing EasyCrypt's Dependencies Manually](#installing-easycrypts-dependencies-manually)
    - [Installing EasyCrypt From Source](#installing-easycrypt-from-source)

## Via OPAM (Recommended)

Installation via OPAM consists of three steps:
1. [Installing and Initializing OPAM](#installing-and-initializing-opam)
2. [Installing EasyCrypt's Dependencies via OPAM](#installing-easycrypt-via-opam)
3. [Installing EasyCrypt via OPAM](#installing-easycrypt-via-opam)

If you already have a working installation of OPAM on your system, you can skip ahead
and start with [installing EasyCrypt's dependencies via OPAM](#installing-easycrypts-dependencies-via-opam).

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
(Depending on your system, the package names may vary slightly).

To launch OPAM's script, run

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

After installing OPAM, initialize it by running

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
contains a single [switch](https://ocaml.org/docs/opam-switch-introduction).
A switch is OPAM's take on an isolated environment, similar to Python's `virtualenv`.
To avoid conflicts with your EasyCrypt installation, it's recommended to create a dedicated switch.

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

Let OPAM detect and install EasyCrypt's dependencies by running:

```
opam install --deps-only easycrypt
```

If your OPAM version is **2.1 or higher**, this command will also detect
and install any missing *system* dependencies. In this case,
you may be prompted to install these dependencies via your
system's package manager or some other appropriate mechanism.
Be sure to read the output carefully and follow any instructions!

Finally, install at least one
[SMT solver compatible with the current version of Why3 used by EasyCrypt](README.md#compatibility).
A common choice is Alt-Ergo, which is conveniently packaged by OPAM.
Although it's not a direct dependency of EasyCrypt (and you're free
to use a different compatible SMT solver), the simplest option is to
install the correct version of Alt-Ergo via OPAM by running

```
opam install alt-ergo.2.6.0
```

(If you accidentally installed a different version of Alt-Ergo, you can change
to version 2.6.0 by running `opam pin alt-ergo 2.6.0`)

At this point, you can proceed to [install EasyCrypt](#installing-easycrypt-via-opam).
However, if you wish, you can also install additional SMT solvers.
This allows you to pick and choose between multiple solvers, or use them simultaneously.
A list of compatible solvers is available [below](README.md#compatibility).

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
[(post-installation) setup and configuration](README.md#setup-and-configuration) to
ensure everything works as expected.

## Via Nix

> **Note:** As this is not the recommended installation method and is
> considered more advanced, we don't go into much detail here.
> If you are looking for a more guided installation
> process, consider [installing via OPAM](#via-opam-recommended) instead.

First, ensure you have [Nix's](https://nixos.org/) package manager installed.
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

### Installing EasyCrypt's Dependencies Manually

> **Note:** If you only want to install EasyCrypt *itself* from source but prefer
> to install *its dependencies* automatically, consider following the
> [OPAM-based installation instructions](#via-opam-recommended) up to and including
> [the installation of EasyCrypt's dependencies](installing-easycrypts-dependencies-via-opam),
> then proceed to [install Easycrypt from source](#installing-easycrypt-from-source).

The following is a list of all the dependencies required to build and run
EasyCrypt. For each dependency, we provide some installation resources along
with any relevant details or caveats. Once all dependencies are installed,
proceed to [install EasyCrypt from Source](#installing-easycrypt-from-source).

- [OCaml](https://ocaml.org/install/) (version >= 4.08 and < 5.0)  
  Additional resources:
  - <https://github.com/ocaml/ocaml>.
- [OCamlbuild](https://github.com/ocaml/ocamlbuild/)
- [Git](https://git-scm.com/downloads)
- [Why3](https://www.why3.org/) (version >= 1.8 and < 1.9)  
  You also need to install Why3's libraries (typically by running `make byte && make install-lib`).
  Further, you might already want to install at least one [compatible SMT solver](README.md#compatibility).  
  Additional resources:
  - <https://www.why3.org/#provers>
  - <https://gitlab.inria.fr/why3/why3>
- [Menhir](https://gallium.inria.fr/~fpottier/menhir/)  
  Additional resources:
  - <https://gitlab.inria.fr/fpottier/menhir>
- [OCaml Batteries Included](https://ocaml-batteries-team.github.io/batteries-included/hdoc2/) (version >= 3)  
  Additional resources:
  - <https://github.com/ocaml-batteries-team/batteries-included>
  - <http://batteries.forge.ocamlcore.org>
- [OCaml PCRE](https://github.com/mmottl/pcre-ocaml/) (version >= 7)
- [OCaml Zarith](https://github.com/ocaml/Zarith/) (version >= 1.10)  
  Additional resources:
  - <https://forge.ocamlcore.org/projects/zarith>
- [OCaml ini-files](https://opam.ocaml.org/packages/ocaml-inifiles/) (version >= 1.2)  
  Additional resources:
  - http://archive.ubuntu.com/ubuntu/pool/universe/o/ocaml-inifiles
- [Python3](https://www.python.org/downloads)  
  You also need to install the following libraries:
  - [Python3 YAML](https://pyyaml.org/wiki/PyYAMLDocumentation)
  - [Python3 Curses](https://docs.python.org/3/library/curses.html#module-curses)  
    *Note: This might already be included with your Python installation. If so, you do not need to install it separately.*

### Installing EasyCrypt From Source

Having installed EasyCrypt's dependencies, you can build and install
EasyCrypt from source as follows.

First, clone or download the repository (e.g., by running `git clone https://github.com/EasyCrypt/easycrypt.git`)
and navigate to its root.

Then, to build EasyCrypt, run

```
make
```

After the build completes, a symbolic link to the EasyCrypt binary (`ec.native`) will
have been created in the repository's root directory. (The actual binary will be located at `src/ec.exe`.)
You can use this symbolic link directly anywhere an EasyCrypt binary is expected.
If this is sufficient for your use, proceed to [the (post-installation) setup and configuration](README.md#setup-and-configuration).
However, if you prefer a system-wide installation, run

```
make install
```

Once installed, proceed to [the (post-installation) setup and configuration](README.md#setup-and-configuration).
