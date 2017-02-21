Installing requirements
====================================================================

EasyCrypt uses the following third-party tools/libraries:

 * OCaml (>= 4.02)

     Available at http://caml.inria.fr/

 * OCamlbuild (only for OCaml >= 4.03)

 * Why3 (>= 0.87)

     Available at <http://why3.lri.fr/>

     Why3 must be installed with a set a provers.
     See <http://why3.lri.fr/#provers>

     Why3 libraries must be installed (make byte && make install-lib)

 * Menhir <http://gallium.inria.fr/~fpottier/menhir/>

 * OCaml Batteries Included <http://batteries.forge.ocamlcore.org/>
 
 * OCaml PCRE (>= 7) <https://github.com/mmottl/pcre-ocaml>

 * OCaml ZArith <https://forge.ocamlcore.org/projects/zarith>

On POSIX systems (GNU/Linux, *BSD, OS-X), we recommend people to
install EasyCrypt and all its dependencies via `opam`.


Installing requirements using OPAM (POSIX systems)
--------------------------------------------------------------------

Starting with opam 1.2.0, you can install all the needed dependencies
via the opam OCaml packages manager.

  0. Optionally, switch to a dedicated compiler for EasyCrypt:

        $> opam switch -A $OVERSION easycrypt

     where $OVERSION is a valid OCaml version (e.g. 4.02.1)

  1. Add the EasyCrypt repository:

        $> opam repository add easycrypt git://github.com/EasyCrypt/opam.git
        $> opam update
        
  2. Add the EasyCrypt meta-packages:

        $> opam install --deps-only easycrypt
        $> opam install ec-provers

Opam can be easily installed from source or via your packages manager:

  * On Ubuntu and derivatives:
  
        $> add-apt-repository ppa:avsm/ppa
        $> apt-get update
        $> apt-get install ocaml ocaml-native-compilers camlp4-extra opam
        
  * On MacOSX using brew:

        $> brew install ocaml opam

See [https://opam.ocaml.org/doc/Install.html] for how to install opam.

See [https://opam.ocaml.org/doc/Usage.html] for how to initialize opam


Configuring Why3
====================================================================

Before running EasyCrypt and after the installation/removal/update
of an SMT prover, you need to (re)configure Why3.

By EasyCrypt is using the default Why3 location, i.e. ~/.why3.conf,
or _tools/why3.local.conf when it exists. If you have several versions
of Why3 installed, it may be impossible to share the same configuration
file among them. EasyCrypt via the option -why3, allows you to load a
Why3 configuration file from a custom location. For instance:

       $> why3 config --detect -C $WHY3CONF.conf
       $> ./ec.native -why3 $WHY3CONF.conf


Installing/Compiling EasyCrypt
====================================================================

If installing from source, running

        $> make
        $> make install

builds and install EasyCrypt (under the binary named `easycrypt`),
assuming that all dependencies have been successfully installed. If
you choose not to install EasyCrypt system wide, you can use the
binary `ec.native` that is located at the root of the source tree.

It is possible to change the installation prefix by setting the
environment variable PREFIX:

        $> make PREFIX=/my/prefix install


EasyCrypt comes also with an opam package. Running

      $> opam install easycrypt

installs EasyCrypt and its dependencies via opam. In that case, the
EasyCrypt binary is named `easycrypt`.


Proof General Front-End
====================================================================

Installing using opam
--------------------------------------------------------------------

If you installed the EasyCrypt dependencies using opam, you can
install ProofGeneral via opam too. Running

      $> opam install proofgeneral

installs ProofGeneral along with its EasyCrypt mode. You still have to
tweak your emacs configuration file (~/.emacs) to load
ProofGeneral by adding the following line to it

        (load-file "$proof-general-home/generic/proof-site.el")

where $proof-general-home should be replaced by

        $prefix/share/proofgeneral/generic/proof-site.el

with $prefix being set to the output of

        $> opam config var prefix

Installing from sources
--------------------------------------------------------------------

EasyCrypt mode has been integrated upstream. Please, go to
<https://github.com/ProofGeneral/PG> and follow the instructions.
