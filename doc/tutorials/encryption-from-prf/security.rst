Defining Security
=================

Now that we have a scheme, we can define its security. For the time
being, EasyCrypt exclusively allows exact—rather than
asymptotic—security definitions. As such, we will only consider exact
security definitions. Furthermore, we will be a bit more generic than
necessary, starting with a definition of security for *any* symmetric
nonce-based encryption scheme, not just for the particular scheme we are
currently interested in. As alluded to before, in general, we aim to be
rather generic when formalizing and proving security in EasyCrypt. The
reason for this is that, if done properly, this can significantly
increase (and cannot decrease) the strength and reusability of the
result. Nevertheless, at this point, we will keep things somewhat more
concrete than usual for clarity purposes. Later on, we will cover
writing and reusing fully generic proof components.

IND$-NRCPA Security for Symmetric Nonce-Based Encryption Schemes, Pen-and-Paper
-------------------------------------------------------------------------------

For the security property, we consider INDistinguishability from RANDOM
ciphertexts under Nonce-Respecting Chosen-Plaintext Attacks
(IND$-NRCPA): An adversary with access to a chosen-plaintext
oracle—which takes a nonce and plaintext as input, outputs a ciphertext,
and does not allow for repeating nonces—should not be able to
distinguish (except with a “small” probability) the actual encryption
scheme with a fixed and properly generated secret key from an oracle
that returns freshly and uniformly sampled ciphertexts. Intuitively,
this property captures the extent to which the ciphertexts of a
(symmetric nonce-based) encryption scheme can be distinguished from
uniformly random ciphertexts: The smaller this extent, the better the
security of the scheme. For defining this indistinguishability property,
it’s crucial to ensure that nonces are not used more than once, as this
could trivially break security; indeed, if we would not impose this
restriction, the adversary could distinguish by simply reusing a nonce.

More formally, consider the two oracles shown below,
:math:`\mathcal{O}^{CPA\textrm{-}real}_{\Sigma}` (which is defined with
respect to an abstract symmetric nonce-based encryption scheme
:math:`\Sigma`, instantiable by any concrete such scheme) and
:math:`\mathcal{O}^{CPA\textrm{-}ideal}`.

.. math::


   \begin{align*}
   \begin{align*}
   & \underline{\smash{\mathcal{O}^{CPA\textrm{-}real}_{\Sigma}}}\\
   & \begin{align*}
     & \underline{\smash{\mathsf{init}()}}\\
     & \left\lfloor~
       \begin{align*}
       & k \operatorname{\smash{\overset{\$}{\leftarrow}}} \Sigma.\mathsf{KGen}()\\
       & \mathrm{log} \leftarrow [\ ]
       \end{align*}
       \right.
     \end{align*}
   \\
   & \begin{align*}
     & \underline{\smash{\mathsf{enc}(n, m)}}\\
     & \left\lfloor~
       \begin{align*}
       & \textsf{if}\ n \notin \mathrm{log}\\
       & \left\lfloor~
         \begin{align*}
         & \mathrm{log} \leftarrow n\ ||\ \mathrm{log}\\
         & c \leftarrow \Sigma.\mathsf{Enc}(k, n, m)\\
         & \textsf{return}\ c
         \end{align*}
         \right.\\
       & \textsf{else}\\
       & \left\lfloor~
         \begin{align*}
         & \textsf{return}\ \bot
         \end{align*}
         \right.
       \end{align*}
       \right.
     \end{align*}
   \end{align*}
   &&&&&&&&
   \begin{align*}
   & \underline{\smash{\mathcal{O}^{CPA\textrm{-}ideal}}}\\
   & \begin{align*}
     & \underline{\smash{\mathsf{init}()}}\\
     & \left\lfloor~
       \begin{align*}
       & \\
       & \mathrm{log} \leftarrow [\ ]
       \end{align*}
       \right.
     \end{align*}
     \\
     & \begin{align*}
     & \underline{\smash{\mathsf{enc}(n, m)}}\\
     & \left\lfloor~
       \begin{align*}
       & \textsf{if}\ n \notin \mathrm{log}\\
       & \left\lfloor~
         \begin{align*}
         & \mathrm{log} \leftarrow n\ ||\ \mathrm{log}\\
         & c \operatorname{\smash{\overset{\$}{\leftarrow}}} \mathcal{U}_{\mathcal{C}}\\
         & \textsf{return}\ c
         \end{align*}
         \right.\\
       & \textsf{else}\\
       & \left\lfloor~
         \begin{align*}
         & \textsf{return}\ \bot
         \end{align*}
         \right.
       \end{align*}
       \right.
       \end{align*}
     \end{align*}
   \end{align*}

Evidently, these oracles are extremely similar: The only difference
between the two concerns the creation of ciphertexts (and the
corresponding initialization differences). Then, we capture the
“insecurity” of a (symmetric nonce-based) encryption scheme
:math:`\Sigma` against a nonce-respecting chosen-plaintext distinguisher
:math:`\mathcal{D}`—i.e., a (potentially probabilistic) algorithm
:math:`\mathcal{D}` with the appropriate interface—as the (absolute)
difference between the likelihood of (1) :math:`\mathcal{D}` outputting
:math:`\texttt{true}` when given access to (the :math:`\mathsf{enc}`
procedure of) :math:`\mathcal{O}^{CPA\textrm{-}real}_{\Sigma}` and (2)
:math:`\mathcal{D}` outputting :math:`\texttt{true}` when given access
to (the :math:`\mathsf{enc}` procedure of)
:math:`\mathcal{O}^{CPA\textrm{-}ideal}`. Conceptually, the truth value
output by the distinguisher can be interpreted as the distinguisher’s
“guess” of which oracle it was given. In general terms, this (absolute)
difference is often called *the advantage of :math:`\mathcal{D}` in
distinguishing :math:`\Sigma` from random*; however, since we have
already established a slick name for the exact security property, we
will be more precise and refer to it as *the advantage of
:math:`\mathcal{D}` against IND$-NRCPA of :math:`\Sigma`*.
Mathematically, this advantage is expressed as follows.

.. math::


   \mathsf{Adv}^{\mathrm{IND\$\textrm{-}NRCPA}}_{\Sigma}(\mathcal{D})
   = \left|\mathsf{Pr}\left[\mathsf{Exp}^{\mathrm{IND\$\textrm{-}NRCPA}}_{\mathcal{D}, \mathcal{O}^{CPA\textrm{-}real}_{\Sigma}} = 1\right]
   - \mathsf{Pr}\left[\mathsf{Exp}^{\mathrm{IND\$\textrm{-}NRCPA}}_{\mathcal{D}, \mathcal{O}^{CPA\textrm{-}ideal}} = 1\right]\right|

Here, the experiment

.. math:: \mathsf{Exp}^{\mathrm{IND\$\textrm{-}NRCPA}}_{\mathcal{D}, \mathcal{O}}

\ is defined below. This experiment is rather straightforward: It
initializes the given oracle, runs the distinguisher while providing
access to the :math:`\mathsf{enc}` function of the oracle, and directly
outputs the return value received from the distinguisher.

.. math::


   \begin{align*}
   & \underline{\smash{\mathsf{Exp}^{\mathrm{IND\$\textrm{-}NRCPA}}_{\mathcal{D}, \mathcal{O}}}}\\
   & \left\lfloor
     \begin{align*}
     & \mathcal{O}.\mathsf{init}()\\
     & b \operatorname{\smash{\overset{\$}{\leftarrow}}} \mathcal{D}^{\mathcal{O}.\mathsf{enc}}.\mathsf{distinguish}()\\
     & \textsf{return}\ b
     \end{align*}
     \right.
   \end{align*}

Surely, with these oracle and game definitions,

.. math:: \mathsf{Adv}^{\mathrm{IND\$\textrm{-}NRCPA}}_{\Sigma}(\mathcal{D})

matches the intuitive description of insecurity we gave earlier. Namely,
because

.. math:: \mathsf{Exp}^{\mathrm{IND\$\textrm{-}NRCPA}}_{\mathcal{D}, \mathcal{O}^{CPA\textrm{-}real}_{\Sigma}}

and

.. math:: \mathsf{Exp}^{\mathrm{IND\$\textrm{-}NRCPA}}_{\mathcal{D}, \mathcal{O}^{CPA\textrm{-}ideal}}

merely differ in the oracle they provide to :math:`\mathcal{D}`, a
difference in probability of :math:`\mathcal{D}` outputting a certain
truth value (arbitrarily chosen to be 1, or :math:`\texttt{true}`, here)
between the experiments must be a consequence of distinguishing the
oracles somehow. Certainly, this is precisely what

.. math::

   \left|\mathsf{Pr}\left[\mathsf{Exp}^{\mathrm{IND\$\textrm{-}NRCPA}}_{\mathcal{D}, \mathcal{O}^{CPA\textrm{-}real}_{\Sigma}} = 1\right] -
   \mathsf{Pr}\left[\mathsf{Exp}^{\mathrm{IND\$\textrm{-}NRCPA}}_{\mathcal{D}, \mathcal{O}^{CPA\textrm{-}ideal}} = 1\right]\right|

captures.

Finally, we say that a (symmetric nonce-based encryption) scheme
:math:`\Sigma` is IND$-NRCPA secure if, for any nonce-respecting
chosen-plaintext adversary :math:`\mathcal{D}`,

.. math:: \mathsf{Adv}^{\mathrm{IND\$\textrm{-}NRCPA}}_{\Sigma}(\mathcal{D})

\ is “small”. Because we exclusively consider exact security, “small”
essentially means “bounded by other *concrete values/probabilities* that
we believe are small in practice”.

To directly read further on the security definitions of PRFs for the pen
and paper setting, jump
`here <#nonce-respecting-pseudo-random-function-family-property-pen-and-paper>`__.

IND$-NRCPA Security for Symmetric Nonce-Based Encryption Schemes, EasyCrypt
---------------------------------------------------------------------------

To formalize the above-discussed oracles, adversary class, and
experiment in EasyCrypt, we will make use of `module types and
modules </docs/reference#module-types-modules-and-procedures>`__, as
well as several libraries from the *standard library*. Specifically, we
will make use of the ``AllCore.ec``, ``List.ec``, and ``Distr.ec``
libraries for the definitions and properties of basic concepts, lists,
and distributions, respectively. To have those theories available, we
issue the following command at the beginning of the file.

::

   require import AllCore List Distr.

The keyword ``require`` loads the content of a library and the
``import`` keyword makes all the symbols available without
qualification. For more information regarding loading and importing,
`click here </docs/reference#loading-and-importing-libraries>`__.

NRCPA Oracle Type
~~~~~~~~~~~~~~~~~

Before formalizing the oracles, we will formalize their type. From the
pen-and-paper definition of the oracles, we can see that they implement
two algorithms:

.. math:: \mathsf{init()}

\ and

.. math:: \mathsf{enc}(n, m)

, where

.. math:: n

is a nonce,

.. math:: m

is a plaintext, and

.. math:: \mathsf{enc}(n, m)

outputs either a valid ciphertext or an indication of failure (

.. math:: \bot

). The module type that captures this is shown below.

::

   module type NRCPA_Oraclei = {
     proc init() : unit
     proc enc(n : nonce, m : ptxt) : ctxt option
   }.

Here, notice that the procedures’ output types. First, the output type
of ``init`` is ``unit``, which is a built-in type that only contains a
single value. Among others, this type is used as the type of the return
value of procedures that do not return an actual value. Certainly, we do
not expect the initialization procedure of a NRCPA oracle to return
anything; as such, we use ``unit`` to denote its output type. Second,
the output type of ``enc`` is ``ctxt option`` (instead of the ``ctxt``
type you might have expected). ``option`` is an example of a *type
constructor* (as is ``distr``, which we briefly mentioned
`earlier <context#defining-the-basics-easycrypt>`__). Such constructors
can be used to construct types by instantiating them (using prefix
notation) with already-existing types. In the specific case of
``option``, any type—say ``t``—can be used to create a corresponding
option type that is denoted by ``t option``. This option type contains a
value ``Some x`` for each value ``x`` of type ``t``, and an additional
value ``None``. In the formalization of the oracles, we use the
``ctxt option`` type as a convenient way to let ``enc`` return either a
valid ciphertext (as ``Some c`` where ``c`` is a ciphertext) or an
indication of failure (as ``None``).

Real NRCPA Oracle
~~~~~~~~~~~~~~~~~

Next, we formalize

.. math:: \mathcal{O}^{CPA\textrm{-}real}_{\Sigma}

, the real oracle. Particularly, we do so using a module of type
``NRCPA_Oraclei``. However, in contrast to the encryption scheme we
formalized as a module
`before <context#defining-the-scheme-easycrypt>`__,

.. math:: \mathcal{O}^{CPA\textrm{-}real}_{\Sigma}

is defined with respect to some other entity :math:`\Sigma` from a
certain class; in this case, this is the class of symmetric nonce-based
encryption schemes. In EasyCrypt, we formalize this using a so-called
`functor or higher-order
module </docs/reference#higher-order-modules-and-module-types>`__—i.e.,
a module parameterized on other module(s)—that takes a module of the
type that represents this class; indeed, here this is the
`previously-defined <context#defining-the-scheme-easycrypt>`__
``NBEncScheme`` module type. So, we can formalize

.. math:: \mathcal{O}^{CPA\textrm{-}real}_{\Sigma}

as follows.

::

   module O_NRCPA_real (S : NBEncScheme) : NRCPA_Oraclei = {
     var k : key
     var log : nonce list
     
     proc init() : unit = {
       k <@ S.kgen();
       
       log <- [];
     }

     proc enc(n : nonce, m : ptxt) : ctxt option = {
       var c : ctxt;
       var r : ctxt option;

       if (! (n \in log)) {
         log <- n :: log;
         
         c <@ S.enc(k, n, m);
         
         r <- Some c;
       } else {
         r <- None;
       }
       
       return r;
     }
   }.

Intuitively, the definition of ``O_NRCPA_real`` can be interpreted as
follows: Given any scheme ``S`` that implements the expected procedures
(or minimal syntax) of a symmetric nonce-based encryption scheme, we can
construct a NRCPA oracle by implementing the expected procedures (or
minimal syntax) in the following way, using (the expected procedures of)
``S``. Certainly, this means that the procedures of ``O_NRCPA_real`` can
formally only be given a meaning (and, hence, be referred/called from
other code) if the module parameter is instantiated. In other words,
``O_NRCPA_real.init`` and ``O_NRCPA_real.enc`` are not well-defined
procedures, but ``O_NRCPA_real(M).init`` and ``O_NRCPA_real(M).enc`` are
(where ``M`` is a module of type ``NBEncScheme``). Contrarily, the
module variables of ``O_NRCPA_real`` (i.e., ``k`` and ``log``) are
independent of the instantiation of its module parameter: there is only
ever one ``O_NRCPA_real.k`` and one ``O_NRCPA_real.log``, even if
``O_NRCPA_real`` is instantiated multiple times with different modules.
Therefore, it is possible to refer to ``O_NRCPA_real.k`` and
``O_NRCPA_real.log``, but not to ``O_NRCPA_real(M).k`` and
``O_NRCPA_real(M).log`` (again, where ``M`` is a module of type
``NBEncScheme``).

:::note From pen-and-paper to computer Looking at the actual code of
``O_NRCPA_real``, we can see that it is a relatively straightforward
translation from the pen-and-paper definition of which the novel
concepts may seem rather self-explanatory. Regardless, we briefly go
over these concepts for clarity and completeness. + ``list`` is a type
constructor (defined in ``List.ec``) that can be used to construct the
type of lists over a certain type. In other words, for any type ``t``,
``t list`` is the type of lists containing elements of type ``t``. +
``[]`` is a value (defined in ``List.ec``) that denotes the empty list.
+ ``\in`` is an abbreviation (defined in ``List.ec``) that can be used
an infix operator, and checks whether the left-hand side operand (of
some type, say ``t``) is an element of the right-hand side operand (of
type ``t list``). + ``::`` is an infix operator (defined in ``List.ec``)
that prepends the left-hand side operand (of some type, say ``t``) to
the right-hand side operand (of type ``t list``). + In EasyCrypt,
procedures can only have a single return statement. The main reason for
this is to keep the complexity of the program logics (used for proofs)
somewhat in check. For this reason, to formalize procedures that contain
multiple return statements, we accordingly replace all return statements
by assignments to a return variable and a single return statement at the
end. :::

Ideal NRCPA Oracle
~~~~~~~~~~~~~~~~~~

Having dealt with the formalization of

.. math:: \mathcal{O}^{CPA\textrm{-}real}_{\Sigma}

, we continue with the formalization of

.. math:: \mathcal{O}^{CPA\textrm{-}ideal}

. Certainly, as one would expect from the pen-and-paper definitions, the
latter essentially only differs from the former in that it samples
ciphertexts uniformly at random instead of legitimately generating them
(i.e., via an actual encryption scheme). As a result, the module
formalizing the ideal oracle does not need to be parameterized on
another module (representing an actual encryption scheme), nor does it
need to maintain a secret key. However, it does require a uniform
distribution over the complete ciphertext space to sample from. So,
before formalizing the oracle, we need to define this distribution; we
do so as follows.

::

   op [lossless full uniform] dctxt : ctxt distr.

In this code, we define a (sub)distribution ``dctxt`` over the ``ctxt``
type, similar to how we defined the (sub)distribution ``dkey`` over the
``key`` type `before <context#defining-the-basics-easycrypt>`__.
However, in contrast to ``dkey``, ``dctxt`` is assumed to have several
properties, each of which is denoted by one of the keywords in the
square brackets. First, we assume ``dctxt`` to be ``lossless``; that is,
we assume ``dctxt`` is proper distribution (the sum of its probabilities
exactly equals 1). Second, we assume ``dctxt`` to be ``full``; that is,
we assume ``dctxt`` assigns a non-zero probability to each value of type
``ctxt``. Lastly, we assume ``dctxt`` to be ``uniform``; that is, we
assume ``dctxt`` assigns either a probability of 0 or a constant
probability to each value of type ``ctxt`` (this constant probability is
the same for all values). Note that the combination of the ``full`` and
``uniform`` properties mean that ``dctxt`` assigns the same non-zero
probability to each value of type ``ctxt``. Adding the ``lossless``
property on top of this results in ``dctxt`` assigning each value of
type ``ctxt`` a probability of

.. math:: 1 / \left| \mathcal{C} \right|

(where

.. math:: \left| \mathcal{C} \right|

denotes the cardinality of the ciphertext space). In other words,
combining the ``lossless``, ``full``, and ``uniform`` properties results
in the distribution that is usually referred to as the “uniform
distribution”. For more information about distributions in EasyCrypt,
`click here </docs/reference#distributions>`__.

Having the required ciphertext distribution at our disposal, we can go
ahead and formalize the ideal oracle. As mentioned before, this
formalization is essentially identical to the formalization of the real
oracle, merely replacing the legitimate generation of ciphertexts by the
appropriate sampling operation (and, of course, removing anything
related to the legitimate generation of ciphertext, as this is
redundant). More precisely, we formalize

.. math:: \mathcal{O}^{CPA\textrm{-}ideal}

\ as the module given below.

::

   module O_NRCPA_ideal : NRCPA_Oraclei = {
     var log : nonce list

     proc init() : unit = {
       log <- [];
     }

     proc enc(n : nonce, m : ptxt) : ctxt option = {
       var c : ctxt;
       var r : ctxt option;
       
       if (! (n \in log)) {
         log <- n :: log;
         
         c <$ dctxt;
         
         r <- Some c;
       } else {
         r <- None;
       }
       
       return r;
     }
   }.

IND$-NRCPA Experiment and Security
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

At this point, it remains to formalize the considered class of
adversaries and security experiment before finally being able to
formalize the security property of a (symmetric nonce-based) encryption
scheme :math:`\Sigma`.

Starting off, recall that a class of adversaries contains any (possibly
probabilistic) algorithm that implements a certain interface,
potentially requiring access to a number of oracles. Notice that if we
would be able to specify access to modules of other types in a module
type, adversary classes (with potential oracle access) could easily be
formalized using module types. Namely, the only requirement for a module
``A`` to be of a certain module type ``AT`` is that ``A`` implements the
procedures defined by ``AT``; otherwise, there are no restrictions on
``A``. Indeed, this precisely matches our concept of (a class of)
adversaries: All algorithms that satisfy the expected interface
constitute valid adversaries and, hence, belong to the considered class
of adversaries. So, to formalize a class of adversaries that do not
expect access to any oracle, it suffices to use module types as we have
already gone over before. However, to formalize a class of adversaries
that does expect access to an oracle(s), we require some additional
functionality. Fortunately, EasyCrypt allows for module types that, in
addition to specifying a set of procedures that is to be implemented,
also indicate a sequence of module parameter(s), so-called `functor
types or higher-order module
types </docs/reference#higher-order-modules-and-module-types>`__.

Applying the above to our currently case, we first create a module type
formalizing the interface of the NRCPA oracles provided *to the
adversaries*. This is necessary because ``NRCPA_Oraclei``, the module
type formalizing the interface of the NRCPA oracles given *to the
experiment*, include the ``init`` procedure, which we do not want to
expose to the adversaries. Therefore, we create a separate module type
for the oracles actually given to the adversary; indeed, this type
should only specify the ``enc`` procedure of the ``NRCPA_Oraclei`` type.
Luckily, EasyCrypt allows for the direct inclusion of procedure
signatures from other module types, so we do not have to copy-paste; see
the snippet below.

::

   module type NRCPA_Oracle = {
     include NRCPA_Oraclei [enc]
   }.

Using this newly defined module type, we can formalize the class of
adversaries with a module type as follows.

::

   module type Adv_IND_NRCPA (O : NRCPA_Oracle) = {
     proc distinguish() : bool
   }.

Intuitively, the ``Adv_IND_NRCPA`` module type encompasses all modules
that expect a module of type ``NRCPA_Oracle`` and, *after* being given
such a module, implement ``distinguish`` procedure that takes no input
and outputs a value of type ``bool`` (i.e., a boolean).

Based on the above, we can formalize the IND$-NRCPA experiment/game,
which is nothing more than a (probabilistic) program that is defined
with respect to a NRCPA oracle and an IND$-NRCPA adversary. In EasyCrypt
terms, the IND$-NRCPA experiment/game is a module that takes two module
parameters: one of type ``NRCPA_Oraclei`` and one of type
``Adv_IND_NRCPA``. Here, a technicality is that—because EasyCrypt allows
code to be written exclusively inside of procedures—we must encapsulate
the actual code of the experiment/game in a procedure (which we
arbitrarily name ``run``), even though there is no corresponding
(explicit) procedure/algorithm signature in the pen-and-paper
definition. Otherwise, the formalization, provided in the following
snippet, is a verbatim translation of the pen-and-paper definition.

::

   module Exp_IND_NRCPA (O : NRCPA_Oraclei) (D : Adv_IND_NRCPA) = {
     proc run() : bool = {
       var b : bool;

       O.init();
       
       b <@ D(O).distinguish();
       
       return b;
     }
   }.

At last, we can express the advantage of an (IND$-NRCPA) adversary
:math:`\mathcal{D}` against IND$-NRCPA of a symmetric nonce-based
encryption scheme :math:`\Sigma`. Recall that the pen-and-paper
definition of this advantage is the following.

.. math::


   \mathsf{Adv}^{\mathrm{IND\$\textrm{-}NRCPA}}_{\Sigma}(\mathcal{D})
   = \left|\mathsf{Pr}\left[\mathsf{Exp}^{\mathrm{IND\$\textrm{-}NRCPA}}_{\mathcal{D}, \mathcal{O}^{CPA\textrm{-}real}_{\Sigma}} = 1\right]
   - \mathsf{Pr}\left[\mathsf{Exp}^{\mathrm{IND\$\textrm{-}NRCPA}}_{\mathcal{D}, \mathcal{O}^{CPA\textrm{-}ideal}} = 1\right]\right|

Formally, these probability expressions are not fully defined unless the
initial memory/context is fixed. More precisely, the experiment only
defines a distribution over its (state and) output value—which allows us
to talk about things such as the probability of the output of the
experiment being 1—if the initial memory is fixed; otherwise, it would
define a set of distributions (one distribution for each possible
initial memory). To keep flexibility in reasoning, EasyCrypt makes the
choice of letting programs run in arbitrary initial memories, and those
need to be specified as part of the probability statements/advantages.
At present, it is impossible to define operators that are parameterized
by memories in EasyCrypt, and we must always explicitly write out the
advantage expressions when they are present. This means that the
advantage expressions will only be formalized within the formalization
of the corresponding security statements. For this reason, we postpone
the discussion concerning the formalization of the advantage expressions
to when we start formalizing the relevant security statements.

“Nonce-Respecting” Pseudo-Random Function Family Property, Pen-and-Paper
------------------------------------------------------------------------

In cryptography, it is common to base security of a scheme on
computational hardness assumptions that can somehow be linked to (parts
of) the scheme; we also do this here. Particularly, we base the
IND$-NRCPA security of

.. math:: \mathcal{E}

\ on the (assumed) “Nonce-Respecting” Pseudo-Random Function family
(NRPRF) property [1]_ of the function family used to map nonces to
plaintexts (i.e.,

.. math:: \left(f_{k} : \mathcal{N} \rightarrow \mathcal{P}\right)_{k \in \mathcal{K}}

). Intuitively, this property captures the extent to which an (unknown)
random function from the function family is indistinguishable from a
truly random function of the same type (i.e., from nonces to plaintexts)
by observing the outputs corresponding to unique/non-repeating inputs.

More formally, consider the two oracles given below,
:math:`\mathcal{O}^{PRF\textrm{-}real}` and
:math:`\mathcal{O}^{PRF\textrm{-}ideal}`. [2]_

.. math::


   \begin{align*}
   \begin{align*}
   & \underline{\smash{\mathcal{O}^{PRF\textrm{-}real}}}\\
   & \begin{align*}
     & \underline{\smash{\mathsf{init}()}}\\
     & \left\lfloor~
       \begin{align*}
       & k \operatorname{\smash{\overset{\$}{\leftarrow}}} \mathcal{D}_{\mathcal{K}}\\
       & \mathrm{log} \leftarrow [\ ]
       \end{align*}
       \right.
     \end{align*}
   \\
   & \begin{align*}
     & \underline{\smash{\mathsf{get}(n)}}\\
     & \left\lfloor~
       \begin{align*}
       & \textsf{if}\ n \notin \mathrm{log}\\
       & \left\lfloor~
         \begin{align*}
         & \mathrm{log} \leftarrow n\ ||\ \mathrm{log}\\
         & m \leftarrow f_k(n)\\
         & \textsf{return}\ m
         \end{align*}
         \right.\\
       & \textsf{else}\\
       & \left\lfloor~
         \begin{align*}
         & \textsf{return}\ \bot
         \end{align*}
         \right.
       \end{align*}
       \right.
     \end{align*}
   \end{align*}
   &&&&&&&&
   \begin{align*}
   & \underline{\smash{\mathcal{O}^{PRF\textrm{-}ideal}}}\\
   & \begin{align*}
     & \underline{\smash{\mathsf{init}()}}\\
     & \left\lfloor~
       \begin{align*}
       & \\
       & \mathrm{log} \leftarrow [\ ]
       \end{align*}
       \right.
     \end{align*}
     \\
     & \begin{align*}
     & \underline{\smash{\mathsf{get}(n)}}\\
     & \left\lfloor~
       \begin{align*}
       & \textsf{if}\ n \notin \mathrm{log}\\
       & \left\lfloor~
         \begin{align*}
         & \mathrm{log} \leftarrow n\ ||\ \mathrm{log}\\
         & m \operatorname{\smash{\overset{\$}{\leftarrow}}} \mathcal{U}_{\mathcal{P}}\\
         & \textsf{return}\ m
         \end{align*}
         \right.\\
       & \textsf{else}\\
       & \left\lfloor~
         \begin{align*}
         & \textsf{return}\ \bot
         \end{align*}
         \right.
       \end{align*}
       \right.
       \end{align*}
     \end{align*}
   \end{align*}

As we can see, :math:`\mathcal{O}^{PRF\textrm{-}real}` and
:math:`\mathcal{O}^{PRF\textrm{-}ideal}` effectively only differ in the
way they create plaintexts: The former creates plaintexts by mapping the
provided nonces with a random function (that is fixed during
initialization) from
:math:`\left(f_{k} : \mathcal{N} \rightarrow \mathcal{P}\right)_{k \in \mathcal{K}}`;
the latter creates plaintexts by sampling them uniformly at random,
independent of the provided nonces. Then, akin to what we did for
IND$-NRCPA security, we define the advantage of a nonce-respecting
pseudo-random function distinguisher :math:`\mathcal{D}` against
:math:`\left(f_{k} : \mathcal{N} \rightarrow \mathcal{P}\right)_{k \in \mathcal{K}}`
as the following (absolute) difference.

.. math::


   \mathsf{Adv}^{\mathrm{NRPRF}}(\mathcal{D})
   = \left|\mathsf{Pr}\left[\mathsf{Exp}^{\mathrm{NRPRF}}_{\mathcal{D}, \mathcal{O}^{PRF\textrm{-}real}} = 1\right]
   - \mathsf{Pr}\left[\mathsf{Exp}^{\mathrm{NRPRF}}_{\mathcal{D}, \mathcal{O}^{PRF\textrm{-}ideal}} = 1\right]\right|

In this equation,
:math:`\mathsf{Exp}^{\mathrm{NRPRF}}_{\mathcal{D}, \mathcal{O}}` refers
to the experiment defined below.

.. math::


   \begin{align*}
   & \underline{\smash{\mathsf{Exp}^{\mathrm{NRPRF}}_{\mathcal{O}}(\mathcal{D})}}\\
   & \left\lfloor
     \begin{align*}
     & \mathcal{O}.\mathsf{init}()\\
     & b \operatorname{\smash{\overset{\$}{\leftarrow}}} \mathcal{D}^{\mathcal{O}.\mathsf{get}}.\mathsf{distinguish}()\\
     & \textsf{return}\ b
     \end{align*}
     \right.
   \end{align*}

Notice that this experiment takes the exact same approach as the one we
defined for IND$-NRCPA security: The only difference between these
experiments concerns the class of adversaries and the class of oracles
they consider.

Lastly, we say that
:math:`\left(f_{k} : \mathcal{N} \rightarrow \mathcal{P}\right)_{k \in \mathcal{K}}`
is a NRPRF if, for any nonce-respecting pseudo-random function family
adversary :math:`\mathcal{D}`,
:math:`\mathsf{Adv}^{\mathrm{NRPRF}}(\mathcal{D}`) is “small”. Again,
because we only consider exact security, “small” basically means
“bounded by other *concrete values/probabilities* that we believe are
small in practice”.

Again, if you are interested in seeing the paper-based security proof
before diving into the EasyCrypt formalization, you can read further on
the `proving security part <proof>`__.

“Nonce-Respecting” Pseudo-Random Function Family Property, EasyCrypt
--------------------------------------------------------------------

Evidently, on a conceptual level, the definitions for IND$-NRCPA and
NRPRF experiment and oracles are almost identical. Accordingly, the
corresponding EasyCrypt formalization are also going to be almost
identical. As such, we go over the formalization of NRPRF at a faster
pace, primarily highlighting the differences with the formalization of
IND$-NRCPA and reiterating important aspects. The preceding material
discussing IND$-NRCPA most likely contains explanations of
subjects/concepts left untouched here.

NRPRF Oracle Type
~~~~~~~~~~~~~~~~~

Once again, we start by defining the type for the oracles; as before, we
do so using a module type that specifies a procedure signature for each
algorithm defined expected to be implemented by NRPRF oracles. Looking
at the definitions of :math:`\mathcal{O}^{PRF\textrm{-}real}` and
:math:`\mathcal{O}^{PRF\textrm{-}ideal}`, we can see what (type of)
algorithms these are. The following snippet presents the corresponding
formalization.

::

   module type NRPRF_Oraclei = {
     proc init() : unit
     proc get(n : nonce) : ptxt option
   }.

Real NRPRF Oracle
~~~~~~~~~~~~~~~~~

Using the newly defined module type, we formalize the real NRPRF oracle
using a (by now) straightforward translation from the pen-and-paper
definition; see the snippet below. Recall that an EasyCrypt procedure
can only have one ``return`` statement, which is why we employ a return
variable instead of having multiple ``return`` statements. Furthermore,
remember that, since we are using an ``option`` type to represent
successes and failures, the outputs are of the form ``Some p`` (where
``p`` is of type ``ptxt``; this represents a success) or ``None`` (this
represents a failure).

::

   module O_NRPRF_real : NRPRF_Oraclei = {
     var k : key
     var log : nonce list

     proc init() : unit = {
       k <$ dkey;

       log <- [];
     }

     proc get(n : nonce) : ptxt option = {
       var r : ptxt option;

       if (! (n \in log)) {
         log <- n :: log;
         
         r <- Some (f k n);
       } else {
         r <- None;
       }
       
       return r;
     }
   }.

Ideal NRPRF Oracle
~~~~~~~~~~~~~~~~~~

For the ideal NRPRF oracle, the formalization is similar to that of the
real NRPRF oracle, only differing in (analogous) ways the pen-and-paper
definitions also differ.

The only novelty here is that we define and use an alias for the
``dctxt`` distribution, called ``dptxt``. In its definition, this alias
is explicitly indicated to be a distribution over the type of
plaintexts. Naturally, this is only possible because ``ptxt`` and
``ctxt`` are actually the same type. Semantically, this makes no
difference at all; the only reason we do this is to increase readability
by matching the notation with the conceptual meaning. (Recall that NRPRF
oracles conceptually produce plaintexts, not ciphertexts.) The specific
alias definition is provided in the snippet below.

::

   op dptxt : ptxt distr = dctxt.

Then, we formalize the ideal NRPRF oracle as follows.

::

   module O_NRPRF_ideal : NRPRF_Oraclei = {
     var log : nonce list

     proc init() : unit = {
       log <- [];
     }

     proc get(n : nonce) : ptxt option= {
       var y : ptxt;
       var r : ptxt option;

       if (! (n \in log)) {
         log <- n :: log;
         
         y <$ dptxt;
         
         r <- Some y;
       } else {
         r <- None;
       }
       
       return r;
     }
   }.

NRPRF Experiment and Security
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Having formalized the relevant oracles, we continue by formalizing the
(NRPRF) adversary class. Once again, we formalize this adversary class
using a module type with a single module parameter modeling the expected
NRPRF oracle. Notice that, akin to before, the current module type we
have for NRPRF oracles—``NRPRF_Oraclei``—specifies (the signature of) an
initialization procedure, which we do not want to expose to adversaries.
As such, we create a separate module type for NRPRF oracles given to
adversaries, which only expose the ``get`` procedure.

::

   module type NRPRF_Oracle = {
     include NRPRF_Oraclei [get]
   }.

   module type Adv_NRPRF (O : NRPRF_Oracle) = {
     proc distinguish() : bool
   }.

At this point, we have everything required to formalize the NRPRF
experiment, shown. Recall that, even though the adversary is given an
oracle of type ``NRPRF_Oraclei``, the ``init`` procedure of this module
is not actually exposed to the adversary due to the way we specified its
module type.

::

   module Exp_NRPRF (O : NRPRF_Oraclei) (D : Adv_NRPRF) = {
     proc run() : bool = {
       var b : bool;
       
       O.init();
       
       b <@ D(O).distinguish();
       
       return b;
     }
   }.

.. [1]
   NRPRF is not a conventional property; rather, it is a variant of the
   more customary Pseudo-Random Function family (PRF) property. For
   educational purposes, we have specifically devised this variant to
   simplify the current proof.

.. [2]
   Typically, the NRPRF experiment and oracles would first be defined
   with respect to an abstract function family of the correct type
   before being instantiated with the actual relevant function family
   for the proof. This is analogous to how we first defined IND$-NRCPA
   with respect to an abstract (symmetric) nonce-respecting encryption
   scheme before instantiating it with the actual relevant encryption
   scheme for the proof. However, for educational purposes, we decide to
   keep it simple and stick with the description that matches the
   EasyCrypt formalization the best; for this reason, we immediately
   consider the concrete NRPRF property of
   :math:`\left(f_{k} : \mathcal{N} \rightarrow \mathcal{P}\right)_{k \in \mathcal{K}}`.
