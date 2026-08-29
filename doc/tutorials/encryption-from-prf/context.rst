Defining the Preliminaries/Context
==================================

We will start off by defining the preliminaries and context of our
security proof, both mathematically (“pen-and-paper”) and in EasyCrypt.
This includes everything from the relevant sets and functions to the
actual scheme; this does not yet include anything regarding security.

Defining the Basics, Pen-and-Paper
----------------------------------

We assume the existence of the following artifacts; these artifacts will
be used to construct the encryption scheme. - A set :math:`\mathcal{K}`
of keys called the *key space*. - A set :math:`\mathcal{P}` of
plaintexts called the *plaintext space*. - A set :math:`\mathcal{N}` of
nonces called the *nonce space*. - A set :math:`\mathcal{C}` of
ciphertexts called the *ciphertext space*. In this case, the ciphertext
space happens to be equal to the plaintext space; that is,
:math:`\mathcal{C} = \mathcal{P}`. - An associative and commutative
binary operator :math:`\oplus : \mathcal{P}
  \times \mathcal{P} \rightarrow \mathcal{P}` such that
:math:`x \oplus x
  \oplus y = y` for any :math:`x, y \in \mathcal{P}`. - A family of
functions
:math:`\left(f_{k} : \mathcal{N} \rightarrow \mathcal{P}\right)_{k \in \mathcal{K}}`
from nonces (in :math:`\mathcal{N}`) to plaintexts (in
:math:`\mathcal{P}`), indexed by keys (in :math:`\mathcal{K}`). - A
distribution :math:`\mathcal{D}_{\mathcal{K}}` over
:math:`\mathcal{K}`. [1]_

Defining the Scheme, Pen-and-Paper
----------------------------------

The (symmetric) encryption scheme we consider is a straightforward one;
we call it nonce-based because it uses a nonce (that it takes as an
input) to perform its encryption and decryption procedures. Formally, we
define the encryption scheme as a triple of algorithms
:math:`\mathcal{E} = \left(\mathsf{KGen}, \mathsf{Enc}, \mathsf{Dec}\right)`,
the implementations of which are provided below.

.. math::


   \begin{align*}
   \begin{align*}
   & \underline{\smash{\mathsf{KGen}()}}\\
   & \left\lfloor~
     \begin{align*}
     & k \operatorname{\smash{\overset{\$}{\leftarrow}}} \mathcal{D}_{\mathcal{K}}\\
     & \mathsf{return}\ k
     \end{align*}
     \right.
   \end{align*}
   &&&&
   \begin{align*}
   & \underline{\smash{\mathsf{Enc}(k, n, m)}}\\
   & \left\lfloor~
     \begin{align*}
     & \mathsf{return}\ f_{k}(n) \oplus m
     \end{align*}
     \right.\\
   &
   \end{align*}
   &&&&
   \begin{align*}
   & \underline{\smash{\mathsf{Dec}(k, n, c)}}\\
   & \left\lfloor~
     \begin{align*}
     & \textsf{return}\ f_{k}(n) \oplus c
     \end{align*}
     \right.\\
   &
   \end{align*}
   \end{align*}

As you can see, this is a relatively basic nonce-based encryption
scheme, not containing more than a single sampling and a handful of
simple function/operator evaluations. Correctness of the scheme—that is,
whether the decryption of any encryption returns the original
message—can be seen to hold as follows.

.. math::


   \begin{align*}
   \forall_{k \in \mathcal{D}_{\mathcal{K}}, n \in \mathcal{N}, m \in \mathcal{M}}:
   &\ \mathcal{E}.\mathsf{Dec}(k, n, \mathcal{E}.\mathsf{Enc}(k, n, m)) =\\
   &\ \mathcal{E}.\mathsf{Dec}(k, n, f_{k}(n) \oplus m) =\\
   &\ f_{k}(n) \oplus (f_{k}(n) \oplus m) =\\
   &\ f_{k}(n) \oplus f_{k}(n) \oplus m =\\
   &\ m
   \end{align*}

Here, the first two equalities are obtained by respectively replacing
the identifiers of the encryption and decryption procedures by their
specifications; the final two equalities are a consequence of the
assumed associativity and “self-inverse” properties of :math:`\oplus`.

If you want to get an overview first before you dive into the
formalization in EasyCrypt, you can directly jump to the `paper-based
definition of the security model <security>`__ from here.

:::note From pen-and-paper to computer

In standard cryptographic practice, :math:`\mathcal{K}`,
:math:`\mathcal{P}`, :math:`\mathcal{N}`,
:math:`\mathcal{D}_{\mathcal{K}}`, and :math:`\oplus` would be given
concrete definitions. In EasyCrypt, we tend to make proofs as generic as
possible, only afterward instantiating the proof with concrete types.
For example, anything we prove on the construction above will also hold
in the case where :math:`\mathcal{K} = \mathcal{N} = \{0,1\}^{\lambda}`
(for some key length :math:`\lambda`),
:math:`\mathcal{P} = \{0,1\}^{\ell}` (for some plaintext length
:math:`\ell`), :math:`\mathcal{D}_{\mathcal{K}}` is the uniform
distribution over :math:`\mathcal{K}`, and :math:`\oplus` is bitwise XOR
over :math:`\{0,1\}^{\ell}`. We will elaborate on this in a later
section. :::

Interlude: EasyCrypt’s Languages
--------------------------------

EasyCrypt provides a combination of two specification languages for the
formalization of (pen-and-paper) definitions such as the above.
Specifically, it provides the following two languages. + Expression
language. This is a polymorphic lambda calculus used to describe
mathematical structure. + :math:`\texttt{pWhile}` language. This is a
simple probabilistic imperative language used to describe any
(potentially probabilistic) program.

Programmatic constructs in these languages are wrapped inside
*theories*. For now, to keep things simple, we will use a single
monolithic theory containing specialized definitions. At a later stage,
we will explain how developments in EasyCrypt can be split across
multiple theories, some of which can even be generalized for reuse
across multiple proofs.

Defining the Basics, EasyCrypt
------------------------------

Starting from scratch, we formalize the above pen-and-paper definitions
in EasyCrypt as follows. [2]_

::

   (* Types for keys, plaintexts, nonces, respectively *)
   type key, ptxt, nonce.

   (* Type for ciphertexts *)
   type ctxt = ptxt.

   (* Binary infix operator on plaintexts *)
   op (+) : ptxt -> ptxt -> ptxt.

   (* Family of functions from nonces to plaintexts, indexed by keys *)
   op f : key -> nonce -> ptxt.

   (* Subdistribution over keys *)
   op dkey : key distr.

   (* Associativity, commutativity, and "self-inverse" property of the binary operator, respectively *)
   axiom addpA (x y z : ptxt) : x + y + z = x + (y + z).
   axiom addpC (x y : ptxt) : x + y = y + x.
   axiom addKp (x y : ptxt) : x + x + y = y.

Foremost, note that each declaration is terminated by a full stop ``.``,
which marks the end of a “formal sentence” (e.g., declarations,
definitions, axioms, lemmas, or atomic proof steps) in EasyCrypt. Let us
now discuss the various kinds of declarations that appear in this
preamble.

:::note From pen-and-paper to computer

On paper, we often refer to the formal description of an artifact as a
“definition”. However, when talking about the corresponding descriptions
in EasyCrypt, we deliberately make a distinction between *declarations*
and *definitions*. Intuitively, a *declaration* is a (formal) sentence
that describes some abstract artifact, but does not provide a particular
realization of this artifact. For example, most (formal) sentences in
the above snippet are declarations: they merely specify the existence of
a certain type/function/distribution, but do not specify this
type/function/distribution concretely. Contrarily, a *definition* is a
(formal) sentence that describes some artifact with a specific
realization. One can turn a declaration into a definition by providing a
realization (that still satisfies the restrictions imposed by the
declaration, e.g., the types). This can be done by either (1) directly
changing the code and appending a “=” followed by a definition to the
declaration (e.g., ``type key = int.``), or (2) cloning the theory and
providing instantiations of the abstract artifact(s). [3]_ This latter
approach will be explained at a later stage of the tutorial. :::

Types
~~~~~

First, we *declare* three *types* (which can be thought of as non-empty
sets): ``key`` (denoting :math:`\mathcal{K}`), ``ptxt`` (denoting
:math:`\mathcal{P}`) and ``nonce`` (denoting :math:`\mathcal{N}`). We
also *define* a type of ciphertexts, ``ctxt``—in this case, it is
defined to be the same as the type of plaintexts (corresponding to the
fact that :math:`\mathcal{C} =  \mathcal{P}`).

Operators and Distributions
~~~~~~~~~~~~~~~~~~~~~~~~~~~

Following, we *declare* the operators using the ``op`` keyword (standing
for operator).

The first operator we declare is :math:`\oplus`, specifying we want to
use it as an infix by enclosing it in parentheses. More specifically, by
declaring the operator ``(+)``, we can subsequently use it as ``a + b``
(where ``a`` and ``b`` are operands of the appropriate type). After the
colon, we specify the type of the declared operator; so, ``(+)`` is of
type ``ptxt -> ptxt -> ptxt``. This might strike you as strange, since
this type intuitively corresponds to a (pen-and-paper) function
:math:`\oplus : \mathcal{P} \rightarrow \mathcal{P} \rightarrow \mathcal{P}`.
However, since ``->`` is right associative, i.e.,
``ptxt -> ptxt -> ptxt`` is equal to ``ptxt -> (ptxt -> ptxt)``, we have
that ``ptxt -> ptxt -> ptxt`` is actually equal to
``ptxt * ptxt -> ptxt`` (which corresponds to the pen-and-paper
:math:`\mathcal{P} \times \mathcal{P} \rightarrow \mathcal{P}`). This
translation of functions that take multiple arguments into sequences of
functions that each take a single argument is called
`currying <https://en.wikipedia.org/wiki/Currying>`__. In computer-based
treatments, the curried form of the type (i.e., the type corresponding
to sequences of functions that each take a single argument) is more
customary, mainly because it eases the manipulation of individual
operands and the partial application of operators.

As a second operator, we declare the function family :math:`f`, giving
it the ``key -> nonce -> ptxt`` type. As desired, this type intuitively
corresponds to the (pen-and-paper) set :math:`\mathcal{K} \rightarrow
(\mathcal{N} \rightarrow \mathcal{P})` of functions from nonces to
plaintexts, indexed by keys. (Note that
:math:`f : \mathcal{K} \rightarrow (\mathcal{N} \rightarrow \mathcal{P})`
is just a less fancy way of writing
:math:`\left(f_{k} : \mathcal{N} \rightarrow \mathcal{P}\right)_{k \in \mathcal{K}}`.)

Finally, the `(sub)distribution </docs/reference#distributions>`__
:math:`\mathcal{D}_{\mathcal{K}}` is simply declared as a constant
``dkey`` of type ``key distr``, the type of (sub)distributions over
elements in type ``key``. [4]_ Here, ``distr`` is a so-called *type
constructor*; such constructors can be instantiated (in prefix notation)
by any type to construct another type. We discuss the details of
parameterized (or polymorphic) types at a later stage, as they are not
useful/necessary yet.

Axioms
~~~~~~

With the operators declared, it remains to restrict the set of valid
candidates for :math:`\oplus` or, equivalently, state the properties we
want/assume :math:`\oplus` to satisfy. We achieve this by declaring the
appropriate *axioms*.

More precisely, we restrict our infix ``+`` operator by declaring three
axioms, each capturing one of the properties we want :math:`\oplus` to
satisfy: ``addpC`` captures commutativity, ``addpA`` captures
associativity, and ``addKp`` captures the “self-inverse” property.

The general shape of an axiom declaration is
``axiom < name > < parameters > : < boolean expression >.``, where the
parameters are universally quantified (typed) variables. For example,
axiom ``addpC`` formally states

.. math::


   \forall x, y \in \mathcal{P}.\ x \oplus y = y \oplus x

Interpreting Declarations
~~~~~~~~~~~~~~~~~~~~~~~~~

So far, we have laid down formal declarations, but how should they be
interpreted? In essence, everything in the remainder of the file
(including definitions and proofs) can be thought of as *parameterized*
by the declared artifacts. So, in this case, everything in the remainder
of the file can be applied to (and is valid for) any set of keys,
plaintext and nonces, and any operators and distributions that meet the
axioms.

We’ll discuss how to actually instantiate constructions and proofs at a
later point.

Defining the Scheme, EasyCrypt
------------------------------

With these preliminaries laid down formally, we can now use them to
formalize the (minimal) *syntax* of (symmetric) nonce-based encryption
schemes—that is, the signatures of the procedures that any such scheme
is expected to implement and, thus, can be called from other code that
has access to such a scheme by using the appropriate call statements—as
well as the specification of :math:`\mathcal{E}`. The following snippet
presents these formalizations in EasyCrypt using `module types and
modules </docs/reference#module-types-modules-and-procedures>`__.

::

   (* 
     Module type for (symmetric) nonce-based encryption schemes.
     Intuitively, this specifies the interface that such 
     encryption schemes are expected to implement.
   *)
   module type NBEncScheme = {
     proc kgen(): key
     proc enc(k : key, n : nonce, m : ptxt): ctxt
     proc dec(k : key, n : nonce, c : ctxt): ptxt
   }.

   (* 
     Specification of the considered nonce-based encryption scheme.
     Because the module implements all the procedures specified in the NBEncScheme
     module type, the module has this type (making it valid to give it this type).  
   *)
   module E : NBEncScheme = {
     proc kgen() : key = {
       var k;

       k <$ dkey;
       
       return k;
     }

     proc enc(k : key, n : nonce, m : ptxt) : ctxt = {
       return (f k n) + m;
     }

     proc dec(k : key, n : nonce, c : ctxt) : ptxt = {
       return (f k n) + c;
     }
   }.

Here, we start by defining a module type called ``NBEncScheme`` which
defines the (minimal) *syntax* of nonce-based encryption schemes. More
precisely, it states that any module of type ``NBEncScheme`` *must*
implement the following three procedures (but may implement more).

- A procedure ``kgen`` which takes no arguments and outputs a value of
  type ``key``.
- A procedure ``enc`` which, given a value of type ``key``, a value of
  type ``nonce`` and a value of type ``ptxt``, outputs a value of type
  ``ctxt``.
- A procedure ``dec`` which, given a value of type ``key``, a value of
  type ``nonce`` and a value of type ``ctxt`` produces a value of type
  ``ptxt``.

As a result, code that has access to a module of type ``NBEncScheme``
(which may be abstract) can always call these procedures by using the
appropriate call statements.

Surely, the above formalization of nonce-based encryption schemes
accurately captures the corresponding generic pen-and-paper definition
we gave earlier: any triple of algorithms consisting of a key generation
algorithm, taking no inputs and producing a key; an encryption
algorithm, taking a key, nonce, and plaintext, and producing a
ciphertext; and a decryption algorithm, taking a key, nonce, and
ciphertext, and producing a plaintext.

After defining the module type, we formalize the considered encryption
scheme :math:`\mathcal{E}` as the module ``E``. As expected, this module
is of type ``NBEncScheme`` and, hence, provides an implementation of all
the procedures specified by this module type. Other code can issue calls
to these procedures; for example, the encryption procedure may be called
as ``idc <@ E.enc(idk, idn, idm)`` (or ``E.kgen(idk, idn, idm)`` when
you do not want to store the return value of the procedure), where
``idc``, ``idk``, ``idn``, and ``idm`` are identifiers for variables of
type ``ctxt``, ``key``, ``nonce``, and ``ptxt``, respectively. [5]_ In
this case, ``E`` does not implement more procedures than specified by
``NBEncScheme``, so its concrete syntax is fully captured by the generic
syntax defined by its module type. However, if ``E`` would implement
more procedures, other code would also be able to issue direct calls to
these procedures through the corresponding call statements, even though
these procedures would not be part of the module type definition.

The procedures’ *bodies* then specify the scheme’s operation. In this
particular case, ``E.kgen`` samples a key from ``dkey``, the
formalization of distribution :math:`\mathcal{D}_{\mathcal{K}}`, into a
*local variable* ``k`` and returns this value; ``E.enc`` and ``E.dec``
straightforwardly use ``f`` and ``+``, the formalization of
:math:`\left(f_{k} : \mathcal{N} \rightarrow \mathcal{P}\right)_{k \in \mathcal{K}}`
and :math:`\oplus`, to behave as specified mathematically. Note that, in
the syntax of expressions, spaces rather than parentheses are used to
denote operator application: ``f k n`` denotes the value obtained by
applying the operator ``f`` to ``k`` and further applying the resulting
value (an operator of type ``nonce -> ptxt``) to ``n``. Indeed, this is
where the aforementioned currying comes into play: Instead of taking a
``key``-``input`` two-tuple and returning a ``ptxt`` value, ``f`` takes
a ``key`` value and returns an operator that takes a ``nonce`` value and
returns a ``ptxt`` value.

.. [1]
   There are subtleties with this; in certain cases, we might instead
   want to only assume a key generation algorithm—which may not directly
   define a distribution (for example, if it involves interaction). We
   keep these discussions for a subsequent tutorial.

.. [2]
   In EasyCrypt, ``(*`` and ``*)`` delimit a (potentially multi-line)
   comment.

.. [3]
   Oftentimes, the realizations given to artifacts in a definition are
   based on other declarations (i.e., other abstract artifacts).
   Nevertheless, we refer to these as definitions since the artifact is
   technically still given a realization (even though this realization
   is based on other abstract artifacts).

.. [4]
   In this context, the use of the word “constant” might be a bit
   confusing: Wasn’t the ``op`` keyword used to declare/define
   operators? The answer is *yes, but operators are constants.* For
   example, when you declare an operator ``op g : ptxt -> ctxt``, you
   denote a *single, fixed* function (abstract perhaps, but fixed) from
   plaintexts to ciphertexts. Surely, this is the same as defining a
   (potentially abstract) constant of type ``ptxt -> ctxt``. Similarly,
   we can use the ``op`` keyword to declare/define constants of any
   type, including non-function types such as ``key`` or ``key distr``.

.. [5]
   When calling a module’s procedure from other code, it is not
   necessary to have the identifiers of the provided arguments match the
   identifiers in the syntax definition; these are merely placeholders
   that may be used for documentation purposes.
