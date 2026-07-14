Reusing Proof Components
========================

A huge advantage of using tools to machine-check cryptographic proofs
lies in their ability to argue about generic and modularized proof
elements. We can therefore easily define or reason about cryptographic
primitives and properties in a reusable way. This reusability is also
supported by EasyCrypt and therefore topic of this more advanced
tutorial.

In the following sections, we will dive into the concept of abstract
theories in EasyCrypt and explore how they can be effectively reused in
different proofs.

Using Reusable Definitions
--------------------------

In EasyCrypt we can write so-called abstract theories that for example
include formal representations of mathematical concepts (rings, groups,
…) or security definitions (CPA security, PRF assumption, …). Abstract
theories allow for the generalization of underlying primitives such that
we can reason for a whole category of the same structure. An abstract
theory does not define concrete objects unless it is instantiated in
another theory. It can then be applied to various cryptographic
scenarios, reducing the need to recreate formal definitions and proofs
for commonly used primitives. The difference between a concrete and an
abstract theory is that we cannot import an abstract theory without
copying it. This is solved by cloning abstract theories in EasyCrypt
which also allows us to set abstract types and operators in this theory
to concrete values from the theory one is currently working in.

::

   clone import AbstractTheory as AT with
     type a <- b,
     op f <- 1.

In this tutorial, we are going to show two examples how to reuse the
abstract ``Construction`` theory that is introduced in the basic
tutorial. In contrast to the basic tutorial, we introduce most of the
definitions directly in EasyCrypt.

Example: Nonce-Based Security of a Concrete Construction
--------------------------------------------------------

Until now our construction gives generic results for a nonce-based
encryption scheme without specifying the exact types or functions used
for encryption. It is straight forward to reason that if something is
secure for all types and functions fulfilling some axioms, it should be
especially secure for one specific instantiation of those types and
functions. In our case of a nonce-based encryption scheme we could for
example want to choose our plaintexts and ciphertexts to be bitstrings
of a certain length and the ``(+)`` operator to be the XOR operator. To
do so in EasyCrypt, we first need to define what a bitstring is in
general before we can have fixed length bitstrings. Luckily there exists
already an abstract theory in the standard library called ``BitWord``
which we can use for defining strings of 256 bits. We will use the
cloning mechanism of EasyCrypt as mentioned above. Make sure you first
require the ``BitWord`` theory to make it available in your theory.

::

   clone import BitWord as Bitstring with
     op n <- 256
   proof gt0_n by trivial
   rename
     "word" as "bits"
     "dunifin" as "dbits".
   import DWord.

In the ``BitWord`` theory the operator n determines the length of a word
(same as a string) consisting of bits. In the instantiation we set this
operator to the specific value of 256 bits. To be able to apply the
theorems from that theory, we have to fulfill the assumptions stated for
this operator. In this case the only condition of ``n`` is to be greater
than zero. We prove the axiom ``gt0_n`` by using the ``trivial`` tactic.
The renaming to bits is more cosmetic and used to be consistent in
naming of lemmas. As last step we import the ``DWord`` theory which
makes lemmas about the distribution of bitstrings we imported available.
Those are used in the next clone to have a distribution that satisfies
all axioms for the distribution of ciphertexts.

Additionally, we require the ``BitEncoding`` theory for the definition
of the XOR operator. With that we have all types and operators to
instantiate the nonce-based encryption scheme in the basic tutorial.

::

   clone import Construction as C with 
     type ptxt <- bits,
     type nonce <- bits,
     op (+) <- (+^),
     op dctxt <- dbits
   proof *.
   realize addpA. proof. move => x y z. by rewrite xorwA. qed.
   realize addpC. proof. move => x y. by rewrite xorwC. qed.
   realize addKp. proof. move => x y. by rewrite xorwK xorwC xorw0. qed.
   realize dctxt_ll by exact/dbits_ll.
   realize dctxt_uni by exact/dbits_uni.
   realize dctxt_fu by exact/dbits_fu.

As described above we clone the ``Construction`` using ``bits`` and the
XOR operator denoted as ``(+^)``. To get an overview which assumptions
of the ``Construction`` we need to prove, we can use ``proof *``
here. [1]_ It is not necessary to use it, but it helps to not forget
about realizing any of the assumptions and checks whether all
assumptions are consistent. In this case we get six assumptions we have
to show. The first three of them are axioms about the ``(+)`` operator
and are proven by using axioms about the XOR operator we can find in the
``BitEncoding`` theory. The latter three are the assumptions about the
distribution of ciphertexts which are exactly met by the axioms about
the distribution of bitstrings.

Since this new definition if a scheme using bitstrings and the XOR
operator satisfies all assumptions of the ``Construction`` we get that
all proofs about the security also hold in this case. o8

Example: IV-Based Security from Nonce-Based Security
----------------------------------------------------

In the ``Construction`` we looked at the security of nonce-based
encryption guaranteeing that the nonce is not reused. The example above
illustrated how to use this abstract definition to apply the results to
a more concrete scheme. In contrast to that, this second example
instantiates the ``Construction`` in a more conceptual way to build a
bigger abstract theory about IV-based security and its relations to
nonce-based security.

We start by defining the preliminaries for the security of IV-based
encryption schemes and giving an overview of the reasoning in the
security proof. Then we will present the detailed steps of the proof in
EasyCrypt.

Difference between IV-Based and Nonce-Based Security
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Both IV-based and nonce-based encryption are techniques to randomize the
encryption process. The randomization is necessary to be able to ensure
the security when we encrypt multiple messages using the same key.
Instead of letting the adversary choose a nonce as input to the oracle,
the IV (Initialization Vector) is a fixed-length random value generated
inside the oracle. The encryption algorithm is not changed and expects
still a random value as input. We can illustrate the difference between
IV-based and nonce-based by looking on the real oracles (nr stands for
nonce respecting).

.. math::


   \begin{align*}
   \begin{align*}
   & \smash{\mathcal{CPA}^{nr\textrm{-}real}_{\Sigma_{NR}}}\\
   \\
   & \begin{align*}
     & \underline{\smash{\mathsf{init}()}}\\
     & \left\lfloor~
       \begin{align*}
       & k \operatorname{\smash{\overset{\$}{\leftarrow}}} \Sigma_{NR}.\mathsf{KGen}()\\
       & U \leftarrow \emptyset
       \end{align*}
       \right.
     \end{align*}
   \\
   & \begin{align*}
     & \underline{\smash{\mathsf{enc}(n, m)}}\\
     & \left\lfloor~
       \begin{align*}
       & \textsf{if}\ n \notin U\\
       & \left\lfloor~
         \begin{align*}
         & U \leftarrow U \cup \{n\}\\
         & c \leftarrow \Sigma_{NR}.\mathsf{Enc}(k, n, m)\\
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
   & \smash{\mathcal{CPA}^{iv\textrm{-}real}_{\Sigma_{IV}}}\\
   \\
   & \begin{align*}
     & \underline{\smash{\mathsf{init}()}}\\
     & \left\lfloor~
       \begin{align*}
       & k \operatorname{\smash{\overset{\$}{\leftarrow}}} \Sigma_{IV}.\mathsf{KGen}()
       \end{align*}
       \right.
     \end{align*}
     \\
     & \begin{align*}
     & \underline{\smash{\mathsf{enc}(m)}}\\
     & \left\lfloor~
       \begin{align*}
         & r \operatorname{\smash{\overset{\$}{\leftarrow}}} \mathcal{R}\\
       & c \leftarrow \Sigma_{IV}.\mathsf{Enc}(k, r, m)\\
       & \textsf{return}\ (r, c)
       \end{align*}
       \right.
       \end{align*}
     \end{align*}
   \end{align*}

Since the adversary is not allowed to input the randomness for the
encryption anymore, we can omit the check whether the given nonce is
unique and the initialization of the log. The randomness r is sampled
from a uniform distribution on the set :math:`\mathcal{R}` called the
*randomness space*. To make the randomness used in the encryption
accessible, we return this time both the value r and c. All changes also
apply for the ideal case.

Definitions for IV-Based Security in EasyCrypt
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

We start the same way as in the ``Construction`` before by defining all
needed types and operators with the needed axioms in an EasyCrypt
theory. To be more precise, we reuse the same types except for the
``nonce`` type (see the code). Instead, we introduce the ``rndness``
type and a full and uniform distribution ``drndness`` for it. Since
those types are abstract, this mainly changes the name and our
understanding.

::

   type rndness.
   op [lossless full uniform] drndness: rndness distr.

As mentioned before the encryption scheme does not change except for the
type of the second parameter to the ``enc`` and ``dec`` procedures that
is set to ``rndness``. Similarly, we rewrite the definitions for the
oracles, the distinguisher and the experiment to adapt to the setting of
the IV-based scheme. The interesting changes are in the oracles for the
CPA security for the IV-based encryption scheme and therefore presented
here.

::

   module type CPA_Oracle_IV_i = {
     proc init(): unit
     proc enc(m : ptxt) : rndness * ctxt
   }.

   module O_IV_ideal : CPA_Oracle_IV_i = {
     proc init() : unit = {
     }

     proc enc(m : ptxt) : rndness * ctxt = {
       var r, c;

       r <$ drndness;
       c <$ dctxt;
       return (r, c);
     }
   }.

   module O_IV_real (E : Enc_Scheme) : CPA_Oracle_IV_i = {
     var k : key

     proc init() : unit = {
       k <@ E.kgen();
     }

     proc enc(m : ptxt) : rndness * ctxt = {
       var r, c;

       r <$ drndness;
       c <@ E.enc(k, r, m);
       return (r, c);
     }
   }. 

This corresponds to the changes we saw in the pen-and-paper version of
the section above. Since the oracle has different return values, we
first define a new module type that describes the interface of an
IV-based oracle.

The last definition we include in this section is the instantiation of
the ``Construction``. This is crucial to be able to define a reduction
from an IV-based adversary to a nonce-based adversary in the later
sections. We clone the ``Construction`` using our new types and
operators. We especially want to match the ``nonce`` type with the new
defined ``rndness`` type in the clone.

::

   clone import Construction as C with
     type key <- key,
     type ptxt <- ptxt,
     type nonce <- rndness,
     op f <- f,
     op (+) <- (+),
     op dkey <- dkey,
     op dctxt <- dctxt
   proof *.
   realize addpA by exact/addpA.
   realize addpC by exact/addpC.
   realize addKp by exact/addKp.
   realize dctxt_ll by exact/dctxt_ll.
   realize dctxt_uni by exact/dctxt_uni.
   realize dctxt_fu by exact/dctxt_fu.

This time the cloning of the ``Construction`` theory is straight forward
since we have formulated the same axioms for the operators in this
theory as well. Therefore, we can prove them by saying exact and then
the name of the axiom in this theory.

Note that this does not mean we get around to prove those axioms for a
concrete instantiation. When cloning the ``IVbased`` theory to apply its
results we still need to prove all assumptions and axioms. This is why
we write this as an abstract theory as well.

Proof Overview
~~~~~~~~~~~~~~

For the IV-based encryption scheme the advantage of :math:`\mathcal{D}`
distinguishing ciphertexts produced using the encryption scheme
:math:`\Sigma_{IV}` from random ciphertexts is given by:

.. math::


   \mathsf{Adv}^{\mathsf{iv\textrm{-}cpa}}_{\mathcal{E}}(\mathcal{D})
   = \left|\mathsf{Pr}\left[\mathsf{Exp}^{\mathsf{iv\textrm{-}cpa}}_{\mathcal{CPA}^{\mathit{iv\textrm{-}real}}_{\Sigma_{IV}}}(\mathcal{D}): 1\right]
   - \mathsf{Pr}\left[\mathsf{Exp}^{\mathsf{iv\textrm{-}cpa}}_{\mathcal{CPA}^{\mathit{iv\textrm{-}ideal}}}(\mathcal{D}): 1\right]\right|  

Our goal with this theory is to prove the relation between the IND-CPA
security of IV-based encryption schemes and nonce-based schemes. In
particular, we show that the result from the ``Construction`` implies
IV-based security.

To make the implication more clear, we start by comparing the real
oracles. So in both the NR and the IV real oracle, we call the ``enc``
procedure of the scheme with some random value of type ``rndness``. Note
that we set ``nonce`` to match ``rndness``. The difference is that we
did not restrict the IV to be unique. Informally, that should not
compromise the security, since the adversary has no influence on the
sampling on the randomness and the case that the same random value is
sampled is very unlikely for a large set :math:`\mathcal{R}`. We can be
more precise and say that the probability that the sampling is returning
the same value twice is bounded by the so-called Birthday bound, which
is known to be negligible for large sets.

So with a great certainty we can assume that the random values sampled
are unique. In that case the IV-based security is directly related to
the nonce-based security since the nonces are restricted to be unique.
This gives us the following inequality we aim to prove.

.. math::


   \mathsf{Adv}^{\mathsf{iv\textrm{-}cpa}}_{\mathcal{E}}(\mathcal{D})
   \leq \left|\mathsf{Pr}\left[\mathsf{Exp}^{\mathsf{nr\textrm{-}cpa}}_{\mathcal{CPA}^{\mathit{nr\textrm{-}real}}_{\Sigma_{NR}}}(\mathcal{D'}): 1\right]
   - \mathsf{Pr}\left[\mathsf{Exp}^{\mathsf{nr\textrm{-}cpa}}_{\mathcal{CPA}^{\mathit{nr\textrm{-}ideal}}}(\mathcal{D'}): 1\right]\right| 
   + \frac{(q \cdot (q-1))}{2N}

The last term is the Birthday bound where :math:`q` denotes the number
of oracle queries by the adversary and :math:`N` is the size of the set
:math:`\mathcal{R}`. Note that we used :math:`\mathcal{D'}` in the
nonce-based setting since :math:`\mathcal{D}` is not a nonce-respecting
CPA distinguisher. :math:`\mathcal{D'}` defines a reduction turning the
IV adversary :math:`\mathcal{D}` into a distinguisher against a
nonce-based encryption scheme :math:`\Sigma_{NR}`.

In EasyCrypt we can state our goal that we want to show in the following
lemma. Since we do not know the number of distinct elements of type
``rndness``, we instead use the probability of drawing an element which
is implemented as ``mu1 drndness witness``. [2]_ We denote the reduction
by ``Reduction(D)``. This module which has an IV distinguisher as
parameter is presented in the reduction section.

::

   lemma IV_security_NR &m:
     `| Pr[Exp_IV_CPA(D, O_IV_real(E)).run() @ &m: res]
        - Pr[Exp_IV_CPA(D, O_IV_ideal).run() @ &m: res] |
     <= 
     `| Pr[Exp_NR_CPA(CPA_real(E), Reduction(D)).run() @ &m: res]
        - Pr[Exp_NR_CPA(CPA_ideal, Reduction(D)).run() @ &m: res] | 
      + (q * (q - 1))%r / 2%r * mu1 drndness witness.

What are the steps for that in EasyCrypt to be able to prove the lemma
above? [//]: # (Will write this at the end)

Sampling
~~~~~~~~

The first step we take is to import the ``Birthday`` theory to be able
to use the lemmas stated about the birthday bound. More precisely, we
clone the theory to adapt it to the types we need. The operator q is
used to denote the number of queries made to the oracle.

Note that we write our proof inside a section to quantify all lemmas
over ``D`` - an IV distinguisher with restricted access to the memories
of oracles and the reduction. Therefore, we also use declare for the
operator ``q`` and local for the following modules and lemmas.

::

   declare op q : { int | 0 <= q } as ge0_q.

   local clone import Birthday as BB with 
     op q <- q,
     type T <- rndness,
     op uT <- drndness
   proof *. 
   realize ge0_q by exact: ge0_q.

The lemma about the birthday theory argues about an adversary against a
Sampler. [//]: # (Link to standard library) In order to apply this we
have to wrap an oracle around a sampler of the type ``Sampler``.
Therefore, we define new oracles for both the real and ideal side that
instead of sampling the randomness itself calls the sampler ``S``. The
code shows the real oracle, the ideal is defined respectively.

::

   local module O_IV_S_real (S: Sampler) (E: Enc_Scheme) : CPA_Oracle_IV_i = {
     var k : key
     
     proc init() : unit = {
       k <@ E.kgen();
       S.init();
     }
     
     proc enc(m : ptxt) : rndness * ctxt = {
       var r : rndness;
       var c : ctxt;
       
       r <@ S.s();
       c <@ E.enc(O_IV_S_real.k, r, m);
       
       return (r, c);
     }
   }.

So the first lemma that we actually proof in EasyCrypt states that
pushing the sampling into another module as we do in this oracle is
equivalent to the original oracle. So if we have the same key as
invariant between the modules ``O_IV_real`` and ``O_IV_S_real``, and we
relate the sampled randomness (from same distribution) the behavior
should be identical.

::

   local lemma Sample_real &m:
     Pr[Exp_IV_CPA(D, O_IV_real(E)).run() @ &m: res] =
     Pr[Exp_IV_CPA(D, O_IV_S_real(Sample, E)).run() @ &m: res].
   proof.
   byequiv => //. 
   proc; inline *.
   sim (: ={k}(O_IV_real, O_IV_S_real)).
   proc; inline *. 
   by auto.
   qed.

The lemma is stated using an equality between probability statements.
The proof works as described above. The important steps are the ``sim``
tactic to introduce the invariant and the ``rnd`` tactic that relates
the distributions of the sampled random values. [//]: # (need to explain
sim and auto tactic (Fix EC code))

Reduction
~~~~~~~~~

Counting
~~~~~~~~

Security statement
~~~~~~~~~~~~~~~~~~

Final lemma
~~~~~~~~~~~

.. [1]
   ``proof *.`` This line in a clone import will return all open
   assumptions of the cloned theory that we have to prove. They are
   displayed as a list in another buffer when using proof general in
   emacs.

.. [2]
   ``mu1 dtype element`` The operator ``mu1`` is defined in the theory
   of distributions in the standard library. It gives the probability to
   sample the ``element`` of some type from a distribution ``dtype``
   over that type.
