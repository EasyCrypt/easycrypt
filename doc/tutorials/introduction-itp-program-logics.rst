Introduction to Computer-Aided Cryptographic Proofs
===================================================

.. note::

   This guide is reproduced and updated, with permission, from `Tejas
   Shah <https://tejaswrites.com/>`__\ ’s `Joy of
   EasyCrypt <https://github.com/tejasanilshah/the-joy-of-easycrypt>`__.

   We are grateful to Tejas and Dominique Unruh for developing it and
   allowing us to use it here.

This repo consists of learning material for EasyCrypt, a toolset for
reasoning about cryptographic proofs. It inspired by and written in the
style of `Software
Foundations <https://softwarefoundations.cis.upenn.edu/>`__, a series of
electronic textbooks that explain the mathematical underpinnings of
reliable software. For concepts related to cryptography we aim to track
`The Joy of Cryptography <https://joyofcryptography.com/>`__ (JoC), an
open-source undergrad textbook for cryptography.

Target audience
---------------

Anyone curious about cryptography and who wants to understand formal
verification and computer-aided cryptography in the computational
approach to design-level security [1]_. In line with that, we assume
that the reader is completely new to the field of cryptography, and for
some concepts, the reader will be referred to JoC when needed. We will
offer simplified explanations of concepts required for formal
verification as we go. We expect familiarity with discrete mathematics,
data structures and algorithms, a basic familiarity with the command
line and the ability to work with the Emacs text editor. Essentially, if
you have a little programming experience, then you should be able to
work your way through the ideas presented in this work.

Although Emacs is pretty complex, we only expect the reader to know how
to open files and navigate them to begin with. These skills can be
learnt quickly with the tutorial that is presented upon a fresh install
of Emacs. Additionally, the `guided tour of
Emacs <https://www.gnu.org/software/emacs/tour/>`__ is helpful for those
who want to know more about what Emacs is capable of and don’t want to
go through the entire tutorial.

As with the original text, joy is not guaranteed. Formal verification
can be challenging, so we ask you to be patient and keep working with
the material. A tip that we can provide is to start and learn as you go.

.. [1]
   If you do not understand what that means, it is alright, we develop
   the required background.
