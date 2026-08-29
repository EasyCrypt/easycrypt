Tutorial Overview
=================

This tutorial is intended as a ladder, each rung of which takes you from
“I’ve heard enough about EasyCrypt to end up here” to “I’ve proved a
cryptographically-relevant (if not interesting) thing.”

The rungs are roughly intended to also progressively introduce more
*proof* complexity, starting from simple proofs on data structures
(Merkle-Damgård and Merkle trees) to simple reductions (relating
collision resistance and second preimage resistance; and proving
semantic security of the KEM+DEM construction) and to reductions with
oracles (securely constructing symmetric encryption from a PRF; and
proving CCA security of the KEM+DEM construction).

The tutorials are designed to be engaged with in sequence. However, we
make back-references (when we remember), and also refer to reference
material from the tutorial content for deeper discussions of some
concepts, or for reference access to related information.

Before we get to proving anything, we make a best effort attempt at
guiding you through setting your environment up. It assumes you are
confidently in control of your computer (we can only cover installation
and setup generically), and that you have had minimal exposure (as would
be suffered in a good undergraduate degree in computer science with
cryptography) to functional programming, program logics, and
cryptographic proofs.

What you’ll need
----------------

- A reasonable computer: in interactive mode, your brain and fingers are
  a lot more limiting than your CPU. (I am writing this on an 2GHz CPU
  from 2019, and have not had any issues even when checking proofs
  non-interactively, where the CPU *is* the bottleneck.) That being
  said, EasyCrypt does consume some memory and you should probably
  expect things to go wrong, slow, or both if you have less than 4GB of
  RAM. Having multiple cores helps, but we typically won’t use more than
  4 at a time unless you choose to install more SMT solvers than those
  we recommend.

- Ideally, a Unix-y operating system (Linux, BSD, MacOS, WSL). You can
  probably make things work on Windows or on stranger operating systems,
  but we can’t help you do it, and likely won’t even try.

- About two hours of loose attention for installation, then a variable
  amount of time for each tutorial. Each can be tackled independently,
  but leaving too long between sessions may expose you to severe and
  breaking changes in EasyCrypt.
