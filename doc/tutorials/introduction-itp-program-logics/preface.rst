   .. rubric:: “Program testing can be used to show the presence of
      bugs, but never to show their absence!”
      :name: program-testing-can-be-used-to-show-the-presence-of-bugs-but-never-to-show-their-absence

   .. rubric:: - Edsger W. Dijkstra
      :name: edsger-w.-dijkstra

Building reliable software is extremely tough. In order to guarantee the
reliability of software, there are plenty of different approaches that
can be employed, ranging from testing to various software building
methodologies. However, these are among the weakest guarantees we can
provide or are simply best practices that can ensure some level of
reliability.

With the explosion of software applications being used, bad software has
also been the source of literal explosions. For instance, NASA lost its
`Mars Climate
Orbiter <https://solarsystem.nasa.gov/missions/mars-climate-orbiter/in-depth/>`__
in 1998 due to a bug in converting units from the Imperial system to the
SI system. More recently, bad software led to the death of 346 people
onboard `two Boeing 737 MAX airplanes that crashed in 2018 and
2019 <https://www.reuters.com/article/uk-boeing-737max-timeline-idUKKBN27Y1RQ>`__.
Bad software has proven to be extremely costly.

On the opposite end of the spectrum of software reliability guarantees
lies the field of formal verification. The core idea behind formal
verification of software is to provide mathematical guarantees of
program behaviour based on specifications. It grew out of the field of
formal methods in mathematics and later computer-aided mathematical
proofs. So, formal verification rests on the firm foundations of formal
logic and reasoning.

Cryptography also follows the same pattern when it comes to reliability
guarantees. Testing and following best practices are still the go-to
methods to ensure the reliability of most cryptographic protocols; these
methods provide the weakest guarantees, as we discussed above. To
provide stronger guarantees, the ideas of formal verification have been
applied to cryptography, giving rise to the field of formally verified
cryptography. As these fields advanced and became more and more complex,
software tools that could aid us in this process were built. There are
several approaches to formal verification of cryptography, as we will
see. We will focus on one approach to the field (design-level security)
and work with EasyCrypt, a toolset that allows us to verify game-based
cryptographic proofs.

Formal verification: A brief history
------------------------------------

The ideas of formal verification can be traced back to Leibniz’s ideas
about *characteristica universalis* back in the 17th century. He
imagined it to be a universal conceptual language that could be used to
solve logical problems. However, we do not need to go that far back; for
our intents and purposes, formal methods and later computer-aided math
came into the limelight with the famous four-colour theorem being proven
with the help of computers by Appel and Haken (`Part
I <https://projecteuclid.org/journals/illinois-journal-of-mathematics/volume-21/issue-3/Every-planar-map-is-four-colorable-Part-I-Discharging/10.1215/ijm/1256049011.full>`__,
`Part
II <https://projecteuclid.org/journals/illinois-journal-of-mathematics/volume-21/issue-3/Every-planar-map-is-four-colorable-Part-II-Reducibility/10.1215/ijm/1256049012.full>`__)
in 1977.

The hypothesis of the four-colour theorem is quite simple and elegant.
It says, “Any planar map can be coloured with only four colours”. The
computer-aided proof by Appel and Haken attracted plenty of criticism
since it was done by performing an exhaustive case analysis of a billion
cases. An exhaustive case analysis means that the computer went through
every single case that could arise when trying to colour a map and came
back saying that four colours are all it takes. For an elegant problem,
the proposed computer-aided proof felt like using a sledgehammer to
crack a seemingly innocent nut, and this style of theorem proving
polarised the research community.

Nevertheless, the computer-aided proof of the four-colour theorem is a
significant milestone, and it set off more work and efforts in the field
of computer-aided mathematics. The field has grown considerably since
then, and there are a multitude of tools available for use. For
instance, one can use theorem provers like Coq or Isabelle to formally
prove general mathematical statements with the help of a computer. Or,
one can use specialised tools like EasyCrypt or Tamarin to work with
specific domains of formal verification, like cryptography in this case.
As for the four-colour theorem, a fully computer-free proof is yet to be
discovered.

Formal verification in cryptography
-----------------------------------

As the field of formal verification in math took off and got established
over the years, there was a problem brewing in the academic circles
dealing with cryptography. At its core, modern cryptography is based on
math, and to demonstrate different security properties of protocols, we
come up with mathematical proofs and guarantees about them. As the field
advanced, these proofs started getting fairly complex and often too
complicated for humans to go through. This problem can be best
illustrated with this excerpt from a `paper by Shai
Halevi <https://eprint.iacr.org/2005/181.pdf>`__:

“The problem is that as a community, we generate more proofs than we
carefully verify (and as a consequence some of our published proofs are
incorrect). I became acutely aware of this when I wrote my `EME\*
paper <https://eprint.iacr.org/2004/125.pdf>`__. After spending a
considerable effort trying to simplify the proof, I ended up with a
23-page proof of security for a — err — marginally useful
mode-of-operation for block ciphers. Needless to say, I do not expect
anyone in his right mind to even read the proof, let alone carefully
verify it.”

In the paper, Halevi highlights that cryptography as a field has
advanced to the point where the proofs are so complex that the field
could benefit from automation or, at the very least, some help from
machines. In a way, automated and computer-assisted are the two
approaches that are possible in the field of formal verification of
cryptography.

What is computer-aided cryptography?
------------------------------------

At this point, it is a good idea to read `Sec 1.1 of
JoC <https://joyofcryptography.com/pdf/chap1.pdf>`__ to understand what
cryptography is and is not. To summarise and add to the ideas from JoC,
modern cryptography deals with three main problems related to the
security of communication. They are the following:

1. **Privacy**: Protecting information from being accessed by
   unauthorised parties
2. **Integrity**: Protecting information from being tampered with or
   altered
3. **Authenticity**: Making sure the information is from an authentic
   source

Each of these properties can be defined as a mathematical property of
information, and claiming that a cryptographic protocol protects a
certain property is equivalent to proving that the information possesses
that mathematical property. Given that the proofs can be complicated and
hard to follow, the idea of using computers to verify the proofs comes
in here.

To illustrate this idea better, let us first meet Alice, Bob and Eve. We
assume that Alice wants to send a message to Bob and wants the
communication to be private. While Eve wants to eavesdrop on their
communication. One way to prove that a system of communication is secure
is to think of Alice, Bob and Eve playing a game where the objective of
the game for Alice and Bob is to communicate in a way that Eve can’t
differentiate between the messages and a random string of characters.
This would mean that Eve can extract just as much information from an
intercepted message as they can extract from random noise, implying that
the communication is private. This game can be modelled mathematically,
and we can prove that the communication was private. Proofs written in
this style are called game-based cryptographic proofs.

These ideas of representing information security properties as
mathematical properties and the games that Alice, Bob and Eve play
(game-based cryptographic proofs) are essentially the cornerstones of
provable and verifiable security. Depending on the definition of the
games and conditions related to them, the proofs can turn out to be
fairly intricate, as we established earlier. In the worst case,
handwritten proofs could even be wrong. Incorrect proofs translate to
significant security risks and reaffirm the need for the field of
formally verified cryptography. The complexity and difficulty of
verifying these proofs translate to a need for more automation and
computer-aided verification – tools like EasyCrypt are built to do just
that.

Criticism of computer-aided cryptography
----------------------------------------

Although the need for the field has been well established, it faces many
challenges and has its own shortcomings.

Only a few important protocols, such as Bluetooth, and TLS, are formally
verified, and it is less likely that verifying these protocols uncovers
serious flaws. This is because they are subject to extensive testing and
attacks. Whereas the protocols that aren’t used to support major
industrial applications generally aren’t subject to the same level of
scrutiny. They only receive limited manual testing, which leaves them
prone to errors. This is where formal verification can actually be used
to improve them significantly. The complexity of using the tools poses a
significant hurdle, and these protocols are left unverified.

Additionally, a high barrier to entry to the field compounds the problem
of protocols being left unverified. This is because teams developing
protocols can’t spend the time and effort required to go through the
process of formally verifying them.

In the end, the benefits of formal verification can seem marginal as the
tools themselves can have flaws, leading to the philosophical conundrum
of “Who will guard the guards themselves?”

As a response to these challenges, the field offers the following
rebuttals: 1. The field is still new, and the tooling is undergoing
active development. Once the tools mature and are easier to use, we can
expect the industry to move in the direction of requiring formal
verification for protocols to be put into use. For instance, the
development of the 5G protocol happened in close `collaboration with the
formal verification community <https://arxiv.org/pdf/1806.10360.pdf>`__
and is an encouraging move in the right direction 2. Even though the
tools might have flaws, the point to note here is that it would be
exceptionally hard for a mathematical proof to be wrong and also getting
past a formal verification check. So a flawed tool already provides
better security compared to a human-verified proof. The standard to beat
remains a highly specialised set of human eyes verifying a mathematical
proof. The argument of who guards the guards themselves already applies
to the current situation, and formal verification is, in fact, a
significant improvement. 3. The high barrier to entry remains a problem
with no simple solutions. However, this argument is akin to saying that
nuclear physics has a high barrier to entry. Although true, this
situation arises from the fact that these fields are highly specialised
and require years of training to reach a certain level of competence.

All in all there is plenty of work left to do in the field.
