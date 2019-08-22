(lang dune 2.8)
(using menhir 2.0)

(generate_opam_files true)

(source (github EasyCrypt/easycrypt))
(license CeCILL-C)
(authors "IMDEA Software Institute" "Inria" "X")
(maintainers "pierre-yves@strub.nu")

(package
 (name easycrypt)
 (synopsis "EasyCrypt: Computer-Aided Cryptographic Proofs")
 (description "EasyCrypt is a toolset for reasoning about relational properties of probabilistic computations with adversarial code. Its main application is the construction and verification of game-based cryptographic proofs.")
 (depends
  (ocaml (>= 4.08.0))
  (why3 (and (>= 1.4.0) (< 1.5)))
  (zarith (>= 1.10))
  (ocaml-initfiles (>= 1.2))
  camlzip
  yojson
  (pcre (>= 7))
  (batteries (>= 2.3.0))))
