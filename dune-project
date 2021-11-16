(lang dune 2.8)
(using menhir 2.0)

(generate_opam_files true)

(package
 (name easycrypt)
 (depends
  (ocaml (>= 4.08.0))
  (batteries (>= 2.3.0))
  camlzip
  dune-build-info
  (ocaml-inifiles (>= 1.2))
  (pcre (>= 7))
  (why3 (and (>= 1.4.0) (< 1.5)))
  yojson
  (zarith (>= 1.10))
))
