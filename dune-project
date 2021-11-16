(lang dune 2.8)
(using menhir 2.0)

(generate_opam_files true)

(package
 (name easycrypt)
 (depends
  (ocaml (>= 4.08.0))
  (why3 (and (>= 1.4.0) (< 1.5)))
  (zarith (>= 1.10))
  (ocaml-inifiles (>= 1.2))
  camlzip
  yojson
  (pcre (>= 7))
  (batteries (>= 2.3.0))))
