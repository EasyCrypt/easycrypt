(lang dune 2.8)
(using menhir 2.0)
(using dune_site 0.1)

(wrapped_executables false)

(name easycrypt)

(generate_opam_files true)

(package
 (name easycrypt)
 (sites (lib theories))
 (depends
  (ocaml (>= 4.08.0))
  (batteries (>= 3))
  camlzip
  dune-build-info
  dune-site
  (ocaml-inifiles (>= 1.2))
  (pcre (>= 7))
  (why3 (and (>= 1.4.0) (< 1.5)))
  yojson
  (zarith (>= 1.10))
))
