(lang dune 3.6)
(using menhir 2.0)
(using dune_site 0.1)

(wrapped_executables false)

(name easycrypt)

(generate_opam_files true)

(package
 (name easycrypt)
 (sites (lib theories) (libexec commands))
 (depends
  (ocaml (>= 4.08.0))
  (batteries (>= 3))
  (camlp-streams (>= 5))
  camlzip
  (dune (>= 3.6))
  dune-build-info
  dune-site
  (ocaml-inifiles (>= 1.2))
  (pcre (>= 7))
  (why3 (and (>= 1.7.0) (< 1.8)))
  yojson
  (zarith (>= 1.10))
))
