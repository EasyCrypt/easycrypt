(lang dune 3.13)
(using menhir 3.0)
(using dune_site 0.1)

(wrapped_executables false)

(name easycrypt)

(generate_opam_files true)

(package
 (name easycrypt)
 (sites (lib theories) (lib specs) (libexec commands))
 (depends
  (ocaml (>= 4.08.0))
  (batteries (>= 3))
  bitwuzla
  (camlp-streams (>= 5))
  camlzip
  cmdliner
  dune
  dune-build-info
  dune-site
  hex
  iter
  (ocaml-inifiles (>= 1.2))
  (pcre (>= 7))
  ppx_deriving
  ppx_deriving_yojson
  (progress (>= 0.2))
  (why3 (and (>= 1.8.0) (< 1.9)))
  yojson
  (zarith (>= 1.10))
))
