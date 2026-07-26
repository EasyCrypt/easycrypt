(lang dune 3.13)
(using menhir 3.0)
(using dune_site 0.1)

(wrapped_executables false)

(name easycrypt)

(generate_opam_files true)

(package
 (name easycrypt)
 (sites (lib theories) (libexec commands) (lib doc) (lib config))
 (depends
  (ocaml (>= 4.08.0))
  (batteries (>= 3.9))
  bitwuzla-cxx
  (camlp-streams (>= 5))
  camlzip
  dune
  dune-build-info
  dune-site
  markdown
  (pcre2 (>= 8))
  (why3 (and (>= 1.8.0) (< 1.9)))
  yojson
  (zarith (>= 1.10))
))

(package
 (name tooling)
 (synopsis "EasyCrypt tooling daemon (LSP + MCP)")
 (description
  "Modular daemon wrapping `ec llm`. Serves LSP to editors and MCP to LLM clients over a shared session pool. PoC scaffolding; see doc/tooling-poc-plan.md.")
 (depends
  (ocaml (>= 5.1.0))
  dune
  eio
  eio_main
  cmdliner
  logs
  yojson
  notty
))
