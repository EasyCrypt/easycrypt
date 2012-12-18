(* Copyright Jeremy Yallop 2007.
   This file is free software, distributed under the MIT license.
   See the file COPYING for details.
*)

(* Extend the OCaml grammar to include the `deriving' clause after
   type declarations in structure and signatures. *)

module Deriving (S : Camlp4.Sig.Camlp4Syntax): Camlp4.Sig.Camlp4Syntax
