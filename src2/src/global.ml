(* -------------------------------------------------------------------- *)
open Symbols
open Parsetree
open Typedtree

(* -------------------------------------------------------------------- *)
module Module = struct
  type eobj = [
    | `PEVar of (symbol list * pty)
    | `PEFun of (function_decl * function_body)
  ]

  let start (name : symbol) =
    ()

  let closed () =
    ()

  let abort () =
    ()

  let extend (eobj : eobj) =
    ()
end
