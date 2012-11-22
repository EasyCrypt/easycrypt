(* -------------------------------------------------------------------- *)
open Utils

type symbol = string

type path =
  | Pident of symbol
  | Pqname of symbol * path

let rec create (path : string) =
  match try_nf (fun () -> String.index path '.') with
    | None   -> Pident path
    | Some i ->
      let qname = String.sub path 0 i in
      let path  = String.sub path i (String.length path - i) in
        Pqname (qname, create path)

let toqsymbol =
  let rec toqsymbol scope = function
    | Pident x       -> (List.rev scope, x)
    | Pqname (nm, p) -> toqsymbol (nm :: scope) p
  in
    fun (p : path) -> toqsymbol [] p

let path_equal = (=)
