(* -------------------------------------------------------------------- *)
open Utils
open Symbols

(* -------------------------------------------------------------------- *)
type path =
  | Pident of Ident.t
  | Pqname of path * Ident.t

let equal : path -> path -> bool = (=)

(* -------------------------------------------------------------------- *)
let rec create (path : string) =
  match try_nf (fun () -> String.rindex path '.') with
    | None   -> Pident (Ident.create path)
    | Some i ->
      let path = String.sub path 0 i
      and name = String.sub path (i+1) (String.length path - (i+1)) in
        Pqname (create path, Ident.create name)

(* -------------------------------------------------------------------- *)
let rec tolist (p : path) =
  match p with
  | Pident x      -> [x]
  | Pqname (p, x) -> x :: (tolist p)

(* -------------------------------------------------------------------- *)
let toqsymbol (p : path) =
  match p with
  | Pident x      -> ([], Ident.name x)
  | Pqname (p, x) ->
    let scope = List.rev (tolist p) in
      (List.map Ident.name scope, Ident.name x)

(* -------------------------------------------------------------------- *)
module Mp = Map.Make (struct type t = path let compare = compare end)
