(* -------------------------------------------------------------------- *)
open EcUtils
open EcSymbols

(* -------------------------------------------------------------------- *)
type path =
  | Pident of EcIdent.t
  | Pqname of path * EcIdent.t

let equal : path -> path -> bool = (=)

(* -------------------------------------------------------------------- *)
let rec create (path : string) =
  match try_nf (fun () -> String.rindex path '.') with
    | None   -> Pident (EcIdent.create path)
    | Some i ->
      let path = String.sub path 0 i
      and name = String.sub path (i+1) (String.length path - (i+1)) in
        Pqname (create path, EcIdent.create name)

(* -------------------------------------------------------------------- *)
let rec tolist (p : path) =
  match p with
  | Pident x      -> [x]
  | Pqname (p, x) -> x :: (tolist p)

(* -------------------------------------------------------------------- *)
let toqsymbol (p : path) =
  match p with
  | Pident x      -> ([], EcIdent.name x)
  | Pqname (p, x) ->
    let scope = List.rev (tolist p) in
      (List.map EcIdent.name scope, EcIdent.name x)

(* -------------------------------------------------------------------- *)
module Mp = Map.Make (struct type t = path let compare = compare end)
