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
let tolist =
  let rec aux l = function
    | Pident x      -> x :: l
    | Pqname (p, x) -> aux (x :: l) p in
  aux []

(* -------------------------------------------------------------------- *)
let toqsymbol (p : path) =
  match p with
  | Pident x      -> ([], EcIdent.name x)
  | Pqname (p, x) ->
    let scope = tolist p in
      (List.map EcIdent.name scope, EcIdent.name x)

(* -------------------------------------------------------------------- *)
let basename = function
  | Pident x -> x
  | Pqname (_, x) -> x

(* -------------------------------------------------------------------- *)
let extend (p : path option) (x : EcIdent.t) =
  match p with
  | None   -> Pident x
  | Some p -> Pqname (p, x)

(* -------------------------------------------------------------------- *)
module Mp = Map.Make (struct type t = path let compare = compare end)
