(* -------------------------------------------------------------------- *)
open EcUtils
open EcSymbols

(* -------------------------------------------------------------------- *)
type path =
  | Pident of EcIdent.t
  | Pqname of path * EcIdent.t

let rec p_equal p1 p2 = 
  p1 == p2 || match p1, p2 with
  | Pident id1, Pident id2 -> EcIdent.id_equal id1 id2
  | Pqname (p1,id1), Pqname(p2,id2) -> 
      EcIdent.id_equal id1 id2 && p_equal p1 p2
  | _, _ -> false

let rec p_compare p1 p2 =
  if p1 == p2 then 0
  else match p1, p2 with
  | Pident id1, Pident id2 -> EcIdent.id_compare id1 id2
  | Pident _, _ -> -1
  | Pqname(p1, id1), Pqname(p2,id2) ->
      let cmp = EcIdent.id_compare id1 id2 in
      if cmp = 0 then p_compare p1 p2 else cmp
  | _, Pident _ -> 1

(* -------------------------------------------------------------------- *)
(* TODO : Remove this function *)
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
let rec rootname = function
  | Pident x -> x
  | Pqname (p, _) -> rootname p

(* -------------------------------------------------------------------- *)
let extend (p : path option) (x : EcIdent.t) =
  match p with
  | None   -> Pident x
  | Some p -> Pqname (p, x)

(* -------------------------------------------------------------------- *)
module Mp = Map.Make (struct type t = path let compare = p_compare end)

(* -------------------------------------------------------------------- *)
let id_top       = EcIdent.create "Top"
let id_pervasive = EcIdent.create "Pervasive"
let id_int       = EcIdent.create "int"
let id_real      = EcIdent.create "real"
let id_bool      = EcIdent.create "bool"

let id_true      = EcIdent.create "true"
let id_false     = EcIdent.create "false"
let id_not       = EcIdent.create "prefix !"
let id_and       = EcIdent.create "infix &&"
let id_or        = EcIdent.create "infix ||"
let id_imp       = EcIdent.create "infix =>"

let p_top        = extend None id_top
let p_pervasive  = extend (Some p_top) id_pervasive
let pervasive id = extend (Some p_pervasive) id

let p_int        = pervasive id_int
let p_real       = pervasive id_real
let p_bool       = pervasive id_bool

let p_true       = pervasive id_true
let p_false      = pervasive id_false
let p_not        = pervasive id_not 
let p_and        = pervasive id_and
let p_or         = pervasive id_or
let p_imp        = pervasive id_imp


