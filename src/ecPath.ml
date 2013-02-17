(* -------------------------------------------------------------------- *)
open EcUtils
open EcMaps
open EcSymbols

(* -------------------------------------------------------------------- *)
type path =
  | Pident of symbol
  | Pqname of path * symbol

type epath =
| EPath   of path
| EModule of EcIdent.t * symbol option

type cref =
| CRefPath of path                      (* Top-level component    *)
| CRefMid  of EcIdent.t                 (* Bound module component *)

type xcref = cref * xcref list

(* -------------------------------------------------------------------- *)
let p_equal =
  let rec p_equal (p1 : path) (p2 : path) =
    match p1, p2 with
    | Pident id1, Pident id2 -> EcSymbols.equal id1 id2
    | Pqname (p1, id1), Pqname(p2, id2) -> 
        EcSymbols.equal id1 id2 && p_equal p1 p2
    | _, _ -> false
  in
    fun p1 p2 -> p1 == p2 || p_equal p1 p2

let p_compare p1 p2 =
  let rec p_compare (p1 : path) (p2 : path) =
    match p1, p2 with
    | Pident id1, Pident id2 -> EcSymbols.compare id1 id2
    | Pident _, _ -> -1
    | _, Pident _ -> 1
    | Pqname(p1, id1), Pqname(p2,id2) ->
        let cmp = EcSymbols.compare id1 id2 in
          if cmp = 0 then p_compare p1 p2 else cmp
  in
    if p1 == p2 then 0 else p_compare p1 p2

(* -------------------------------------------------------------------- *)
let ep_equal (p1 : epath) (p2 : epath) =
  match p1, p2 with
  | EPath   p1      , EPath   p2       -> p_equal p1 p2
  | EModule (m1, s1), EModule (m2, s2) -> (EcIdent.id_equal m1 m2) && (s1 = s2)
  | _               , _                -> false

let ep_compare p1 p2 =
  if p1 == p2 then 0 else Pervasives.compare p1 p2

(* -------------------------------------------------------------------- *)
let cref_equal (p1 : cref) (p2 : cref) =
  match p1, p2 with
  | CRefPath p1, CRefPath p2 -> p_equal p1 p2
  | CRefMid  m1, CRefMid m2  -> EcIdent.id_equal m1 m2
  | _          , _           -> false

(* -------------------------------------------------------------------- *)
let rec xcref_equal ((p1, args1) : xcref) ((p2, args2) : xcref) =
     (cref_equal p1 p2)
  && (List.length args1 = List.length args2)
  && (List.for_all2 xcref_equal args1 args2)

(* -------------------------------------------------------------------- *)
let rec tostring p =
  match p with
  | Pident x ->
      Printf.sprintf "%s" x
  | Pqname (p, x) ->
      Printf.sprintf "%s.%s" (tostring p) x

(* -------------------------------------------------------------------- *)
let ep_tostring = function
  | EPath p ->
      tostring p

  | EModule (mid, None) ->
      EcIdent.tostring mid

  | EModule (mid, Some x) ->
      Printf.sprintf "%s.%s" (EcIdent.tostring mid) x

(* -------------------------------------------------------------------- *)
let cref_tostring = function
  | CRefPath p ->
      tostring p

  | CRefMid mid ->
      EcIdent.tostring mid

(* -------------------------------------------------------------------- *)
let rec create (path : string) =
  match try_nf (fun () -> String.rindex path '.') with
  | None   -> Pident path
  | Some i ->
      let path = String.sub path 0 i
      and name = String.sub path (i+1) (String.length path - (i+1)) in
        Pqname (create path, name)

(* -------------------------------------------------------------------- *)
let tolist =
  let rec aux l = function
    | Pident x      -> x :: l
    | Pqname (p, x) -> aux (x :: l) p in
  aux []

(* -------------------------------------------------------------------- *)
let toqsymbol (p : path) =
  match p with
  | Pident x      -> ([], x)
  | Pqname (p, x) -> (tolist p, x)

(* -------------------------------------------------------------------- *)
let basename = function
  | Pident x -> x
  | Pqname (_, x) -> x

(* -------------------------------------------------------------------- *)
let prefix = function
  | Pident _ -> None
  | Pqname (p, _) -> Some p

(* -------------------------------------------------------------------- *)
let rec rootname = function
  | Pident x -> x
  | Pqname (p, _) -> rootname p

(* -------------------------------------------------------------------- *)
let extend (p : path option) (x : symbol) =
  match p with
  | None   -> Pident x
  | Some p -> Pqname (p, x)

(* -------------------------------------------------------------------- *)
let rec concat p1 p2 = 
  match p2 with
  | Pident x -> Pqname(p1, x)
  | Pqname (p2,x) -> Pqname(concat p1 p2, x)

(* -------------------------------------------------------------------- *)
module PathComparable = struct
  type t = path
  let compare = p_compare
end

module Mp = Map.Make(PathComparable)
module Sp = Mp.Set

(* -------------------------------------------------------------------- *)
module EPathComparable = struct
  type t = epath
  let compare = ep_compare
end

module Mep = Map.Make(EPathComparable)
module Sep = Mep.Set

(* -------------------------------------------------------------------- *)
module Msubp = struct
  type 'a t = ('a submaps) Msym.t

  and 'a submaps = {
    mp_value   : 'a option;
    mp_submaps : 'a t;
  }

  let empty : 'a t = Msym.empty

  let empty_sm : 'a submaps = {
    mp_value   = None;
    mp_submaps = empty;
  }

  let rec update up (path : path) (m : 'a t) =
    match path with
    | Pident x -> up x m
    | Pqname (path, x) ->
        let up supx supm =
          let doupdate subxsm =
            let supxsm = odfl empty_sm subxsm in
              Some { supxsm with mp_submaps = up x supxsm.mp_submaps }
          in
            Msym.change doupdate supx supm
        in
          update up path m

  let add (path : path) (v : 'a) (m : 'a t) =
    let add1 (x : symbol) (v : 'a) (m : 'a t) =
      let doupdate sm =
        let sm = odfl empty_sm sm in
          Some { sm with mp_value = Some v }
      in
        Msym.change doupdate x m
    in
      update (add1^~ v) path m

  let find =
    let find1 (x : symbol) (sm : 'a submaps) =
      match Msym.find_opt x sm.mp_submaps with
      | None -> { mp_value   = sm.mp_value;
                  mp_submaps = empty; }

      | Some subsm -> begin
          match subsm.mp_value with
          | None   -> { subsm with mp_value = sm.mp_value }
          | Some _ -> subsm
        end
    in

    let rec find (path : path) (sm : 'a submaps) =
      match path with
      | Pident x      -> find1 x sm
      | Pqname (p, x) -> find1 x (find p sm)
    in

      fun (path : path) (m : 'a t) ->
        (find path { mp_value = None; mp_submaps = m }).mp_value
end
