(* -------------------------------------------------------------------- *)
open EcUtils
open EcMaps
open EcSymbols

(* -------------------------------------------------------------------- *)
type path = {
    p_node : path_node;
    p_tag  : int
  }

and path_node = 
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
let p_equal : path -> path -> bool = (==)
let p_hash p = p.p_tag

module Hspath = Why3.Hashcons.Make (struct 
  type t = path

  let equal_node p1 p2 = 
    match p1, p2 with
    | Pident id1, Pident id2 -> EcSymbols.equal id1 id2
    | Pqname (p1, id1), Pqname(p2, id2) -> 
        EcSymbols.equal id1 id2 && p_equal p1 p2
    | _ -> false

  let equal p1 p2 = equal_node p1.p_node p2.p_node

  let hash p = 
    match p.p_node with
    | Pident id -> Hashtbl.hash id
    | Pqname (p,id) -> Why3.Hashcons.combine p.p_tag (Hashtbl.hash id)
          
  let tag n p = { p with p_tag = n }

end)

module Path = MakeMSH (struct
  type t  = path
  let tag = p_hash
end)

module Sp = Path.S
module Mp = Path.M
module Hp = Path.H

let p_compare p1 p2 = p_hash p1 - p_hash p2

let mk_path node =
  Hspath.hashcons { p_node = node; p_tag = -1; }

let pident id      = mk_path (Pident id)
let pqname (p, id) = mk_path (Pqname(p,id))

(* -------------------------------------------------------------------- *)
let ep_equal (p1 : epath) (p2 : epath) =
  match p1, p2 with
  | EPath   p1      , EPath   p2       -> p_equal p1 p2
  | EModule (m1, s1), EModule (m2, s2) -> (EcIdent.id_equal m1 m2) && (s1 = s2)
  | _               , _                -> false

let ep_compare p1 p2 =
  if p1 == p2 then 0 else Pervasives.compare p1 p2

let ep_hash = function
  | EPath p -> p_hash p
  | EModule(i,_) -> EcIdent.tag i

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
  match p.p_node with
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
  | None   -> pident path
  | Some i ->
      let path = String.sub path 0 i
      and name = String.sub path (i+1) (String.length path - (i+1)) in
        pqname (create path, name)

(* -------------------------------------------------------------------- *)
let tolist =
  let rec aux l p = 
    match p.p_node with 
    | Pident x      -> x :: l
    | Pqname (p, x) -> aux (x :: l) p in
  aux []

(* -------------------------------------------------------------------- *)
let toqsymbol (p : path) =
  match p.p_node with
  | Pident x      -> ([], x)
  | Pqname (p, x) -> (tolist p, x)

(* -------------------------------------------------------------------- *)
let basename p = 
  match p.p_node with 
  | Pident x -> x
  | Pqname (_, x) -> x

(* -------------------------------------------------------------------- *)
let prefix p = 
  match p.p_node with 
  | Pident _ -> None
  | Pqname (p, _) -> Some p

(* -------------------------------------------------------------------- *)
let rec rootname p = 
  match p.p_node with 
  | Pident x -> x
  | Pqname (p, _) -> rootname p

(* -------------------------------------------------------------------- *)
let extend (p : path option) (x : symbol) =
  match p with
  | None   -> pident x
  | Some p -> pqname (p, x)

(* -------------------------------------------------------------------- *)
let rec concat p1 p2 = 
  match p2.p_node with
  | Pident x -> pqname(p1, x)
  | Pqname (p2,x) -> pqname(concat p1 p2, x)

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
    match path.p_node with
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
      match path.p_node with
      | Pident x      -> find1 x sm
      | Pqname (p, x) -> find1 x (find p sm)
    in

      fun (path : path) (m : 'a t) ->
        (find path { mp_value = None; mp_submaps = m }).mp_value
end
