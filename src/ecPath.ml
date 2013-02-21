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
| Psymbol of symbol
| Pident  of EcIdent.t
| Pqname  of path * symbol

type mpath = {
  m_node : path * mpath list list;
  m_tag  : int;
}

(* -------------------------------------------------------------------- *)
let p_equal : path -> path -> bool = (==)
let p_hash p = p.p_tag
let p_compare p1 p2 = p_hash p1 - p_hash p2

module Hspath = Why3.Hashcons.Make (struct 
  type t = path

  let equal_node p1 p2 = 
    match p1, p2 with
    | Psymbol id1, Psymbol id2 -> EcSymbols.equal id1 id2
    | Pident  id1, Pident  id2 -> EcIdent.id_equal id1 id2
    | Pqname (p1, id1), Pqname(p2, id2) -> 
        EcSymbols.equal id1 id2 && p_equal p1 p2
    | _ -> false

  let equal p1 p2 = equal_node p1.p_node p2.p_node

  let hash p = 
    match p.p_node with
    | Psymbol id    -> Hashtbl.hash id
    | Pident  id    -> EcIdent.tag id
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

let mk_path node =
  Hspath.hashcons { p_node = node; p_tag = -1; }

let psymbol id     = mk_path (Psymbol id)
let pident  id     = mk_path (Pident id)
let pqname (p, id) = mk_path (Pqname(p,id))

(* -------------------------------------------------------------------- *)
let m_equal : mpath -> mpath -> bool = (==)
let m_hash m = m.m_tag
let m_compare p1 p2 = m_hash p1 - m_hash p2

let args_equal = List.all2 (List.all2 m_equal) 

module Hsmpath = Why3.Hashcons.Make (struct 
  type t = mpath

  let equal_node m1 m2 = 
    let (p1,args1) = m1 in
    let (p2,args2) = m2 in
    p_equal p1 p2 && args_equal args1 args2 

  let equal m1 m2 = equal_node m1.m_node m2.m_node

  let hash m = 
    let (p,args) = m.m_node in 
    Why3.Hashcons.combine_list 
      (Why3.Hashcons.combine_list m_hash 0)
      p.p_tag args
          
  let tag n p = { p with m_tag = n }

end)

module MPath = MakeMSH (struct
  type t  = mpath
  let tag = m_hash
end)

module Sm = MPath.S
module Mm = MPath.M
module Hm = MPath.H

let mk_mpath node =
  Hsmpath.hashcons { m_node = node; m_tag = -1; }

let mpath p args = mk_mpath (p,args)

let mident  id = mk_mpath (pident  id, [[]])
let msymbol id = mk_mpath (psymbol id, [[]])
let mqname m id a = 
  let (p,args) = m.m_node in
  mk_mpath (pqname (p,id), a::args) 

let path_of_mpath m = fst m.m_node
let args_of_mpath m = snd m.m_node

(* TODO move this function in ecEnv, we should not export it *)
let mpath_of_path p = 
  let rec args p = 
    match p.p_node with
    | Pqname(p,_) -> [] :: args p
    | _           -> [[]] in
  mk_mpath (p,args p)


(* -------------------------------------------------------------------- *)
let rec tostring p =
  match p.p_node with
  | Psymbol x     -> x
  | Pident x      -> EcIdent.name x
  | Pqname (p, x) -> Printf.sprintf "%s.%s" (tostring p) x


(* -------------------------------------------------------------------- *)
let tolist =
  let rec aux l p = 
    match p.p_node with 
    | Psymbol x     -> x :: l
    | Pident x      -> EcIdent.name x :: l
    | Pqname (p, x) -> aux (x :: l) p in
  aux []

(* -------------------------------------------------------------------- *)
let toqsymbol (p : path) =
  match p.p_node with
  | Psymbol x     -> ([], x)
  | Pident x      -> ([], EcIdent.name x)
  | Pqname (p, x) -> (tolist p, x)

(* -------------------------------------------------------------------- *)
let basename p = 
  match p.p_node with 
  | Psymbol x     -> x
  | Pident  x     -> EcIdent.name x
  | Pqname (_, x) -> x

(* -------------------------------------------------------------------- *)
let prefix p = 
  match p.p_node with 
  | Psymbol _ | Pident _ -> None
  | Pqname (p, _) -> Some p

(* -------------------------------------------------------------------- *)
let rec rootname p = 
  match p.p_node with 
  | Psymbol x     -> x
  | Pident x      -> EcIdent.name x
  | Pqname (p, _) -> rootname p

(* -------------------------------------------------------------------- *)
let extend (p : path option) (x : symbol) =
  match p with
  | None   -> psymbol x
  | Some p -> pqname (p, x)

(* -------------------------------------------------------------------- *)
let rec m_tostring(m:mpath) = 
  let (p,args) = m.m_node in
  let app_tostring id a =
    if a = [] then id 
    else (String.concat (id^"(") (List.map m_tostring a))^")" in
  let rec aux p args = 
    match p.p_node, args with
    | Psymbol id , [a] -> app_tostring id a 
    | Pident id, [a]   -> app_tostring (EcIdent.name id) a
    | Pqname(p,id),a::args ->
        let s1 = aux p args in
        let s2 = app_tostring id a in
        Format.sprintf "%s.%s" s1 s2 
    | _, _ -> assert false in
  aux p args

  
          
