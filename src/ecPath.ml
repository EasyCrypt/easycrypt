(* -------------------------------------------------------------------- *)
open EcUtils
open EcMaps
open EcSymbols
open EcIdent
(* -------------------------------------------------------------------- *)
type path = {
  p_node : path_node;
  p_tag  : int
}

and path_node =
| Psymbol of symbol
| Pqname  of path * symbol


(* -------------------------------------------------------------------- *)
let p_equal   = ((==) : path -> path -> bool)
let p_hash    = fun p -> p.p_tag
let p_compare = fun p1 p2 -> p_hash p1 - p_hash p2

module Hspath = Why3.Hashcons.Make (struct 
  type t = path

  let equal_node p1 p2 = 
    match p1, p2 with
    | Psymbol id1, Psymbol id2 -> EcSymbols.equal id1 id2
    | Pqname (p1, id1), Pqname(p2, id2) -> 
        EcSymbols.equal id1 id2 && p_equal p1 p2
    | _ -> false

  let equal p1 p2 = equal_node p1.p_node p2.p_node

  let hash p = 
    match p.p_node with
    | Psymbol id    -> Hashtbl.hash id
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

(* -------------------------------------------------------------------- *)
let mk_path node =
  Hspath.hashcons { p_node = node; p_tag = -1; }

let psymbol id   = mk_path (Psymbol id)
let pqname  p id = mk_path (Pqname(p,id))

(* -------------------------------------------------------------------- *)
let rec tostring p =
  match p.p_node with
  | Psymbol x    -> x
  | Pqname (p,x) -> Printf.sprintf "%s.%s" (tostring p) x

let tolist =
  let rec aux l p = 
    match p.p_node with 
    | Psymbol x     -> x :: l
    | Pqname (p, x) -> aux (x :: l) p in
  aux []

let toqsymbol (p : path) =
  match p.p_node with
  | Psymbol x     -> ([], x)
  | Pqname (p, x) -> (tolist p, x)

let basename p = 
  match p.p_node with 
  | Psymbol x     -> x
  | Pqname (_, x) -> x

let prefix p = 
  match p.p_node with 
  | Psymbol _ -> None
  | Pqname (p, _) -> Some p

let rec rootname p = 
  match p.p_node with 
  | Psymbol x     -> x
  | Pqname (p, _) -> rootname p

let rec p_size p =
  match p.p_node with
  | Psymbol _     -> 1
  | Pqname (p, _) -> 1 + (p_size p)

(* -------------------------------------------------------------------- *)
type mpath = {
  m_top  : mpath_top;
  m_args : mpath list;
  m_tag  : int;
}

and mpath_top =
[ | `Abstract of ident
  | `Concrete of path * path option ]

let m_equal   = ((==) : mpath -> mpath -> bool)
let m_hash    = fun p -> p.m_tag
let m_compare = fun p1 p2 -> m_hash p1 - m_hash p2

module Hsmpath = Why3.Hashcons.Make (struct 
  type t = mpath

  let equal m1 m2 = 
    let t = 
      match m1.m_top, m2.m_top with
      | `Abstract id1, `Abstract id2 -> EcIdent.id_equal id1 id2
      | `Concrete(p1,o1), `Concrete(p2,o2) ->
        p_equal p1 p2 && oall2 p_equal o1 o2
      | _, _ -> false in
    t && List.all2 m_equal m1.m_args m2.m_args

  let hash m = 
    let hash = 
      match m.m_top with
      | `Abstract id -> EcIdent.id_hash id
      | `Concrete(p, o) -> 
        ofold o (fun s h -> Why3.Hashcons.combine h (p_hash s))
          (p_hash p) in
    Why3.Hashcons.combine_list m_hash hash m.m_args
          
  let tag n p = { p with m_tag = n }
end)

module MPath = MakeMSH (struct
  type t  = mpath
  let tag = m_hash
end)

module Sm = MPath.S
module Mm = MPath.M
module Hm = MPath.H

(* -------------------------------------------------------------------- *)
let mk_mpath p args =
  Hsmpath.hashcons { m_top = p; m_args = args; m_tag = -1; }

let mpath_abs id args = mk_mpath (`Abstract id) args
let mpath_crt p args sp = mk_mpath (`Concrete(p,sp)) args

let m_apply mp args = 
  let args' = mp.m_args in
  if args' = [] then mk_mpath mp.m_top args 
  else (assert (args = []); mp)

let rec m_fv fv mp = 
  let fv = 
    match mp.m_top with 
    | `Abstract id -> EcIdent.fv_add id fv 
    | `Concrete _ -> fv in
  List.fold_left m_fv fv mp.m_args 



(* -------------------------------------------------------------------- *)

type xpath = {
  x_top : mpath;
  x_sub : path;
  x_tag : int;
}

let x_equal   = ((==) : xpath -> xpath -> bool)
let x_hash    = fun p -> p.x_tag
let x_compare = fun p1 p2 -> x_hash p1 - x_hash p2

module Hsxpath = Why3.Hashcons.Make (struct 
  type t = xpath

  let equal m1 m2 = 
    m_equal m1.x_top m2.x_top && p_equal m1.x_sub m2.x_sub

  let hash m = 
    Why3.Hashcons.combine (m_hash m.x_top) (p_hash m.x_sub)

  let tag n p = { p with x_tag = n }
end)

module XPath = MakeMSH (struct
  type t  = xpath
  let tag = x_hash
end)

module Sx = XPath.S
module Mx = XPath.M
module Hx = XPath.H

let xpath top sub =
  Hsxpath.hashcons { x_top = top; x_sub = sub; x_tag = -1; }

let x_fv fv xp = m_fv fv xp.x_top 

let xqname x s = xpath x.x_top (pqname x.x_sub s)
  

(* -------------------------------------------------------------------- *)
  
let rec m_tostring(m : mpath) = 
  let top, sub = 
    match m.m_top with
    | `Abstract id -> EcIdent.name id, ""
    | `Concrete (p,sub) ->
      tostring p, 
      ofold sub (fun p _ ->
        Format.sprintf ".%s" (tostring p)) "" in
  let args = 
    let a = m.m_args in
    if   a = [] then ""
    else
      let args = List.map m_tostring a in
      Printf.sprintf "(%s)" (String.concat ", " args) in
  Printf.sprintf "%s%s%s" top args sub

let x_tostring x = 
  Printf.sprintf "%s.%s" 
    (m_tostring x.x_top) (tostring x.x_sub)

(* -------------------------------------------------------------------- *)
let p_subst (s : path Mp.t) =
  if Mp.is_empty s then identity
  else
    let p_subst aux p =
      try  Mp.find p s
      with Not_found ->
        match p.p_node with
        | Psymbol _ -> p
        | Pqname(p1, id) -> 
          let p1' = aux p1 in
          if p1 == p1' then p else pqname p1' id in
    Hp.memo_rec 107 p_subst

(* -------------------------------------------------------------------- *)
let rec m_subst (sp : path -> path) (sm : mpath EcIdent.Mid.t) m =
  let args = List.smart_map (m_subst sp sm) m.m_args in
  match m.m_top with
  | `Concrete(p,sub) -> 
    let p' = sp p in
    let top = if p == p' then m.m_top else `Concrete(p',sub) in
    if m.m_top == top && m.m_args == args then m else 
      mk_mpath top args 
  | `Abstract id ->
    try 
      let m' = EcIdent.Mid.find id sm in
      m_apply m' args 
    with Not_found -> 
      if m.m_args == args then m else
        mk_mpath m.m_top args 
      
let m_subst (sp : path -> path) (sm : mpath EcIdent.Mid.t) =
  if sp == identity && EcIdent.Mid.is_empty sm then identity
  else m_subst sp sm

(* -------------------------------------------------------------------- *)

let x_subst (sm : mpath -> mpath) = 
  if sm == identity then identity 
  else fun x -> 
    let top = sm x.x_top in
    if x.x_top == top then x 
    else xpath top x.x_sub


