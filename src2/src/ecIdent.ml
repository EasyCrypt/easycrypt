(* -------------------------------------------------------------------- *)
open EcSymbols
open EcUtils
open EcMaps

(* -------------------------------------------------------------------- *)
type ident = { 
    id_symb : symbol;
    id_tag  : int;
  }

let name x = x.id_symb
let id_equal : ident -> ident -> bool = (==)
let id_compare i1 i2 = i2.id_tag - i1.id_tag 
let id_hash id = id.id_tag 

module MSH = Why3.Stdlib.MakeMSH (struct type t = ident let tag = id_hash end)

module Mid = struct 
  include MSH.M 

  let pp pp_key pp_value fmt m =
    let pp fmt (k, v) =
      Format.fprintf fmt "%a = %a" pp_key k pp_value v in
    if is_empty m then Format.fprintf fmt "{}"
    else 
      let pp =
        let first = ref true in
        fun k v ->
          if not !first then Format.fprintf fmt "@,%a" pp (k, v)
          else begin
            Format.fprintf fmt "%a" pp (k, v);
            first := false
          end
      in
      Format.fprintf fmt "{@,@[<v 2>  %a@]@,}" (fun fmt -> iter pp) m
end

module Sid = MSH.S
module Hid = MSH.H

type t     = ident

let create (x : symbol) = 
  { id_symb = x;
    id_tag  = EcUidgen.unique () }

let fresh (id : t) = create (name id)

(* -------------------------------------------------------------------- *)
module Map = struct
  type key  = t
  type 'a t = ((key * 'a) list) SymMap.t

  let empty : 'a t =
    SymMap.empty

  let add (id : key) (v : 'a) (m : 'a t) =
    SymMap.setdfl (fun p -> (id, v) :: (odfl [] p)) (name id) m

  let byident (id : key) (m : 'a t) =
    obind (SymMap.tryfind (name id) m) (List.tryassoc_eq id_equal id)

  let byname (x : symbol) (m : 'a t) =
    match SymMap.tryfind x m with
    | None | Some []     -> None
    | Some (idv :: _) -> Some idv 

  let allbyname (x : symbol) (m : 'a t) =
    odfl [] (SymMap.tryfind x m)

  let update (id : key) (f : 'a -> 'a) (m : 'a t) =
    let rec update1 (xs : (key * 'a) list) =
      match xs with
      | [] -> []
      | (id', v) :: xs when id_equal id id' -> (id', f v) :: xs
      | x :: xs -> x :: (update1 xs)
    in
    let n = name id in
    if SymMap.mem n m then
      SymMap.setdfl (function None -> [] | Some xs -> update1 xs) n m
    else m

   let merge m1 m2 = 
     SymMap.merge 
       (fun _ o1 o2 -> 
         match o1 with None -> o2 | Some l1 -> Some ((odfl [] o2) @ l1))
       m1 m2

   open EcFormat

   let pp ?(align = false) pp_value fmt (m : 'a t) =
     let pp_key =
       match align with
       | false -> pp_string
       | true  -> begin
         let i =
           SymMap.fold (fun x _ j -> max (String.length x) j) m 0
         in
           fun fmt s -> Format.fprintf fmt "%.*s" i s
       end
     in

     let pp fmt bindings =
       let pp_tag fmt id = pp_int fmt id.id_tag in 
       pp_list ~pre:"[" ~pst:"]"
         (pp_pair pp_tag pp_value) fmt bindings
     in
       SymMap.pp pp_key pp fmt m
end

let pp_ident fmt id = Format.fprintf fmt "%s" (name id)
