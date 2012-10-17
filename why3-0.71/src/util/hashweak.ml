(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-2011                                               *)
(*    François Bobot                                                      *)
(*    Jean-Christophe Filliâtre                                           *)
(*    Claude Marché                                                       *)
(*    Andrei Paskevich                                                    *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Library General Public           *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)

module ProdConsume :
sig
  type 'a t
  val create : unit -> 'a t
  val add : 'a -> 'a t -> unit
  val iter_remove : ('a -> unit) -> 'a t -> unit
end
= struct
  (* One thing can produce, one thing can consume concurrently *)

  type 'a cell =
    | Empty
    | Cons of 'a * 'a list
  and 'a list = 'a cell ref

  let rec iter f = function
    | Empty -> ()
    | Cons (x,l) -> f x; iter f !l

  (* a reference on a mutable singly linked list *)
  type 'a t = 'a list ref

  let create () = ref (ref (Empty))
  let add x t = t := ref (Cons(x,!t))
  let iter_remove f t =
    if !(!t) = Empty then () else
    let r = !t in (* atomic one cell of the list *)
    let l = !r in (* the content of the cell *)
    r := Empty; (* Work even if there are some production,
                   just not anymore the head *)
    iter f l
end

module type S = sig

  type key

  type 'a t

  val create : int -> 'a t
    (* create a hashtbl with weak keys *)

  val clear : 'a t -> unit

  val copy : 'a t -> 'a t

  val find : 'a t -> key -> 'a
    (* find the value bound to a key.
       Raises Not_found if there is no binding *)

  val mem : 'a t -> key -> bool
    (* test if a key is bound *)

  val set : 'a t -> key -> 'a -> unit
    (* bind the key _once_ with the given value *)

  val remove : 'a t -> key -> unit
    (* remove the value *)

  val iter : (key -> 'a -> unit) -> 'a t -> unit

  val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b

  val iterk : (key -> unit) -> 'a t -> unit

  val foldk : (key -> 'b -> 'b) -> 'a t -> 'b -> 'b

  val length : 'a t -> int

  val memoize : int -> (key -> 'a) -> (key -> 'a)
    (* create a memoizing function *)

  val memoize_rec : int -> ((key -> 'a) -> (key -> 'a)) -> (key -> 'a)
    (* create a memoizing recursive function *)

  val memoize_option : int -> (key option -> 'a) -> (key option -> 'a)
    (* memoizing functions on option types *)

end

let new_tbl_tag = let c = ref (-1) in
  fun () -> (incr c; !c)

type tag = {
  tag_map : ((int,Obj.t) Hashtbl.t) Lazy.t;
  tag_tag : int;
}

let create_tag tag = {
  tag_map = lazy (Hashtbl.create 3);
  tag_tag = tag;
}

let dummy_tag = {
  tag_map = lazy (failwith "dummy tag");
  tag_tag = -1;
}

let tag_equal : tag -> tag -> bool = (==)

let tag_hash k = assert (k != dummy_tag); k.tag_tag

module type Weakey =
sig
  type t
  val tag : t -> tag
end

module Make (S : Weakey) = struct

  type key = S.t

  module H = Weak.Make (struct
    type t = S.t
    let hash k = (S.tag k).tag_tag
    let equal k1 k2 = S.tag k1 == S.tag k2
  end)

  type 'a t = {
    tbl_set : H.t;
    tbl_tag : int;
  }

  let tag_map k = Lazy.force (S.tag k).tag_map

  let find (t : 'a t) k : 'a =
    Obj.obj (Hashtbl.find (tag_map k) t.tbl_tag)

  let mem t k = Hashtbl.mem (tag_map k) t.tbl_tag

  let set (t : 'a t) k (v : 'a) =
    Hashtbl.replace (tag_map k) t.tbl_tag (Obj.repr v);
    ignore (H.merge t.tbl_set k)

  let remove t k =
    Hashtbl.remove (tag_map k) t.tbl_tag;
    H.remove t.tbl_set k

  let iterk fn t = H.iter fn t.tbl_set
  let foldk fn t = H.fold fn t.tbl_set

  let iter  fn t = H.iter (fun k -> fn k (find t k)) t.tbl_set
  let fold  fn t = H.fold (fun k -> fn k (find t k)) t.tbl_set

  (** This table is just a hack to keep alive the weak hashset :
      Indeed that circunvent a strange behavior/bug of weak hashset,
      when a weak hashset is garbage collected it will not anymore
      remove the dead elements from it. So during finalize or if the
      hashset is keep alive, we can acces invalid pointer...

      So to summarize we keep alive the weak hashset until we don't need them
      anymore.
  *)
  let gen_table = Hashtbl.create 5

  let tbl_final_aux t =
    iterk (fun k -> Hashtbl.remove (tag_map k) t.tbl_tag) t

  let tbl_final t =
    tbl_final_aux t;
    (** We don't need anymore the weak hashset, we can release it *)
    Hashtbl.remove gen_table t.tbl_tag

  (** All the hashweak that can be collected. When a hashweak is
      garbage collected we need to remove its tag from the key
      hashtable. Since finalisation can be triggered at anytime even
      when the key hashtable are in an inconsistent state, we need to
      delay the actual removing until it can be done safely.
      t_collected contains the delayed hashweak *)
  let t_collected = ProdConsume.create ()

  (** Do really the removing *)
  let collect () = ProdConsume.iter_remove tbl_final t_collected

  let create n =
    let t = {
      tbl_set = H.create n;
      tbl_tag = new_tbl_tag () }
    in
    Hashtbl.add gen_table t.tbl_tag t.tbl_set;
    Gc.finalise (fun t -> ProdConsume.add t t_collected) t;
    t

  let find x y = collect (); find x y
  let set x y z = collect (); set x y z

  let clear t = collect (); tbl_final_aux t; H.clear t.tbl_set

  let length t = H.count t.tbl_set

  let copy t =
    collect ();
    let t' = create (length t) in
    iter (set t') t;
    t'

  let memoize n fn =
    let h = create n in fun e ->
      try find h e
      with Not_found ->
        let v = fn e in
        set h e v;
        v

  let memoize_rec n fn =
    let h = create n in
    let rec f e =
      try find h e
      with Not_found ->
        let v = fn f e in
        set h e v;
        v
    in
    f

  let memoize_option n fn =
    let v = lazy (fn None) in
    let fn e = fn (Some e) in
    let fn = memoize n fn in
    function
      | Some e -> fn e
      | None -> Lazy.force v

end

