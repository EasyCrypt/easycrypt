(* -------------------------------------------------------------------- *)
open EcMaps
open EcUtils

(* -------------------------------------------------------------------- *)
module type Item = sig
  type t

  val equal  : t -> t -> bool
  val compare: t -> t -> int
end

(* -------------------------------------------------------------------- *)
module type Data = sig
  type data
  type effects

  val default   : data
  val isvoid    : data -> bool
  val noeffects : effects
  val union     : data -> data -> data * effects
end

(* -------------------------------------------------------------------- *)
module type S = sig
  type item
  type data
  type effects

  type t

  val initial: t

  val find  : item -> t -> item
  val same  : item -> item -> t -> bool
  val data  : item -> t -> data
  val set   : item -> data -> t -> t
  val isset : item -> t -> bool
  val union : item -> item -> t -> t * effects
  val domain: t -> item list
  val closed: t -> bool
  val opened: t -> int
end

(* -------------------------------------------------------------------- *)
module Make (I : Item) (D : Data) = struct
  type item    = I.t
  type data    = D.data
  type effects = D.effects

  type link =
    | Root of int * data
    | Link of item

  module M = Map.Make(I)

  type t = {
    mutable forest: link M.t;
    (*---*) nvoids: int;
  }

  (* ------------------------------------------------------------------ *)
  let initial = { forest = M.empty; nvoids = 0; }

  (* ------------------------------------------------------------------ *)
  let xfind =
    let rec follow (pitem : item) (item : item) (uf : t) =
      match oget (M.find_opt item uf.forest) with
      | Root (w, data) -> (item, w, Some data)
      | Link nitem ->
          let (nitem, _, _) as aout = follow item nitem uf in
            uf.forest <- M.add pitem (Link nitem) uf.forest;
            aout
    in
      fun (item : item) (uf : t) ->
        match M.find_opt item uf.forest with
        | None -> (item, 0, None)
        | Some (Root (w, data)) -> (item, w, Some data)
        | Some (Link next) -> follow item next uf

  (* ------------------------------------------------------------------ *)
  let find (item : item) (uf : t) =
    let (item, _, _) = xfind item uf in item

  (* ------------------------------------------------------------------ *)
  let same (item1 : item) (item2 : item) (uf : t) =
    I.equal (find item1 uf) (find item2 uf)

  (* ------------------------------------------------------------------ *)
  let data (item : item) (uf : t) =
    let (_, _, data) = xfind item uf in odfl D.default data

  (* ------------------------------------------------------------------ *)
  let set (item : item) (data : data) (uf : t) =
    let (item, w, olddata) = xfind item uf in
      { forest = M.add item (Root (w, data)) uf.forest;
        nvoids = uf.nvoids
                   - (odfl 0 (olddata |> omap (int_of_bool |- D.isvoid)))
                   + (int_of_bool (D.isvoid data)); }

  (* ------------------------------------------------------------------ *)
  let isset (item : item) (uf : t) =
    M.mem item uf.forest

  (* ------------------------------------------------------------------ *)
  let union (item1 : item) (item2 : item) (uf : t) =
    let (item1, w1, data1) = xfind item1 uf
    and (item2, w2, data2) = xfind item2 uf in

      if I.equal item1 item2 then
        (uf, D.noeffects)
      else
        let (data, effects) = D.union (odfl D.default data1) (odfl D.default data2) in
        let root = Root (w1 + w2, data) in
        let (link1, link2) =
  	      if   w1 >= w2
          then (root, Link item1)
          else (Link item2, root)
        in

        let uf =
          { forest = M.add item1 link1 (M.add item2 link2 uf.forest);
            nvoids = uf.nvoids
              - (odfl 0 (data1 |> omap (int_of_bool |- D.isvoid)) +
                 odfl 0 (data2 |> omap (int_of_bool |- D.isvoid)))
              + (int_of_bool (D.isvoid data)); }
        in
          (uf, effects)

  (* ------------------------------------------------------------------ *)
  let domain (uf : t) =
    M.keys uf.forest

  (* ------------------------------------------------------------------ *)
  let closed (uf : t) =
    uf.nvoids = 0

  (* ------------------------------------------------------------------ *)
  let opened (uf : t) =
    uf.nvoids
end

(* -------------------------------------------------------------------- *)
module type US = sig
  type item
  type t

  val initial : t

  val find  : item -> t -> item
  val union : item -> item -> t -> t
  val same  : item -> item -> t ->bool
end

(* -------------------------------------------------------------------- *)
module UMake (I : Item) = struct
  module D
    : Data with type data = unit and type effects = unit
  = struct
    type data    = unit
    type effects = unit

    let default : data =
      ()

    let isvoid (_ : data) =
      false

    let noeffects : effects =
      ()

    let union () () =
      ((), ())
  end

  module UF = Make(I)(D)

  type item    = I.t
  type data    = D.data
  type effects = D.effects

  type t = UF.t

  let initial = UF.initial

  let find (x : item) (uf : t) =
    UF.find x uf

  let union (x1 : item) (x2 : item) (uf : t) =
    fst (UF.union x1 x2 uf)

  let same (x1 : item) (x2 : item) (uf : t) =
    UF.same x1 x2 uf
end
