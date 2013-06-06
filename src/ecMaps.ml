(* -------------------------------------------------------------------- *)
open EcUtils

(* -------------------------------------------------------------------- *)
module Map = struct
  module type OrderedType = Why3.Extmap.OrderedType

  module type S = sig
    include Why3.Extmap.S

    val to_stream : 'a t -> (key * 'a) Stream.t

    val dump :
         name:string
      -> (key -> 'a -> string)                   (* key printer *)
      -> (EcDebug.ppdebug -> (key * 'a) -> unit) (* value printer *)
      -> EcDebug.ppdebug -> 'a t -> unit
  end

  module Make(O : OrderedType) : S with type key = O.t = struct
    include Why3.Extmap.Make(O)

    let to_stream (m : 'a t) =
      let next =
        let enum = ref (start_enum m) in
          fun (_ : int) ->
            let aout = val_enum !enum in
              enum := next_enum !enum;
              aout
      in
        Stream.from next

    let dump ~name keyprinter valuepp pp (m : 'a t) =
      let ppkv pp (k, v) =
        EcDebug.onhlist pp (keyprinter k v) valuepp [(k, v)]
      in
        EcDebug.onhseq pp name ppkv (to_stream m)
  end

  module MakeBase(M : S) : Why3.Extmap.S
    with type    key         = M.key
     and type 'a t           = 'a M.t
     and type 'a enumeration = 'a M.enumeration
  =
  struct include M end
end

module Set = Why3.Extset

module EHashtbl = struct
  module type S = sig
    include Why3.Exthtbl.S
    val memo_rec : int -> ((key -> 'a) -> key -> 'a) -> key -> 'a   
  end

  module Make(T : Why3.Stdlib.OrderedHashedType) = struct
    include Why3.Exthtbl.Make(T)

    let memo_rec size f = 
      let h = create size in
      let rec aux x = 
        try find h x with Not_found -> let r = f aux x in add h x r; r in
      aux
  end
end

(* -------------------------------------------------------------------- *)
module MakeMSH (X : Why3.Stdlib.TaggedType) : sig
  module M : Map.S with type key = X.t
  module S : Set.S with module M = Map.MakeBase(M)
  module H : EHashtbl.S with type key = X.t
end = struct
  module T = Why3.Stdlib.OrderedHashed(X)
  module M = Map.Make(T)
  module S = Set.MakeOfMap(M)
  module H = EHashtbl.Make(T)
end

(* --------------------------------------------------------------------*)
module Int = struct
  type t = int
  let compare = (Pervasives.compare : t -> t -> int)
  let equal   = ((=) : t -> t -> bool)
  let hash    = (fun (x : int) -> x)
end

module Mint = Map.Make(Int)
module Sint = Set.MakeOfMap(Mint)
module Hint = Map.Make(Int)

(* --------------------------------------------------------------------*)
module Mstr = Map.Make(String)
module Sstr = Set.MakeOfMap(Mstr)
