(* -------------------------------------------------------------------- *)
open EcUtils

(* -------------------------------------------------------------------- *)
module Map = struct
  module type OrderedType = Why3.Stdlib.Map.OrderedType

  module type S = sig
    include Why3.Stdlib.Map.S

    val to_stream : 'a t -> (key * 'a) Stream.t

    val dump :
         name:string
      -> (key -> 'a -> string)                   (* key printer *)
      -> (EcDebug.ppdebug -> (key * 'a) -> unit) (* value printer *)
      -> EcDebug.ppdebug -> 'a t -> unit
  end

  module Make(O : OrderedType) : S with type key = O.t = struct
    include Why3.Stdlib.Map.Make(O)

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
end

(* -------------------------------------------------------------------- *)
module MakeMSH (X : Why3.Stdlib.TaggedType) : sig
  module M : Map.S with type key = X.t
  module S : M.Set
  module H : Why3.Exthtbl.Hashtbl.S with type key = X.t
end = struct
  module T = Why3.Stdlib.OrderedHashed(X)
  module M = Map.Make(T)
  module S = M.Set
  module H = Why3.Exthtbl.Hashtbl.Make(T)
end

(* -------------------------------------------------------------------- *)
module Int = struct
  type t = int
  let compare = (Pervasives.compare : t -> t -> int)
  let equal (x : t) (y : t) = (x = y)
end

module Mint = Map.Make(Int)
module Sint = Mint.Set

(* -------------------------------------------------------------------- *)
module Mstr = Map.Make(String)
module Sstr = Mstr.Set
