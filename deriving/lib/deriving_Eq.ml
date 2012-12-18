(* Copyright Jeremy Yallop 2007.
   This file is free software, distributed under the MIT license.
   See the file COPYING for details.
*)

module type Eq =
sig
  type a
  val eq : a -> a -> bool
end

module Eq_immutable(S : sig type a end) :
  Eq with type a = S.a =
struct
  type a = S.a
  let eq = (=)
end

module Eq_mutable(S : sig type a end) :
  Eq with type a = S.a =
struct
  type a = S.a
  let eq = (==)
end

module Eq_alpha(S : sig type a end) = struct type a = S.a let eq _ _ = assert false end
module Eq_int = Eq_immutable(struct type a = int end)
module Eq_bool = Eq_immutable(struct type a = bool end)
module Eq_float = Eq_immutable(struct type a = float end)
module Eq_unit = Eq_immutable(struct type a = unit end)
module Eq_char = Eq_immutable(struct type a = char end)
module Eq_int32 = Eq_immutable(struct type a = int32 end)
module Eq_int64 = Eq_immutable(struct type a = int64 end)
module Eq_nativeint = Eq_immutable(struct type a = nativeint end)

module Eq_string = Eq_mutable(struct type a = string end)
module Eq_ref (E : Eq) = Eq_mutable(struct type a = E.a ref end)
module Eq_array (E : Eq) = Eq_mutable(struct type a = E.a array end)

module Eq_option (E : Eq) 
  : Eq with type a = E.a option =
struct 
  type a = E.a option
  let eq l r = match l, r with
    | None, None -> true
    | Some l, Some r -> E.eq l r
    | _ -> false
end

module Eq_map_s_t (E : Eq) (M : Map.S)
  : Eq with type a = E.a M.t =
struct
  type a = E.a M.t
  let eq = M.equal (E.eq)
end  

module Eq_list (E : Eq) :
  Eq with type a = E.a list =
struct
  type a = E.a list
  let rec eq l r = match l, r with
    | [], [] -> true
    | (lfst::lrst), (rfst::rrst) when E.eq lfst rfst -> eq lrst rrst
    | _ -> false
end

