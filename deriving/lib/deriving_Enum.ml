(* Copyright Jeremy Yallop 2007.
   This file is free software, distributed under the MIT license.
   See the file COPYING for details.
*)

open Deriving_Bounded

let rec rassoc (rkey : 'b) : ('a * 'b) list -> 'a = function
  | []                     -> raise Not_found
  | (a,b)::_ when b = rkey -> a
  | _::xs                  -> rassoc rkey xs

let rec last : 'a list -> 'a = function
    | []    -> raise (Invalid_argument "last")
    | [x]   -> x
    | _::xs -> last xs

module Deriving_Enum =
struct
(** Enum **)
module type Enum = sig
  type a
  val succ : a -> a
  val pred : a -> a
  val to_enum : int -> a
  val from_enum : a -> int
  val enum_from : a -> a list
  val enum_from_then : a -> a -> a list
  val enum_from_to : a -> a -> a list
  val enum_from_then_to : a -> a -> a -> a list
end

let startThenTo (start : int) (next : int) (until : int) : int list = 
  let step = next - start in
    if step <= 0 then invalid_arg "startThenTo" 
    else
      let rec upFrom current =
        if current > until then []
        else current :: upFrom (current+step)
      in
        upFrom start

let range : int -> int -> int list 
  = fun f t -> startThenTo f (f+1) t

module Defaults 
  (E : (sig
          type a
          val numbering : (a * int) list
        end)) : Enum with type a = E.a =
struct
  let firstCon = fst (List.hd E.numbering)
  let lastCon = fst (last E.numbering)

  type a = E.a
  let from_enum a = List.assoc a E.numbering
  let to_enum i = try rassoc i E.numbering with Not_found -> raise (Invalid_argument "to_enum")
  let succ s = try to_enum ((from_enum s) + 1) with Invalid_argument "to_enum" -> raise (Invalid_argument "succ")
  let pred s = try to_enum ((from_enum s) - 1) with Invalid_argument "to_enum" -> raise (Invalid_argument "pred")
  let enum_from_to x y = List.map to_enum (range (from_enum x) (from_enum y))
  let enum_from_then_to x y z = List.map to_enum (startThenTo (from_enum x) (from_enum y) (from_enum z))
  let enum_from_then x y = (enum_from_then_to x y 
                            (if from_enum y >= from_enum x then lastCon
                             else firstCon))
  let enum_from x = enum_from_to x lastCon
end


module Defaults' 
  (E : (sig
          type a
          val from_enum : a -> int
          val to_enum   : int -> a
        end))
  (B : Bounded with type a = E.a) : Enum with type a = E.a 
                                         and  type a = B.a =
struct
  include E
  let firstCon = B.min_bound
  let lastCon = B.max_bound

  let succ s = try to_enum ((from_enum s) + 1) with Invalid_argument "to_enum" -> raise (Invalid_argument "succ")
  let pred s = try to_enum ((from_enum s) - 1) with Invalid_argument "to_enum" -> raise (Invalid_argument "pred")
  let enum_from_to x y = List.map to_enum (range (from_enum x) (from_enum y))
  let enum_from_then_to x y z = List.map to_enum (startThenTo (from_enum x) (from_enum y) (from_enum z))
  let enum_from_then x y = (enum_from_then_to x y 
                            (if from_enum y >= from_enum x then lastCon
                             else firstCon))
  let enum_from x = enum_from_to x lastCon
end

module Enum_bool = Defaults(struct
  type a = bool
  let numbering = [false, 0; true, 1]
end)

module Enum_char = Defaults'(struct
  type a = char
  let from_enum = Char.code
  let to_enum = Char.chr
end) (Bounded_char)

module Enum_int = Defaults' (struct
  type a = int
  let from_enum i = i
  let to_enum i = i
end)(Bounded_int)

(* Can `instance Enum Float' be justified?
   For some floats `f' we have `succ f == f'. 
   Furthermore, float is wider than int, so from_enum will necessarily
   give nonsense on many inputs. *)

module Enum_unit = Defaults' (struct
  type a = unit
  let from_enum () = 0
  let to_enum = function
    | 0 -> ()
    | _ -> raise (Invalid_argument "to_enum")
end) (Bounded_unit)
end
include Deriving_Enum

type open_flag = Pervasives.open_flag  =
                 | Open_rdonly
                 | Open_wronly
                 | Open_append
                 | Open_creat
                 | Open_trunc
                 | Open_excl
                 | Open_binary
                 | Open_text
                 | Open_nonblock
                     deriving (Bounded,Enum)

type fpclass = Pervasives.fpclass =
               | FP_normal
               | FP_subnormal
               | FP_zero
               | FP_infinite
               | FP_nan
                   deriving (Bounded,Enum)
