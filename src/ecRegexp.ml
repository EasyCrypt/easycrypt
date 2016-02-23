(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2016 - Inria
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcUtils

(* -------------------------------------------------------------------- *)
type split =
  | Text  of string
  | Delim of string

(* -------------------------------------------------------------------- *)
module type CORE = sig
  type error
  type regexp
  type subst
  type match_

  exception Error of error

  val quote   : string -> string
  val regexp  : string -> regexp
  val subst   : string -> subst
  val exec    : ?pos:int -> regexp -> string -> match_ option
  val split   : ?pos:int -> regexp -> string -> split list
  val sub     : regexp -> subst -> string -> string
  val extract : regexp -> string -> (string option array) array

  module Match : sig
    val count  : match_ -> int
    val group  : match_ -> int -> string option
    val groups : match_ -> (string option) array
    val offset : match_ -> int -> (int * int) option
  end
end

(* -------------------------------------------------------------------- *)
module PcreCore : CORE = struct
  type regexp  = Pcre.regexp
  type subst   = Pcre.substitution
  type match_  = Pcre.substrings

  type error =
    | PCREError of Pcre.error
    | InvalidSubString of int
    | InvalidBackRef

  exception Error of error

  let wrap (f : 'a -> 'b) (x : 'a) =
    try  f x
    with Pcre.Error err -> raise (Error (PCREError err))

  let quote  (x : string) = (wrap Pcre.quote ) x
  let regexp (x : string) = (wrap Pcre.regexp) x
  let subst  (x : string) = (wrap Pcre.subst ) x

  let exec ?(pos = 0) (rex : regexp) (x : string) =
    try  Some (wrap (Pcre.exec ~pos ~rex) x)
    with Not_found -> None

  let split ?(pos = 0) (rex : regexp) (x : string) =
    let convert = function
      | Pcre.Text  s -> Some (Text  s)
      | Pcre.Delim s -> Some (Delim s)
      | _ -> None

    in List.pmap convert (wrap (Pcre.full_split ~pos ~rex) x)

  let sub (rex : regexp) (subst : subst) (x : string) =
    try  wrap (Pcre.replace ~rex ~itempl:subst) x
    with Failure _ -> raise (Error InvalidBackRef)

  let extract (rex : regexp) (x : string) =
    try  wrap (Pcre.extract_all_opt ~full_match:true ~rex) x
    with Not_found -> [||]

  module Match = struct
    let count (m : match_) : int =
      (wrap Pcre.num_of_subs) m

    let group (m : match_) (i : int) : string option =
      try  Some (wrap (Pcre.get_substring m) i)
      with
      | Invalid_argument _ -> raise (Error (InvalidSubString i))
      | Not_found -> None

    let groups (m : match_) : (string option) array =
      wrap (Pcre.get_opt_substrings ~full_match:true) m

    let offset (m : match_) (i : int) : (int * int) option =
      try  Some (wrap (Pcre.get_substring_ofs m) i)
      with
      | Invalid_argument _ -> raise (Error (InvalidSubString i))
      | Not_found -> None
  end
end

(* -------------------------------------------------------------------- *)
module Core : CORE = PcreCore

(* -------------------------------------------------------------------- *)
include Core

type oregexp = [`C of regexp | `S of string]
type osubst  = [`C of subst  | `S of string]

(* -------------------------------------------------------------------- *)
let oregexp (rex : oregexp) =
  match rex with
  | `C rex -> rex
  | `S rex -> Core.regexp rex

let osubst (subst : osubst) =
  match subst with
  | `C sst -> sst
  | `S sst -> Core.subst sst

(* -------------------------------------------------------------------- *)
let exec ?(pos : int option) (rex : oregexp) (x : string) =
  exec ?pos (oregexp rex) x

let match_ ?(pos : int option) (rex : oregexp) (x : string) =
  is_some (exec ?pos rex x)

let split ?(pos : int option) (rex : oregexp) (x : string) =
  split ?pos (oregexp rex) x

let split0 ?(pos : int option) (rex : oregexp) (x : string) =
  let convert = function Text s -> Some s | Delim _ -> None in
  List.pmap convert (split ?pos rex x)

let sub (rex : oregexp) (sst : osubst) (x : string) =
  sub (oregexp rex) (osubst sst) x

let extract (rex : oregexp) (x : string) =
  extract (oregexp rex) x
