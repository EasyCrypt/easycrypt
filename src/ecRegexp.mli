(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2016 - Inria
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
type error 
type regexp 
type subst
type match_

type split =
  | Text  of string
  | Delim of string

exception Error of error

type oregexp = [`C of regexp | `S of string]
type osubst  = [`C of subst  | `S of string]

(* -------------------------------------------------------------------- *)
val quote  : string -> string
val regexp : string -> regexp
val subst  : string -> subst

(* -------------------------------------------------------------------- *)
module Match : sig
  val count  : match_ -> int
  val group  : match_ -> int -> string option
  val groups : match_ -> (string option) array
  val offset : match_ -> int -> (int * int) option
end

(* -------------------------------------------------------------------- *)
val exec    : ?pos:int -> oregexp -> string -> match_ option
val match_  : ?pos:int -> oregexp -> string -> bool
val split   : ?pos:int -> oregexp -> string -> split list
val split0  : ?pos:int -> oregexp -> string -> string list
val sub     : oregexp -> osubst -> string -> string
val extract : oregexp -> string -> (string option array) array
