(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcUtils
open EcMaps

(* -------------------------------------------------------------------- *)
type anchor =
  | Start
  | End

type 'base gen_regexp =
  | Anchor    of anchor
  | Any
  | Base      of 'base
  | Choice    of 'base gen_regexp list
  | Named     of 'base gen_regexp * string
  | Repeat    of 'base gen_regexp * int option pair * [ `Greedy | `Lazy ]
  | Seq       of 'base gen_regexp list

(* -------------------------------------------------------------------- *)
exception NoMatch
exception InvalidRange

(* -------------------------------------------------------------------- *)
module type IRegexpBase = sig
  type subject
  type engine
  type regexp1
  type path
  type pos = int

  type regexp = regexp1 gen_regexp

  val mkengine : subject -> engine
  val at_start : engine -> bool
  val at_end   : engine -> bool
  val eat      : engine -> engine
  val eat_base : engine -> regexp1 -> engine * (engine * regexp) list
  val position : engine -> pos
  val extract  : engine -> (pos * pos) -> subject
  val next     : engine -> engine option
  val path     : engine -> path
end

(* -------------------------------------------------------------------- *)
module Regexp(B : IRegexpBase) : sig
  type regexp  = B.regexp
  type subject = B.subject
  type matches = subject Mstr.t

  val search : regexp -> subject -> matches option
end = struct
  type regexp = B.regexp

  (* ------------------------------------------------------------------ *)
  type subject = B.subject
  type matches = subject Mstr.t
  type engine  = { e_sub : B.engine; e_grp : matches; }
  type pos     = B.pos

  (* ------------------------------------------------------------------ *)
  let mkengine (s : subject) =
    { e_sub = B.mkengine s; e_grp = Mstr.empty; }

  (* ------------------------------------------------------------------ *)
  let eat (e : engine) =
    { e with e_sub = B.eat e.e_sub }

  (* ------------------------------------------------------------------ *)
  type continuation  = Cont of (continuation1 * continuation) Lazy.t
   and matchr        = engine * continuation
   and continuation1 = [
     | `Result of engine
     | `Regexp of engine * regexp
   ]

  (* ------------------------------------------------------------------ *)
  let no_continuation =
    Cont (Lazy.from_fun (fun () -> raise NoMatch))

  (* ------------------------------------------------------------------ *)
  let single_continuation (ctn : continuation1) =
    Cont (Lazy.from_val (ctn, no_continuation))

  (* ------------------------------------------------------------------ *)
  let single_mr (e : engine) : matchr =
    (e, no_continuation)

  (* -------------------------------------------------------------------- *)
  let add_match (e : engine) (name : string) (range : pos * pos) =
    { e with e_grp = Mstr.add name (B.extract e.e_sub range) e.e_grp }

  (* ------------------------------------------------------------------ *)
  let rec search (e : engine) (r : regexp) : matchr =
    match r with
    | Anchor Start when B.at_start e.e_sub -> (e, no_continuation)
    | Anchor End   when B.at_end e.e_sub   -> (e, no_continuation)

    | Anchor _ ->
        raise NoMatch

    | Any ->
        (eat e, no_continuation)

    | Base br ->
        let sub, aux = B.eat_base e.e_sub br in
        let grp = List.fold_left search_sub e.e_grp aux in
        ({ e_sub = sub; e_grp = grp; }, no_continuation)

    | Named (subr, name) ->
        let decorate res =
          let start = B.position e.e_sub in
          let end_  = B.position res.e_sub in
          add_match res name (start, end_)
        in apply1_on_mr decorate (search e subr)

    | Choice rs ->
        let ctn =
          let do1 r ctn =
            let ctn1 = `Regexp (e, r) in
            Cont (Lazy.from_val (ctn1, ctn))
          in List.fold_right do1 rs no_continuation
        in force_continuation ctn

    | Seq [] ->
        (e, no_continuation)

    | Seq (r :: rs) ->
        apply_on_mr (fun e -> search e (Seq rs)) (search e r)

    | Repeat (subr, (imin, imax), mode) -> begin
        let imin = odfl 0 imin in
        let imax = odfl max_int imax in

        if imax < imin then raise NoMatch else

        let mr =
          let rec aux (count : int) (e : engine) =
            if   count <= 0
            then (e, no_continuation)
            else apply_on_mr (aux (count - 1)) (search e subr)
          in aux imin e in

        if imax <= imin then mr else

        let module E = struct exception Error end in

        let rec next1 (count : int) (e : engine) =
          if   count <= 0
          then raise NoMatch
          else
            apply_on_mr
              (next (Some (B.path e.e_sub)) (count - 1))
              (search e subr)

        and next start count (e : engine) =
          if Some (B.path e.e_sub) = start then raise NoMatch;
          try
            try
              match mode with
              | `Lazy ->
                (e, continuation_of_mr (next1 count e))
              | `Greedy ->
                  chain_mr
                    (next1 count e)
                    (continuation_of_mr (e, no_continuation))
            with NoMatch -> raise E.Error
          with E.Error -> (e, no_continuation)

        in apply_on_mr (next None (imax - imin)) mr
      end

  (* ------------------------------------------------------------------ *)
  and continuation_of_mr (e, ctn) : continuation =
    Cont (Lazy.from_val (`Result e, ctn))

  (* ------------------------------------------------------------------ *)
  and chain_continuation (Cont ctn1) (Cont ctn2) =
    Cont (Lazy.from_fun (fun () ->
      try
        let (x, ctn1) = Lazy.force ctn1 in
        (x, chain_continuation ctn1 (Cont ctn2))
      with NoMatch -> Lazy.force ctn2))

  (* ------------------------------------------------------------------ *)
  and force_continuation (Cont (lazy (ctn1, ctn))) : matchr =
    match ctn1 with
    | `Result e -> (e, ctn)
    | `Regexp (e, r) ->
        try
          let (e, ectn) = search e r in
          (e, chain_continuation ectn ctn)
        with NoMatch -> force_continuation ctn

  (* ------------------------------------------------------------------ *)
  and apply_on_continuation f ctn =
    Cont (Lazy.from_fun (fun () ->
      let e, ctn = apply_on_mr f (force_continuation ctn) in
      (`Result e, ctn)))

  (* ------------------------------------------------------------------ *)
  and apply_on_mr (f : engine -> matchr) ((e, ctn) : matchr) : matchr =
    try  chain_mr (f e) (apply_on_continuation f ctn)
    with NoMatch -> apply_on_mr f (force_continuation ctn)

  (* ------------------------------------------------------------------ *)
  and chain_mr ((e, ctn1) : matchr) (ctn2 : continuation) =
    (e, chain_continuation ctn1 ctn2)

  (* ------------------------------------------------------------------ *)
  and apply1_on_continuation f (ctn : continuation) : continuation =
    apply_on_continuation (fun e -> (f e, no_continuation)) ctn

  (* ------------------------------------------------------------------ *)
  and apply1_on_mr f (mr : matchr) : matchr =
    apply_on_mr (fun e -> (f e, no_continuation)) mr

  (* ------------------------------------------------------------------ *)
  and next_continuation (e : engine) : continuation =
    let next () : continuation1 * continuation =
      let e = { e with e_sub = oget ~exn:NoMatch (B.next e.e_sub) } in
      (`Result e, next_continuation e)
    in Cont (Lazy.from_fun next)

  (* ------------------------------------------------------------------ *)
  and next_mr (e : engine) : matchr =
    (e, next_continuation e)

  (* ------------------------------------------------------------------ *)
  and search_sub (grp : matches) ((e, r) : B.engine * regexp) =
    let mr = next_mr { e_sub = e; e_grp = grp; } in
    (fst (apply_on_mr (fun e -> search e r) mr)).e_grp

  (* ------------------------------------------------------------------ *)
  let search (re : regexp) (subject : subject) =
    let mr = next_mr (mkengine subject) in
    try  Some (fst (apply_on_mr (fun e -> search e re) mr)).e_grp
    with NoMatch -> None
end

(* -------------------------------------------------------------------- *)
type string_regexp = String of string

module StringBaseRegexp
  : IRegexpBase with type subject = string
                 and type regexp1 = string_regexp
= struct
  type subject = string
  type regexp1 = string_regexp
  type engine  = { e_sbj : string; e_pos : int; }
  type pos     = int
  type path    = int

  type regexp = regexp1 gen_regexp

  (* ------------------------------------------------------------------ *)
  let mkengine (s : string) =
    { e_sbj = s; e_pos = 0; }

  (* ------------------------------------------------------------------ *)
  let at_start (e : engine) = e.e_pos = 0
  let at_end   (e : engine) = e.e_pos = String.length e.e_sbj

  (* ------------------------------------------------------------------ *)
  let path (e : engine) : path =
    e.e_pos

  (* ------------------------------------------------------------------ *)
  let position (e : engine) = e.e_pos

  (* ------------------------------------------------------------------ *)
  let eat (e : engine) (n : int) =
    if   String.length e.e_sbj - e.e_pos < n
    then raise NoMatch
    else { e with e_pos = e.e_pos + 1 }

  (* ------------------------------------------------------------------ *)
  let eat e = eat e 1

  (* ------------------------------------------------------------------ *)
  let eat_base (e : engine) (String s : regexp1) =
    let len = String.length s in

    if String.length e.e_sbj - e.e_pos < len then
      raise NoMatch;

    s |> String.iteri (fun i c ->
      if c <> e.e_sbj.[e.e_pos + i] then raise NoMatch);
    { e with e_pos = e.e_pos + len }, []

  (* ------------------------------------------------------------------ *)
  let extract (e : engine) ((r1, r2) : int * int) =
    try  String.sub e.e_sbj r1 (r2 - r1)
    with Invalid_argument _ -> raise InvalidRange

  (* ------------------------------------------------------------------ *)
  let next (e : engine) =
    if at_end e then None else Some { e with e_pos = e.e_pos + 1 }
end

(* -------------------------------------------------------------------- *)
module StringRegexp = Regexp(StringBaseRegexp)
