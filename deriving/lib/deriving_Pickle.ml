(* Copyright Jeremy Yallop 2007.
   This file is free software, distributed under the MIT license.
   See the file COPYING for details.
*)

(*
  Idea: 
  1. every object receives a serializable id.
  2. an object is serialized using the ids of its subobjects
*)

open Deriving_Typeable
open Deriving_Eq
open Deriving_Dump

module Deriving_Pickle =
struct
exception UnknownTag of int * string
exception UnpicklingError of string

module Id :
sig
  type t deriving (Show, Dump, Eq)
  val initial : t
  val compare : t -> t -> int
  val next : t -> t  
end =
struct
  type t = int deriving (Show, Dump, Eq)
  let initial = 0
  let compare = compare
  let next = succ
end
module IdMap = Map.Make (Id)
type id = Id.t deriving (Show, Dump)

module Repr : sig
  (* Break abstraction for the sake of efficiency for now *)
  type t = Bytes of string | CApp of (int option * Id.t list) deriving (Dump, Show)
  val of_string : string -> t
  val to_string : t -> string
  val make : ?constructor:int -> id list -> t
  val unpack_ctor : t -> int option * id list
end =
struct
  type t = Bytes of string | CApp of (int option * Id.t list) deriving (Dump, Show)
  let of_string s = Bytes s
  let to_string = function
    | Bytes s -> s
    | _ -> invalid_arg "string_of_repr"
  let make ?constructor ids = 
    match constructor with
      | Some n -> CApp (Some n, ids)
      | None   -> CApp (None, ids)
  let unpack_ctor = function 
    | CApp arg -> arg
    | _ -> raise (UnpicklingError "Error unpickling constructor")
end
type repr = Repr.t

module Write : sig
  type s = {
    nextid : Id.t;
    obj2id : Id.t Deriving_dynmap.DynMap.t;
    id2rep : repr IdMap.t;
  }
  val initial_output_state : s
  include Deriving_monad.Monad_state_type with type state = s

  module Utils (T : Typeable) (E : Eq with type a = T.a) : sig
    val allocate : T.a -> (id -> unit m) -> id m
    val store_repr : id -> Repr.t -> unit m
  end
end =
struct
  type s = {
    nextid : Id.t; (* the next id to be allocated *)
    obj2id : Id.t Deriving_dynmap.DynMap.t; (* map from typerep to id cache for the corresponding type *)
    id2rep : repr IdMap.t;
  }
  let initial_output_state = {
    nextid = Id.initial;
    obj2id = Deriving_dynmap.DynMap.empty;
    id2rep = IdMap.empty;
  }
  include Deriving_monad.Monad_state (struct type state = s end)
  module Utils (T : Typeable) (E : Eq with type a = T.a) =
  struct
    module C = Deriving_dynmap.Comp(T)(E)
    let comparator = C.eq

    let allocate o f =
      let obj = T.make_dynamic o in
      get >>= fun ({nextid=nextid;obj2id=obj2id} as t) ->
        match Deriving_dynmap.DynMap.find obj obj2id with
          | Some id -> return id
          | None -> 
              let id, nextid = nextid, Id.next nextid in
                put {t with
                       obj2id=Deriving_dynmap.DynMap.add obj id comparator obj2id;
                       nextid=nextid} >>
                  f id >> return id
                  
    let store_repr id repr =
      get >>= fun state ->
        put {state with id2rep = IdMap.add id repr state.id2rep}
  end
end

module Read : sig
  type s = (repr * (dynamic option)) IdMap.t
  include Deriving_monad.Monad_state_type with type state = s
  val find_by_id : id -> (Repr.t * dynamic option) m
  module Utils (T : Typeable) : sig
    val sum    : (int * id list -> T.a m)  -> id -> T.a m
    val tuple  : (id list -> T.a m)        -> id -> T.a m
    val record : (T.a -> id list -> T.a m) -> int -> id -> T.a m
    val update_map : id -> (T.a -> unit m)
  end
end =
struct
  type s = (repr * (dynamic option)) IdMap.t
  include Deriving_monad.Monad_state (struct type state = s end)

  let find_by_id id =
    get >>= fun state ->
    return (IdMap.find id state)

  module Utils (T : Typeable) = struct
    let decode_repr_ctor c = match Repr.unpack_ctor c with
      | (Some c, ids) -> (c, ids)
      | _ -> invalid_arg "decode_repr_ctor"

    let decode_repr_noctor c = match Repr.unpack_ctor c with
      | (None, ids) -> ids
      | _ -> invalid_arg "decode_repr_ctor"

    let update_map id obj =
      let dynamic = T.make_dynamic obj in
      get >>= fun state -> 
        match IdMap.find id state with 
          | (repr, None) ->     
              put (IdMap.add id (repr, Some dynamic) state)
          | (_, Some _) -> 
              return ()
                (* Checking for id already present causes unpickling to fail 
                   when there is circularity involving immutable values (even 
                   if the recursion wholly depends on mutability).

                   For example, consider the code

                   type t = A | B of t ref deriving (Typeable, Eq, Pickle)
                   let s = ref A in
                   let r = B s in
                   s := r;
                   let pickled = Pickle_t.pickleS r in
                   Pickle_t.unpickleS r

                   which results in the value
                   B {contents = B {contents = B { ... }}}

                   During deserialization the following steps occur:
                   1. lookup "B {...}" in the dictionary (not there)
                   2. unpickle the contents of B:
                   3. lookup the contents in the dictionary (not there)
                   4. create a blank reference, insert it into the dictionary
                   5. unpickle the contents of the reference:
                   6. lookup ("B {...}") in the dictionary (not there)
                   7. unpickle the contents of B:
                   8. lookup the contents in the dictionary (there)
                   9. insert "B{...}" into the dictionary.
                   10. insert "B{...}" into the dictionary.
                *)


    let whizzy f id decode =
      find_by_id id >>= fun (repr, dynopt) ->
      match dynopt with 
        | None ->
            f (decode repr) >>= fun obj ->
            update_map id obj >>
            return obj
        | Some obj -> return (T.throwing_cast obj)

    let sum f id = whizzy f id decode_repr_ctor
    let tuple f id = whizzy f id decode_repr_noctor
    let record_tag = 0
    let record f size id =
      find_by_id id >>= fun (repr, obj) ->
        match obj with
          | None ->
              let this = Obj.magic  (Obj.new_block record_tag size) in
                update_map id this >>
                f this (decode_repr_noctor repr) >>
                return this
          | Some obj -> return (T.throwing_cast obj)


  end
end


module type Pickle =
sig
  type a
  module Typeable : Typeable with type a = a
  module Eq : Eq with type a = a
  val pickle : a -> id Write.m
  val unpickle : id -> a Read.m
  val to_buffer : Buffer.t -> a -> unit
  val to_string : a -> string
  val to_channel : out_channel -> a -> unit
  val from_stream : char Stream.t -> a
  val from_string : string -> a
  val from_channel : in_channel -> a
end

module Defaults
  (S : sig
     type a
     module Typeable : Typeable with type a = a
     module Eq : Eq with type a = a
     val pickle : a -> id Write.m
     val unpickle : id -> a Read.m
   end) : Pickle with type a = S.a =
struct
  include S

  type ids = (Id.t * Repr.t) list
      deriving (Dump, Show)

  type dumpable = id * ids
      deriving (Show, Dump)

  type ('a,'b) pair = 'a * 'b deriving (Dump)
  type capp = int option * Id.t list deriving (Dump)

  (* We don't serialize ids of each object at all: we just use the
     ordering in the output file to implicitly record the ids of
     objects.

     Also, we don't serialize the repr constructors.  All values with
     a particular constructor are grouped in a single list.

     This can (and should) all be written much more efficiently.
  *)
  type discriminated = 
      (Id.t * string) list
    * (Id.t * (int * Id.t list)) list
    * (Id.t * (Id.t list)) list
        deriving (Dump, Show)

  type discriminated_ordered = 
      string list
      * (int * Id.t list) list
      * (Id.t list) list
        deriving (Dump, Show)

  let reorder : Id.t * discriminated -> Id.t * discriminated_ordered =
    fun (root,(a,b,c)) ->
      let collect_ids items (map,counter) =
        List.fold_left 
          (fun (map,counter) (id,_) ->
             IdMap.add id counter map, Id.next counter) 
          (map,counter) items in

      let map, _ = 
        collect_ids c
          (collect_ids b
             (collect_ids a
                (IdMap.empty, Id.initial))) in
      let lookup id = IdMap.find id map in
        (lookup root,
         (List.map snd a,
          List.map (fun (_,(c,l)) -> c, List.map lookup l) b,
          List.map (fun (_,l) -> List.map lookup l) c))

  let unorder : Id.t * discriminated_ordered -> Id.t * discriminated
    = fun (root,(a,b,c)) ->
      let number_sequentially id items =
        List.fold_left
          (fun (id,items) item -> 
             (Id.next id, (id,item)::items))
          (id,[]) items in
      let id = Id.initial in
      let id, a = number_sequentially id a in
      let id, b = number_sequentially id b in
      let  _, c = number_sequentially id c in
        (root, (a,b,c))

  type ('a,'b) either = Left of 'a | Right of 'b
  let either_partition (f : 'a -> ('b, 'c) either) (l : 'a list)
      : 'b list * 'c list =
    let rec aux (lefts, rights) = function
      | [] -> (List.rev lefts, List.rev rights)
      | x::xs ->
          match f x with 
            | Left l  -> aux (l :: lefts, rights) xs
            | Right r -> aux (lefts, r :: rights) xs
    in aux ([], []) l

  type discriminated_dumpable = Id.t * discriminated deriving (Dump) 

  let discriminate : (Id.t * Repr.t) list -> discriminated
    = fun input ->
      let bytes, others = 
        either_partition
          (function
             | id, (Repr.Bytes s) -> Left (id,s)
             | id, (Repr.CApp c) -> Right (id,c))
          input in
      let ctors, no_ctors =
        either_partition
          (function
             | id, (Some c, ps) -> Left (id, (c,ps))
             | id, (None, ps) -> Right (id,ps))
          others in
        (bytes, ctors, no_ctors)

  let undiscriminate : discriminated -> (Id.t * Repr.t) list
    = fun (a,b,c) ->
      List.map (fun (id,s) -> (id,Repr.Bytes s)) a
      @ List.map (fun (id,(c,ps)) -> (id,Repr.CApp (Some c,ps))) b
      @ List.map (fun (id,(ps)) -> (id,Repr.CApp (None,ps))) c

  type do_pair = Id.t * discriminated_ordered 
      deriving (Show, Dump)

  let write_discriminated f
    = fun (root,map) ->
      let dmap = discriminate map in
      let rmap = reorder (root,dmap) in
        f rmap

  let read_discriminated (f : 'b -> 'a) : 'b -> Id.t * (Id.t * Repr.t) list
    = fun s -> 
      let rmap = f s in
      let (root,dmap) = unorder rmap in
        (root, undiscriminate dmap)

  open Write

  let decode_pickled_string (f : 'a -> Id.t * discriminated_ordered) : 'b -> Id.t * Read.s =
    fun s -> 
      let (id, state : dumpable) = 
        read_discriminated f s
      in
        id, (List.fold_right 
               (fun (id,repr) map -> IdMap.add id (repr,None) map)
               state
               IdMap.empty)

  let encode_pickled_string f =
    fun (id,state) ->
      let input_state =
        id, IdMap.fold (fun id repr output -> (id,repr)::output)
          state.id2rep [] in
        write_discriminated f input_state

  let doPickle f v : 'a = 
    let id, state = runState (S.pickle v) initial_output_state in
      encode_pickled_string f (id, state)

  let doUnpickle f input = 
    let id, initial_input_state = decode_pickled_string f input in  
    let value, _ = Read.runState (S.unpickle id) initial_input_state in
      value

  let from_channel = doUnpickle Dump.from_channel<do_pair>
  let from_string = doUnpickle Dump.from_string<do_pair>
  let from_stream = doUnpickle Dump.from_stream<do_pair>
  let to_channel channel = doPickle (Dump.to_channel<do_pair> channel)
  let to_buffer buffer = doPickle (Dump.to_buffer<do_pair> buffer)
  let to_string = doPickle Dump.to_string<do_pair>
end

module Pickle_from_dump
  (P : Dump)
  (E : Eq with type a = P.a)
  (T : Typeable with type a = P.a)
  : Pickle with type a = P.a
           and type a = E.a
           and type a = T.a = Defaults
  (struct
     type a = T.a
     module Typeable = T
     module Eq = E
     module Comp = Deriving_dynmap.Comp(T)(E)
     open Write
     module W = Utils(T)(E)
     let pickle obj = 
       W.allocate obj 
         (fun id -> W.store_repr id (Repr.of_string (P.to_string obj)))
     open Read
     module U = Utils(T)
     let unpickle id = 
       find_by_id id >>= fun (repr, dynopt) ->
         match dynopt with
           | None -> 
               let obj : a = P.from_string (Repr.to_string repr) in
                 U.update_map id obj >> 
                   return obj
           | Some obj -> return (T.throwing_cast obj)
   end)

module Pickle_unit : Pickle with type a = unit = Pickle_from_dump(Dump_unit)(Eq_unit)(Typeable_unit)
module Pickle_bool = Pickle_from_dump(Dump_bool)(Eq_bool)(Typeable_bool)
module Pickle_int = Pickle_from_dump(Dump_int)(Eq_int)(Typeable_int)
module Pickle_char = Pickle_from_dump(Dump_char)(Eq_char)(Typeable_char)
module Pickle_float = Pickle_from_dump(Dump_float)(Eq_float)(Typeable_float)
module Pickle_string = Pickle_from_dump(Dump_string)(Eq_string)(Typeable_string)
module Pickle_int32 = Pickle_from_dump(Dump_int32)(Eq_int32)(Typeable_int32)
module Pickle_int64 = Pickle_from_dump(Dump_int64)(Eq_int64)(Typeable_int64)
module Pickle_nativeint = Pickle_from_dump(Dump_nativeint)(Eq_nativeint)(Typeable_nativeint)

module Pickle_option (V0 : Pickle) : Pickle with type a = V0.a option = Defaults(
  struct
    module Typeable = Typeable_option (V0.Typeable)
    module Eq = Eq_option (V0.Eq)
    module Comp = Deriving_dynmap.Comp (Typeable) (Eq)
    open Write
    type a = V0.a option
    let rec pickle =
      let module W = Utils(Typeable)(Eq) in
      function
          None as obj ->
            W.allocate obj
              (fun id -> W.store_repr id (Repr.make ~constructor:0 []))
        | Some v0 as obj ->
            W.allocate obj
              (fun thisid ->
                 V0.pickle v0 >>= fun id0 ->
                   W.store_repr thisid (Repr.make ~constructor:1 [id0]))
    open Read
    let unpickle = 
      let module W = Utils(Typeable) in
      let f = function
        | 0, [] -> return None
        | 1, [id] -> V0.unpickle id >>= fun obj -> return (Some obj)
        | n, _ -> raise (UnpicklingError
                           ("Unexpected tag encountered unpickling "
                            ^"option : " ^ string_of_int n)) in
        W.sum f
  end)


module Pickle_list (V0 : Pickle)
  : Pickle with type a = V0.a list = Defaults (
struct
  module Typeable = Typeable_list (V0.Typeable)
  module Eq = Eq_list (V0.Eq)
  module Comp = Deriving_dynmap.Comp (Typeable) (Eq)
  type a = V0.a list
  open Write
  module U = Utils(Typeable)(Eq)
  let rec pickle = function
      [] as obj ->
        U.allocate obj
          (fun this -> U.store_repr this (Repr.make ~constructor:0 []))
    | (v0::v1) as obj ->
        U.allocate obj
          (fun this -> V0.pickle v0 >>= fun id0 ->
                          pickle v1 >>= fun id1 ->
                            U.store_repr this (Repr.make ~constructor:1 [id0; id1]))
  open Read
  module W = Utils (Typeable)
  let rec unpickle id = 
    let f = function
      | 0, [] -> return []
      | 1, [car;cdr] -> 
          V0.unpickle car >>= fun car ->
             unpickle cdr >>= fun cdr ->
               return (car :: cdr)
      | n, _ -> raise (UnpicklingError
                         ("Unexpected tag encountered unpickling "
                          ^"option : " ^ string_of_int n)) in
      W.sum f id
end)
end
include Deriving_Pickle  

type 'a ref = 'a Pervasives.ref = { mutable contents : 'a }
    deriving (Eq,Typeable,Pickle)

(* Idea: keep pointers to values that we've serialized in a global
   weak hash table so that we can share structure with them if we
   deserialize any equal values in the same process *)

(* Idea: serialize small objects (bools, chars) in place rather than
   using the extra level of indirection (and space) introduced by ids
*)

(* Idea: bitwise output instead of bytewise.  Probably a bit much to
   implement now, but should have a significant impact (e.g. one using
   bit instead of one byte for two-constructor sums) *)

(* Should we use a different representation for lists?  i.e. write out
   the length followed by the elements?  we could no longer claim
   sharing maximization, but it would actually be more efficient in
   most cases.
*)
