(* -------------------------------------------------------------------- *)
module StringMap = Map.Make(struct
  type t = string
  let  compare = (Pervasives.compare : t -> t -> int)
end)

(* -------------------------------------------------------------------- *)
module type IContext = sig
  type symbol = string

  type 'a context

  exception DuplicatedNameInContext of string
  exception UnboundName of string

  val empty   : unit -> 'a context
  val bind    : symbol -> 'a -> 'a context -> 'a context
  val rebind  : symbol -> 'a -> 'a context -> 'a context
  val exists  : symbol -> 'a context -> bool
  val lookup  : symbol -> 'a context -> 'a option
  val iter    : (symbol -> 'a -> unit) -> 'a context -> unit
  val fold    : ('b -> symbol -> 'a -> 'b) -> 'b -> 'a context -> 'b
  val tolist  : 'a context -> (symbol * 'a) list
end

(* -------------------------------------------------------------------- *)
module Context : IContext = struct
  module SM = StringMap

  module V : sig
    type 'a t

    val empty  : unit -> 'a t
    val push   : 'a -> 'a t -> 'a t
    val iter   : ('a -> unit) -> 'a t -> unit
    val fold   : ('b -> 'a -> 'b) -> 'b -> 'a t -> 'b
    val tolist : 'a t -> 'a list
  end = struct
    type 'a data = {
      v_front : 'a list;
      v_back  : 'a list;
    }

    type 'a t = ('a data) ref

    let normalize =
      let normalize (v : 'a data) ={
        v_front = List.rev_append (List.rev v.v_front) v.v_back;
        v_back  = [];
      } in
        fun v ->
          if !v.v_back <> [] then v := normalize !v; !v

    let empty () =
      ref { v_front = []; v_back = []; }

    let push (x : 'a) (v : 'a t) =
      ref { v_front = !v.v_front; v_back = x :: !v.v_back }

    let iter (f : 'a -> unit) (v : 'a t) =
      List.iter f (normalize v).v_front

    let fold (f : 'b -> 'a -> 'b) (state : 'b) (v : 'a t) =
      List.fold_left f state (normalize v).v_front

    let tolist (v : 'a t) = (normalize v).v_front
  end

  type symbol = string

  type 'a context = {
    ct_map   : 'a SM.t;
    ct_order : (string * 'a) V.t;
  }

  exception DuplicatedNameInContext of string
  exception UnboundName of string

  let empty () = { ct_map = SM.empty; ct_order = V.empty (); }

  let bind (x : symbol) (v : 'a) (m : 'a context) =
    if SM.mem x m.ct_map then
      raise (DuplicatedNameInContext x);
    { ct_map   = SM.add x v m.ct_map;
      ct_order = V.push (x, v) m.ct_order; }

  let rebind (x : symbol) (v : 'a) (m : 'a context) =
    if not (SM.mem x m.ct_map) then
      raise (UnboundName x);
    { ct_map   = SM.add x v m.ct_map;
      ct_order = m.ct_order; }

  let exists (x : symbol) (m : 'a context) =
    SM.mem x m.ct_map

  let lookup (x : symbol) (m : 'a context) =
    try  Some (SM.find x m.ct_map)
    with Not_found -> None

  let iter (f : symbol -> 'a -> unit) (m : 'a context) =
    V.iter (fun (x, v) -> f x v) m.ct_order

  let fold (f : 'b -> symbol -> 'a -> 'b) (state : 'b) (m : 'a context) =
    V.fold (fun st (x, v) -> f st x v) state m.ct_order

  let tolist (m : 'a context) =
    V.tolist m.ct_order
end

(*
(* -------------------------------------------------------------------- *)
module type IScope = sig
  type symbol = string

  type +'a scope

  exception DuplicatedNameInScope of string
  exception NoScopeToClose

  val create  : symbol -> 'a -> 'a scope
  val add     : symbol -> 'a -> 'a scope -> 'a scope
  val tryfind : symbol -> 'a scope -> 'a option
  val focus   : 'a scope -> symbol * 'a
  val attop   : 'a scope -> bool
  val iter    : (symbol -> 'a -> unit) -> 'a scope -> unit
  val chain   : 'a scope -> (symbol * 'a) list
  val sopen   : symbol -> 'a -> 'a scope -> 'a scope
  val sclose  : 'a scope -> 'a scope
end

(* -------------------------------------------------------------------- *)
module Scope : IScope = struct
  type symbol = string

  type 'a scope = unit

  exception DuplicatedNameInScope of string
  exception NoScopeToClose

  (* ------------------------------------------------------------------ *)
    
end
*)
