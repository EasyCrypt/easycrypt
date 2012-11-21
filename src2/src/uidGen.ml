(* -------------------------------------------------------------------- *)
open Symbols

(* -------------------------------------------------------------------- *)
let unique () = Oo.id (object end)

(* -------------------------------------------------------------------- *)
type uid = int

type uidmap = {
  (*---*) um_tbl : (symbol, uid) Hashtbl.t;
  mutable um_uid : int;
}

let create () =
  { um_tbl = Hashtbl.create 0;
    um_uid = 0; }

let lookup (um : uidmap) (x : symbol) =
  try  Some (Hashtbl.find um.um_tbl x)
  with Not_found -> None

let forsym (um : uidmap) (x : symbol) =
  match lookup um x with
    | Some uid -> uid
    | None ->
      let uid = um.um_uid in
        um.um_uid <- um.um_uid + 1;
        Hashtbl.add um.um_tbl x uid;
        uid
