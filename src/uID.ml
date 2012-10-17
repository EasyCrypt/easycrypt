(** Handle counters to have unique identification of objects. *)

type id = int

let pp_id fmt i = Format.fprintf fmt "%d" i

let new_counter n = ref n

let fresh counter = incr counter; !counter

let get_counter n tbl x =
  try Hashtbl.find tbl x
  with Not_found ->
    let counter = new_counter n in
    Hashtbl.add tbl x counter;
    counter


(** Unique identifier for operators *)

type op = id

let int_of_op x = x

let op_tbl = Hashtbl.create 10

let op_counter name = get_counter (-1) op_tbl name

let fresh_op name = fresh (op_counter name)

(** Unique identifier for variables *)

type var = id

let var_counter = ref 1

let fresh_var _ = fresh var_counter

let neq_var = -1

let pp_var = pp_id

(** Unique identifier for logic (Fol) variables *)

type lvar = id

let fresh_lvar _ = fresh var_counter

let empty_lvar = 0

let pp_lvar = pp_id

(** Unique identifier for type variables *)

type tvar = id

let tvar_tbl = Hashtbl.create 10

let tvar_counter name = get_counter (-1) tvar_tbl name

let fresh_tvar name = fresh (tvar_counter name)

let pp_tvar = pp_id


