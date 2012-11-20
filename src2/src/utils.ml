(* -------------------------------------------------------------------- *)
let tryexn (ignoreexn : exn -> bool) (f : unit -> 'a) =
  try  Some (f ())
  with e -> if ignoreexn e then None else raise e

let try_nf (f : unit -> 'a) =
  tryexn (function Not_found -> true | _ -> false) f

(* -------------------------------------------------------------------- *)
module UID = struct
  type uid = unit ref
end

(* -------------------------------------------------------------------- *)
module List = struct
  include List

  let ohead (xs : 'a list) =
    match xs with [] -> None | x :: _ -> Some x

  let index (v : 'a) (xs : 'a list) : int option =
    let rec index (i : int) = function
      | [] -> None
      | x :: xs -> if x = v then Some i else index (i+1) xs
    in
      index 0 xs
end
