(* -------------------------------------------------------------------- *)
let top = "<top>"

(* -------------------------------------------------------------------- *)
let nil  = EcPath.create (Printf.sprintf "%s.list.nil"  top)
let cons = EcPath.create (Printf.sprintf "%s.list.cons" top)
let list = EcPath.create (Printf.sprintf "%s.list.list" top)

(* -------------------------------------------------------------------- *)
let get = EcPath.create "get"             (* FIXME *)
let set = EcPath.create "set"
let map = EcPath.create "map"
