type t = {
  mutable load_path : string list;
  docs              : (string, Document.t) Hashtbl.t;
}

let make ~load_path =
  { load_path; docs = Hashtbl.create 16 }

let load_path t = t.load_path
let set_load_path t path = t.load_path <- path

let open_document t doc =
  assert (not (Hashtbl.mem t.docs doc.Document.uri));
  Hashtbl.replace t.docs doc.Document.uri doc

let update_document t doc =
  match Hashtbl.find_opt t.docs doc.Document.uri with
  | None -> None
  | Some old ->
    Hashtbl.replace t.docs doc.Document.uri doc;
    Some (Document.diff ~old ~new_:doc)

let close_document t ~uri =
  Hashtbl.remove t.docs uri

let get t ~uri = Hashtbl.find_opt t.docs uri

let documents t =
  Hashtbl.fold (fun _ d acc -> d :: acc) t.docs []

let uris t =
  Hashtbl.fold (fun u _ acc -> u :: acc) t.docs []
