open Tyxml.Html

open EcScope

let thkind_str (kind : EcLoader.kind) : string =
  match kind with
  | `Ec -> "Theory"
  | `EcA -> "Abstract Theory" 

let itemkind_str_pl (ik : itemkind) : string =
  match ik with
  | `Type -> "Types"
  | `Operator -> "Operator"
  | `Axiom -> "Axioms"
  | `ModuleType -> "Module Types"
  | `Module -> "Modules"
  | `Theory -> "Theories"

let c_title (fn: string) (kind : EcLoader.kind) : [> Html_types.title] elt =
  title (txt (thkind_str kind ^ " " ^ fn))

let c_metadata (metadata : string list) = ()

let c_head (metadata : string list option) (fn : string) (kind : EcLoader.kind) : [> Html_types.head] elt =
  head (c_title fn kind) []

let c_section_global (fn : string) (kind : EcLoader.kind) (gdoc : string list) =
    div [
      h1 [txt (thkind_str kind ^ " " ^ fn)]
    ] 
    ::
    match gdoc with
    | [] -> []
    | _ -> [div (List.map (fun s -> p [txt s]) gdoc)]
  
let c_section_local_itemkind (lents_ik : EcScope.docentity list) =
  [p [txt "test"]]

let c_section_local (lents : EcScope.docentity list) =
  let iks = [`Type; `Operator; `Axiom; `ModuleType; `Module; `Theory] in
  List.concat 
    (List.map (fun ik -> 
      let lents_ik = List.filter (fun ent -> 
        match ent with
        | ItemDoc (_, di) -> fst di = ik
        | SubDoc _ -> false) lents
      in
      match lents_ik with
      | [] -> []
      | _ ->  [
                div [h2 [txt (itemkind_str_pl ik)]];
                div (c_section_local_itemkind lents_ik)
              ]) 
    iks)

let c_body (fn : string) (kind : EcLoader.kind) (scope : EcScope.scope) : [> Html_types.body] elt =
  let gsec = c_section_global fn kind (get_gdocstrings scope) in
  let lsec = c_section_local (get_ldocentities scope) in
  body (List.concat [gsec; lsec])


let c_page (metadata : string list option) (fn : string) (kind : EcLoader.kind) (scope : EcScope.scope) : [> Html_types.html] elt =
    html (c_head metadata fn kind) (c_body fn kind scope)

(* input = input name, scope contains all documentation items *)
let generate_html (fname : string option) (scope : EcScope.scope) : unit =
  match fname with
  | Some fn ->
      let kind =
        try  EcLoader.getkind (Filename.extension fn)
        with EcLoader.BadExtension _ -> assert false 
      in

      let fnne = Filename.remove_extension fn in
      let hn = fnne ^ ".html" in
      
      let file = open_out hn in
      let fmt = Format.formatter_of_out_channel file in
        pp () fmt (c_page None fnne kind scope);
        close_out file;

  | None -> ()