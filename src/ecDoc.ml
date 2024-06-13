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
  | `Lemma -> "Lemmas"
  | `ModuleType -> "Module Types"
  | `Module -> "Modules"
  | `Theory -> "Theories"

let c_metadata (metadata : string list) = ()

let c_head ?(metadata : string list option) (tstr : string) : [> Html_types.head] elt =
  head (title (txt tstr)) []

let c_section_intro (gdoc : string list) =
  match gdoc with
  | [] -> []
  | _ ->  [
            section ~a:[a_title "Introduction"] [
              div (List.map (fun s -> p [txt s]) gdoc)
            ]
          ]
  
let c_section_main_itemkind_li (lent_ik : EcScope.docentity) =
  match lent_ik with
  | SubDoc _ -> assert false
  | ItemDoc (doc, ditem) -> 
      let (md, ik, nm, src) = ditem in
      let psrc = String.trim (String.concat "\n" src) in
        match ik with
        | `Theory -> li []
        | _ ->
            let (hdoc, tdoc) = List.hd doc, List.tl doc  in 
            li [
              div [txt nm]; 
              div [p [txt hdoc]]; 
              details (summary []) (* TODO: want nicer icon *)
                      (List.map (fun d -> p [txt d]) tdoc 
                       @ [div [txt "Source:"; pre [code [txt psrc]]]])
            ]

let c_section_main_itemkind (lents_ik : EcScope.docentity list) =
  [
    ul (List.map (fun lent_ik -> c_section_main_itemkind_li lent_ik) lents_ik)
  ]

let c_section_main (dp : string) (lents : EcScope.docentity list) =
  let iks = [`Type; `Operator; `Axiom; `Lemma; `ModuleType; `Module; `Theory] in
  List.concat 
    (List.map (fun ik -> 
      let lents_ik = List.filter (fun ent -> 
        match ent with
        | ItemDoc (_, (_, ikp, _, _)) -> ikp = ik
        | SubDoc _ -> false) lents
      in
      match lents_ik with
      | [] -> []
      | _ ->  [
                section ~a:[a_title (itemkind_str_pl ik)] [
                  h2 [txt (itemkind_str_pl ik)];
                  div (c_section_main_itemkind lents_ik)
                ]
              ]) 
    iks)

let c_body ?(supth : string option) (dn : string) (tstr : string) (gdoc : string list) (ldocents : EcScope.docentity list) : [> Html_types.body] elt =
  let page_heading = h1 [txt tstr] ::  
    match supth with
    | None -> []
    | Some sup -> [h5 [txt ("Subtheory of " ^ sup)]] (* TODO: Link to supertheory file *)
  in
  let intro = c_section_intro gdoc in
  let main = c_section_main dn ldocents in
  body (page_heading @ intro @ main)

let c_page ?(metadata : string list option) ?(supth : string option) (dp : string) (tstr : string) (gdoc : string list) (ldocents : EcScope.docentity list) : [> Html_types.html] elt =
    html (c_head ?metadata tstr) (c_body ?supth dp tstr gdoc ldocents)

let emit_page ?(metadata : string list option) ?(supth : string option) (dp : string) (fn : string) (tstr : string) (gdoc : string list) (ldocents : EcScope.docentity list) =
  let wp = Filename.concat dp fn ^ ".html" in      
  let file = open_out wp in
  let fmt = Format.formatter_of_out_channel file in
    pp () fmt (c_page ?metadata ?supth dp tstr gdoc ldocents);
    close_out file

(* input = input name, scope contains all documentation items *)
let generate_html (fname : string option) (scope : EcScope.scope) : unit =
  match fname with
  | Some fn ->
      let kind =
        try  EcLoader.getkind (Filename.extension fn)
        with EcLoader.BadExtension _ -> assert false 
      in
      let dp, fn = Filename.dirname fn, Filename.basename fn in
      let fnne = Filename.remove_extension fn in
      let tstr = thkind_str kind  ^ " " ^ fnne in
      emit_page dp fnne tstr (get_gdocstrings scope) (get_ldocentities scope)
  | None -> ()

(* let generate_html (fname : string option) (scope : EcScope.scope) : unit =
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
        pp () fmt (html (head (title (txt "")) []) (body []));
        close_out file;

  | None -> () *)