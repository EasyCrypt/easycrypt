open Tyxml.Html

open EcScope

let c_filename ?(ext : string option) (nms : string list) =
  match ext with
  | None -> String.concat "!" nms 
  | Some ext -> String.concat "!" nms ^ ext
  
let thkind_str (kind : EcLoader.kind) : string =
  match kind with
  | `Ec -> "Theory"
  | `EcA -> "Abstract Theory" 

let itemkind_str_pl (ik : itemkind) : string =
  match ik with
  | `Type -> "Types"
  | `Operator -> "Operators"
  | `Axiom -> "Axioms"
  | `Lemma -> "Lemmas"
  | `ModuleType -> "Module Types"
  | `Module -> "Modules"
  | `Theory -> "Theories"

let c_head (tstr : string) : [> Html_types.head] elt =
  head (title (txt tstr)) []

let c_section_intro (gdoc : string list) =
  match gdoc with
  | [] -> []
  | _ ->  [
            let ids = "Introduction" in
            section ~a:[a_id ids; a_title ids; a_class ["intro-section"]] [
              div ~a:[a_class ["intro-text-container"]] 
                  (List.map (fun s -> p ~a:[a_class ["intro-text-par"]] [txt s]) gdoc)
            ]
          ]
  
let c_section_main_itemkind_li ?(supthf : string option) (th : string) (lent_ik : EcScope.docentity) =
  match lent_ik with
  | SubDoc ((doc, (_, ik, subth, _)), _) -> 
    begin
      match ik with
      | `Theory -> 
          let (hdoc, tdoc) = 
            if doc = [] then "", []
            else if List.length doc = 1 then List.hd doc, []
            else List.hd doc, List.tl doc
          in
          let hn =
           match supthf with
           | None -> c_filename ?ext:(Some ".html") [th; subth]
           | Some supf -> c_filename ?ext:(Some ".html") [supf; th; subth]
          in
          li ~a:[a_id (itemkind_str_pl ik ^ subth); a_class ["item-entry"]] ([
            div ~a:[a_class ["item-name"]] [a ~a:[a_href (Xml.uri_of_string hn)] [txt subth]]; 
            div ~a:[a_class ["item-basic-desc"]] [txt hdoc]
          ] @ (if tdoc <> []
               then [details ~a:[a_class ["item-details"]] (summary [])
                             (List.map (fun d -> p ~a:[a_class ["item-details-par"]] [txt d]) tdoc)]
               else []))
      | _ -> assert false
    end
  | ItemDoc (doc, (_, ik, nm, src)) -> 
      let psrc = String.trim (String.concat "\n" src) in
        match ik with
        | `Theory -> assert false
        | _ ->
            let (hdoc, tdoc) = 
              if doc = [] then "", []
              else if List.length doc = 1 then List.hd doc, []
              else List.hd doc, List.tl doc
            in
            li ~a:[a_class ["item-entry"]] [
              div ~a:[a_class ["item-name"]] [txt nm]; 
              div ~a:[a_class ["item-basic-desc"]] [txt hdoc]; 
              details ~a:[a_class ["item-details"]] (summary [])
                      (List.map (fun d -> p ~a:[a_class ["item-details-par"]] [txt d]) tdoc 
                       @ [div ~a:[a_class ["source-container"]] 
                              [txt "Source:"; pre ~a:[a_class ["source"]] [txt psrc]]])
            ]

let c_section_main_itemkind ?(supthf : string option) (th : string) (lents_ik : EcScope.docentity list) =
  [
    ul ~a:[a_class ["item-list"]] 
      (List.map (fun lent_ik -> c_section_main_itemkind_li ?supthf th lent_ik) lents_ik)
  ]

let c_section_main ?(supthf : string option) (th : string) (lents : EcScope.docentity list) =
  let iks = [`Type; `Operator; `Axiom; `Lemma; `ModuleType; `Module; `Theory] in
  List.concat 
    (List.map (fun ik -> 
      let lents_ik = List.filter (fun ent -> 
        match ent with
        | ItemDoc (_, (md, ikp, _, _)) -> md = `Specific && ikp = ik
        | SubDoc ((_, (md, ikp, _, _)), _) -> ikp = ik) lents
      in
      match lents_ik with
      | [] -> []
      | _ ->  [
                let iks = itemkind_str_pl ik in
                section ~a:[a_id iks; a_title iks; a_class ["item-section"]] [
                  h2 ~a:[a_class ["section-heading"]] [txt iks];
                  div ~a:[a_class ["item-list-container"]] (c_section_main_itemkind ?supthf th lents_ik)
                ]
              ]
      ) 
    iks)

let c_body ?(supths : string option) ?(supthf : string option) (th : string) (tstr : string) (gdoc : string list) (ldocents : EcScope.docentity list) : [> Html_types.body] elt =
  let page_heading = h1 ~a:[a_class ["page-heading"]] [txt tstr] ::  
    match supths with
    | None -> []
    | Some sup ->
          match supthf with
          | None -> assert false
          | Some supf ->  
              [
                h2 ~a:[a_class ["page-subheading"]] [
                  txt ("Subtheory of ");
                  a ~a:[a_href (Xml.uri_of_string (supf ^ ".html" ^ "#" ^ itemkind_str_pl `Theory ^ th))] [txt sup]
                ]
              ]
  in
  let intro = c_section_intro gdoc in
  let main = c_section_main ?supthf th ldocents in
  body (page_heading @ intro @ main)

let c_page ?(supths : string option) ?(supthf : string option) (th : string) (tstr : string) (gdoc : string list) (ldocents : EcScope.docentity list) : [> Html_types.html] elt =
    html (c_head tstr) (c_body ?supths ?supthf th tstr gdoc ldocents)

let emit_page (dp : string) (fn : string) (page : [> Html_types.html ] elt) =
  let wp = Filename.concat dp fn ^ ".html" in
  (* let s = Format.asprintf "%a" (Tyxml.Html.pp ()) page in *)
  let file = open_out wp in
  let fmt = Format.formatter_of_out_channel file in
    pp () fmt page;
    Format.fprintf fmt "@.";
    close_out file

let emit_pages (dp : string) (th : string) (tstr : string) (gdoc : string list) (ldocents : EcScope.docentity list) =
  let rec c_subpages ?supths ?supthf th docents =
    match docents with 
    | [] -> []
    | de :: docents' ->
        match de with
        | ItemDoc _ -> c_subpages ?supths ?supthf th docents'
        | SubDoc ((sgdoc, (smd, sik, sth, _)), sldocents) ->
             let ststr = (if smd = `Abstract then "Abstract " else "") ^ "Theory " ^ sth in
             let stsupf = 
                match supthf with
                | None -> th
                | Some supf -> c_filename [supf; th]
             in
             let stf = c_filename [stsupf; sth] in
              (stf, c_page ?supths:(Some th) ?supthf:(Some stsupf) sth ststr sgdoc sldocents)
              :: c_subpages ?supths:(Some th) ?supthf:(Some stsupf) sth sldocents 
              @ c_subpages ?supths ?supthf th docents'
  in
  let spgs = c_subpages th ldocents in
  List.iter (fun fnpg -> emit_page dp (fst fnpg) (snd fnpg)) spgs;
  emit_page dp th (c_page th tstr gdoc ldocents)

(* input = input name, scope contains all documentation items *)
let generate_html (fname : string option) (scope : EcScope.scope) : unit =
  match fname with
  | Some fn ->
      let kind =
        try  EcLoader.getkind (Filename.extension fn)
        with EcLoader.BadExtension _ -> assert false 
      in
      let dp, fn = Filename.dirname fn, Filename.basename fn in
      let th = Filename.remove_extension fn in
      let tstr = thkind_str kind  ^ " " ^ th in
      begin
        try emit_pages dp th tstr (get_gdocstrings scope) (get_ldocentities scope) with
        | _ as ex -> Printf.eprintf "Exception: %s\n." (Printexc.to_string ex); raise ex
      end
  | None -> ()