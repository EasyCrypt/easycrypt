open Tyxml.Html

open EcScope

let c_filename ?(ext : string option) (nms : string list) =
  match ext with
  | None -> String.concat ">" nms 
  | Some ext -> String.concat ">" nms ^ ext
  
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
            section ~a:[a_title "Introduction"] [
              div (List.map (fun s -> p [txt s]) gdoc)
            ]
          ]
  
let c_section_main_itemkind_li ?(supthf : string option) (th : string) (lent_ik : EcScope.docentity) =
  match lent_ik with
  | SubDoc ((doc, (_, ik, nm, _)), _) -> 
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
            | None -> c_filename ?ext:(Some ".html") [th; nm]
            | Some supf -> c_filename ?ext:(Some ".html") [supf; th; nm]
          in
          li ([
            div [a ~a:[a_href (Xml.uri_of_string hn)] [txt nm]]; 
            div [p [txt hdoc]]
          ] @ (if tdoc <> []
               then [details (summary [])
                             (List.map (fun d -> p [txt d]) tdoc)]
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
            li [
              div [txt nm]; 
              div [p [txt hdoc]]; 
              details (summary [])
                      (List.map (fun d -> p [txt d]) tdoc 
                       @ [div [txt "Source:"; pre [code [txt psrc]]]])
            ]

let c_section_main_itemkind ?(supthf : string option) (th : string) (lents_ik : EcScope.docentity list) =
  [
    ul (List.map (fun lent_ik -> c_section_main_itemkind_li ?supthf th lent_ik) lents_ik)
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
                section ~a:[a_title (itemkind_str_pl ik)] [
                  h2 [txt (itemkind_str_pl ik)];
                  div (c_section_main_itemkind ?supthf th lents_ik)
                ]
              ]
      ) 
    iks)

let c_body ?(supths : string option) ?(supthf : string option) (th : string) (tstr : string) (gdoc : string list) (ldocents : EcScope.docentity list) : [> Html_types.body] elt =
  let page_heading = h1 [txt tstr] ::  
    match supths with
    | None -> []
    | Some sup ->
          match supthf with
          | None -> assert false
          | Some supf ->  
              [
                h5 [
                  txt ("Subtheory of ");
                  a ~a:[a_href (Xml.uri_of_string (supf ^ ".html"))] [txt sup]
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