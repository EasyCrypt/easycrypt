(* -------------------------------------------------------------------- *)
open Tyxml.Html

open EcScope

(* -------------------------------------------------------------------- *)
module DocModel = struct
  type page_id = string list

  type section_id = {
    sid_page : page_id;
    sid_name : string;
  }

  type item_id = {
    iid_page : page_id;
    iid_kind : itemkind;
    iid_name : string;
    }

  type item_target =
    | PageTarget of page_id

  type t = {
    model_pages : docpage list;
  }

  and docpage = {
    page_id : page_id;
    page_parent : page_id option;
    page_title : string;
    page_intro : docblock list;
    page_sections : docsection list;
    page_subpages : docpage list;
  }

  and docsection = {
    section_id : section_id;
    section_title : string;
    section_items : docitem list;
  }

  and docitem = {
    item_id : item_id;
    item_mode : mode;
    item_kind : itemkind;
    item_name : string;
    item_docs : docblock list;
    item_source : string list;
    item_target : item_target option;
  }

  and docblock =
    | RawDoc of string

  let empty : t = {
    model_pages = [];
  }

  let rawdoc_of_string (s : string) : docblock =
    RawDoc s

  let rawdocs_of_strings (ss : string list) : docblock list =
    List.map rawdoc_of_string ss

  let filename_of_pageid ?ext (id : page_id) : string =
    let base = String.concat "!" id in
    match ext with
    | None -> base
    | Some ext -> base ^ ext

  let pageid_of_name ?pid (name : string) : page_id =
    match pid with
    | None -> [name]
    | Some pid -> pid @ [name]

  let pagetitle_of_mode_and_name (mode : mode) (name : string) : string =
    match mode with
    | `Abstract -> "Abstract Theory " ^ name
    | `Specific -> "Theory " ^ name

  let namesl_of_itemkind (ik : itemkind) : string =
    match ik with
    | `Type -> "Type"
    | `Operator -> "Operator"
    | `Axiom -> "Axiom"
    | `Lemma -> "Lemma"
    | `ModuleType -> "Module Type"
    | `Module -> "Module"
    | `Theory -> "Theory"

  let namepl_of_itemkind (ik : itemkind) : string =
    match ik with
    | `Type -> "Types"
    | `Operator -> "Operators"
    | `Axiom -> "Axioms"
    | `Lemma -> "Lemmas"
    | `ModuleType -> "Module Types"
    | `Module -> "Modules"
    | `Theory -> "Theories"

  let sectionkey_of_itemkind (ik : itemkind) : string =
    match ik with
    | `Type -> "types"
    | `Operator -> "operators"
    | `Axiom -> "axioms"
    | `Lemma -> "lemmas"
    | `ModuleType -> "module-types"
    | `Module -> "modules"
    | `Theory -> "theories"

  (* let path_of_qsymbol (env : EcEnv.env) (ik : itemkind) (qsym : EcSymbols.qsymbol) : EcPath.path = *)
  (*   match ik with *)
  (*   | `Type -> EcEnv.Ty.lookup_path qsym env *)
  (*   | `Operator -> EcEnv.Op.lookup_path qsym env *)
  (*   | `Axiom -> EcEnv.Ax.lookup_path qsym env *)
  (*   | `Lemma -> EcEnv.Ax.lookup_path qsym env *)
  (*   | `ModuleType -> EcEnv.ModTy.lookup_path qsym env *)
  (*   | `Module -> *)
  (*      begin *)
  (*        match (EcEnv.Mod.lookup_path qsym env).m_top with *)
  (*        | `Concrete (p, None) -> p *)
  (*        | `Concrete (_, Some _) -> failwith "Linking to sub-modules not supported." *)
  (*        | `Local _ -> failwith "Linking to local/declared modules not supported." *)
  (*      end *)
  (*   | `Theory -> EcEnv.Theory.lookup_path ~mode:`All qsym env *)

 let docitem_of_itemdoc
      ~(pid : page_id)
      (docstr, (mode, kind, name, src))
    : docitem =
    {
      item_id = {
        iid_page = pid;
        iid_kind = kind;
        iid_name = name;
      };
      item_mode = mode;
      item_kind = kind;
      item_name = name;
      item_docs = rawdocs_of_strings docstr;
      item_source = src;
      item_target = None;
    }

  let docitem_of_subdoc
      ~(pid : page_id)
      (docstr, (mode, kind, name, src))
    : docitem =
    let child_pid = pageid_of_name ~pid name in
    {
      item_id = {
        iid_page = pid;
        iid_kind = kind;
        iid_name = name;
      };
      item_mode = mode;
      item_kind = kind;
      item_name = name;
      item_docs = rawdocs_of_strings docstr;
      item_source = src;
      item_target = Some (PageTarget child_pid);
    }

  let docitem_of_docent ~(pid : page_id) (docent : docentity) : docitem =
    match docent with
    | ItemDoc (docstr, item) ->
        docitem_of_itemdoc ~pid (docstr, item)

    | SubDoc ((docstr, item), _) ->
        docitem_of_subdoc ~pid (docstr, item)

  let docitems_of_docents
      ~(pid : page_id)
      (docents : docentity list)
    : docitem list =
    List.map (docitem_of_docent ~pid) docents

  let docsection_of_docitems
        ~(pid : page_id)
        ~(skey : string)
        ~(title : string)
        (docitems : docitem list)
      : docsection =
    {
      section_id = { sid_page = pid; sid_name = skey; };
      section_title = title;
      section_items = docitems;
    }

  let docsection_of_docitems_by_kind
        ~(pid : page_id)
        ~(kind : itemkind)
        (docitems : docitem list)
      : docsection =
    let title = namepl_of_itemkind kind in
    let skey = sectionkey_of_itemkind kind in
    let items = (List.filter (fun it -> it.item_kind = kind) docitems) in
    docsection_of_docitems ~pid:pid ~skey:skey ~title:title items

  let docsections_of_docitems_by_kind
        ~(pid : page_id)
        (docitems : docitem list)
      : docsection list =
    List.map (fun ik -> docsection_of_docitems_by_kind ~pid:pid ~kind:ik docitems) all_itemkinds
  (* |> List.filter (fun ds ->  ~pid:pid ~kind:ik docitems) *)

  let rec docpage_of_subdoc ?(pid : page_id option) (subdoc : docentity) : docpage =
    match subdoc with
    | ItemDoc _ -> assert false
    | SubDoc ((docstr, (mode, _kind, name, _src)), docents) ->
       let pageid = pageid_of_name ?pid name in
       let docitems = docitems_of_docents ~pid:pageid docents in
       let subpages =
         List.filter_map
           (function
            | ItemDoc _ -> None
            | SubDoc _ as subdoc ->
               Some (docpage_of_subdoc ~pid:pageid subdoc))
           docents
       in
       {
         page_id = pageid;
         page_parent = pid;
         page_title = pagetitle_of_mode_and_name mode name;
         page_intro = rawdocs_of_strings docstr;
         page_sections =
           docsections_of_docitems_by_kind ~pid:pageid docitems;
         page_subpages = subpages;
       }

  let root_page_of_scope ~(thname : string) ~(thmode : mode) (scope : EcScope.scope) : docpage =
    let pageid = [thname] in
    let docents = get_ldocentities scope in
    let docitems = docitems_of_docents ~pid:pageid docents in
    let subpages =
      List.filter_map
        (function
          | ItemDoc _ -> None
          | SubDoc _ as subdoc ->
              Some (docpage_of_subdoc ~pid:pageid subdoc))
        docents
    in
    {
      page_id = pageid;
      page_parent = None;
      page_title = pagetitle_of_mode_and_name thmode thname;
      page_intro = rawdocs_of_strings (get_gdocstrings scope);
      page_sections =
        docsections_of_docitems_by_kind ~pid:pageid docitems;
      page_subpages = subpages;
    }
end


(* -------------------------------------------------------------------- *)
let styles_file : string =
  let (module Sites) = EcRelocate.sites in
  Filename.concat Sites.doc "styles.css"

let stdlib_doc_dp (th : string) : string =
  match th with
  | _ -> ""

(* -------------------------------------------------------------------- *)
let from_stdlib (th : string) : bool =
  match th with
  | _ -> false

(* -------------------------------------------------------------------- *)
let c_filename ?(ext : string option) (nms : string list) =
  match ext with
  | None -> String.concat "!" nms
  | Some ext -> String.concat "!" nms ^ ext

(* -------------------------------------------------------------------- *)
let thkind_str (kind : EcLoader.kind) : string =
  match kind with
  | `Ec -> "Theory"
  | `EcA -> "Abstract Theory"

(* -------------------------------------------------------------------- *)
let itemkind_str_pl (ik : itemkind) : string =
  match ik with
  | `Type -> "Types"
  | `Operator -> "Operators"
  | `Axiom -> "Axioms"
  | `Lemma -> "Lemmas"
  | `ModuleType -> "Module Types"
  | `Module -> "Modules"
  | `Theory -> "Theories"

let itemkind_lookup_path (ik : itemkind) (q : EcSymbols.qsymbol) (env : EcEnv.env) =
  match ik with
  | `Type -> EcEnv.Ty.lookup_path q env
  | `Operator -> EcEnv.Op.lookup_path q env
  | `Axiom -> EcEnv.Ax.lookup_path q env
  | `Lemma -> EcEnv.Ax.lookup_path q env
  | `ModuleType -> EcEnv.ModTy.lookup_path q env
  | `Module ->
     begin
       match (EcEnv.Mod.lookup_path q env).m_top with
       | `Concrete (p, None) -> p
       | `Concrete (_, Some _) -> failwith "Linking to sub-modules not supported."
       | `Local _ -> failwith "Linking to local/declared modules not supported."
     end
  | `Theory -> EcEnv.Theory.lookup_path ~mode:`All q env

(* -------------------------------------------------------------------- *)
let rec bot_env_of_qsymbol (q : EcSymbols.qsymbol) (env : EcEnv.env)=
  match fst q with
  | [] | ["Top"] -> env
  | x :: xs ->
    let p = EcEnv.Theory.lookup_path ~mode:`All ([], x) env in
    let env = EcEnv.Theory.env_of_theory p env in
      bot_env_of_qsymbol (xs, snd q) env

let filename_of_path ?(ext : string option) (rth : string) (p : EcPath.path) =
  let qs = EcPath.toqsymbol p in
  match fst qs with
  | [] -> assert false
  | ["Top"] -> c_filename ?ext [rth]
  | "Top" :: ts ->
      let reqrt = (List.hd ts) in
      if from_stdlib reqrt then
        Filename.concat (stdlib_doc_dp reqrt) (c_filename ?ext ts)
      else
        (c_filename ?ext (rth :: ts))
  | _ -> assert false

(* -------------------------------------------------------------------- *)
let md_pre_format ~kind (s : string) =
  match kind with | _ -> pre [txt s]

let md_href_format (rth : string) (env : EcEnv.env) (hr : Markdown.href) : Html_types.phrasing elt =
  let il_format = Str.regexp "^>\\([^|]*\\)|\\([^|]+\\)$" in
  if Str.string_match il_format hr.href_target 0 then
    let tkind = Str.matched_group 1 hr.href_target in
    let tname = Str.matched_group 2 hr.href_target in
    let tqs = EcSymbols.qsymbol_of_string tname in
    let env = bot_env_of_qsymbol tqs env in
    let ikstr, path =
      match tkind with
      | "Ty" | "Type" -> itemkind_str_pl `Type, itemkind_lookup_path `Type tqs env
      | "Op" | "Operator" -> itemkind_str_pl `Operator, itemkind_lookup_path `Operator tqs env
      | "Ax" | "Axiom" -> itemkind_str_pl `Axiom, itemkind_lookup_path `Axiom tqs env
      | "Lem" | "Lemma" -> itemkind_str_pl `Lemma, itemkind_lookup_path `Lemma tqs env
      | "ModTy" | "ModuleType" -> itemkind_str_pl `ModuleType, itemkind_lookup_path `ModuleType tqs env
      | "Mod" | "Module" -> itemkind_str_pl `Module, itemkind_lookup_path `Module tqs env
      | "Th" | "Theory" -> itemkind_str_pl `Theory, itemkind_lookup_path `Theory tqs env
      | "" ->
         let rec try_lookup = function
           | [] -> failwith (Printf.sprintf "No item/entity found with name `%s'." tname)
           | ik :: iks ->
              try itemkind_str_pl ik, itemkind_lookup_path ik tqs env
              with EcEnv.LookupFailure _ -> try_lookup iks
         in
         let iks = [`Type; `Operator; `Axiom; `Lemma; `ModuleType; `Module; `Theory] in
         try_lookup iks
      | _ -> failwith (Printf.sprintf "Invalid item/entity kind `%s'." tkind)
    in
    let fn = filename_of_path ~ext:".html" rth path in
    let il = fn ^ "#" ^ ikstr ^ snd tqs in
    a ~a:[a_href (uri_of_string il)] [txt hr.href_desc]
  else
    a ~a:[a_href (uri_of_string hr.href_target)] [txt hr.href_desc]

let md_img_format (_ : Markdown.img_ref) =
  failwith "Image embedding not supported."

let c_markdown (input : string) (rth : string) (env : EcEnv.env) =
  let input = Markdown.parse_text input in

  MarkdownHTML.to_html
    ~render_pre:md_pre_format
    ~render_link:(md_href_format rth env)
    ~render_img:md_img_format
    input


(* -------------------------------------------------------------------- *)
let c_head (tstr : string) : [> Html_types.head] elt =
  head (title (txt tstr)) [link ~rel:[`Stylesheet] ~href:styles_file ()]

(* -------------------------------------------------------------------- *)
let c_sidebar (th : string) (lents : EcScope.docentity list) =
  let iks = [`Type; `Operator; `Axiom; `Lemma; `ModuleType; `Module; `Theory] in
  let iksin =
    List.filter (fun ik ->
      List.exists (fun ldoc ->
        match ldoc with
        | ItemDoc (_, (_, ikp, _, _)) -> ikp = ik
        | SubDoc ((_, (_, ikp, _, _)), _) -> ikp = ik) lents) iks
  in
    nav ~a:[a_class ["sidebar"]]
        [
          div ~a:[a_class["sidebar-title"]]
          [
            h2 [txt "EasyCrypt Documentation"];
            span ~a:[a_class ["sidebar-title-theory"]] [txt th]
          ];
          div ~a:[a_class ["sidebar-elems"]]
          [
            ul ~a:[a_class ["sidebar-section-list"]]
                (List.map (fun ik ->
                  let ikstr = itemkind_str_pl ik in
                  li [a ~a:[a_href (Xml.uri_of_string ("#" ^ ikstr))] [txt ikstr]]) iksin)
          ]
        ]

(* -------------------------------------------------------------------- *)
let c_section_intro (rth : string) (gdoc : string list) (env : EcEnv.env) =
  match gdoc with
  | [] -> []
  | _ ->  [
            let ids = "Introduction" in
            section ~a:[a_id ids; a_title ids; a_class ["intro-section"]] [
              div ~a:[a_class ["intro-text-container"]]
                  (List.map (fun s -> div ~a:[a_class ["intro-par-container"]] (c_markdown s rth env)) gdoc)
            ]
          ]

(* -------------------------------------------------------------------- *)
let c_section_main_itemkind_li ?(supthf : string option) (rth : string) (th : string) (lent_ik : EcScope.docentity) (env : EcEnv.env) =
  match lent_ik with
  | SubDoc ((doc, (_, ik, subth, _)), _) ->
    begin
      match ik with
      | `Theory ->
          let (hdoc, tdoc) =
            if doc = [] then "No description available.", []
            else if List.length doc = 1 then List.hd doc, []
            else List.hd doc, List.tl doc
          in
          let hn =
           match supthf with
           | None -> c_filename ~ext:(".html") [th; subth]
           | Some supf -> c_filename ~ext:(".html") [supf; th; subth]
          in
          li ~a:[a_id (itemkind_str_pl ik ^ subth); a_class ["item-entry"]] ([
            div ~a:[a_class ["item-name-desc-container"]] [
              div ~a:[a_class ["item-name"]] [a ~a:[a_href (Xml.uri_of_string hn)] [txt subth]];
              div ~a:[a_class ["item-basic-desc"]] (c_markdown hdoc rth env)
            ]
          ] @ (if tdoc <> []
               then [details ~a:[a_class ["item-details"]] (summary [])
                             (List.map (fun d -> div ~a:[a_class ["item-details-par"]] (c_markdown d rth env)) tdoc)]
               else []))
      | _ -> assert false
    end
  | ItemDoc (doc, (_, ik, nm, src)) ->
      let psrc = String.trim (String.concat "\n" src) in
        match ik with
        | `Theory -> assert false
        | _ ->
            let (hdoc, tdoc) =
              if doc = [] then "No description available. (However, see source below.)", []
              else if List.length doc = 1 then List.hd doc, []
              else List.hd doc, List.tl doc
            in
            li ~a:[a_id (itemkind_str_pl ik ^ nm) ; a_class ["item-entry"]] [
              div ~a:[a_class ["item-name-desc-container"]] [
                div ~a:[a_class ["item-name"]] [txt nm];
                div ~a:[a_class ["item-basic-desc"]] (c_markdown hdoc rth env)
              ];
              details ~a:[a_class ["item-details"]] (summary [])
                      (List.map (fun d -> div ~a:[a_class ["item-details-par"]] (c_markdown d rth env)) tdoc
                       @ [div ~a:[a_class ["source-container"]]
                              [txt "Source:"; pre ~a:[a_class ["source"]] [txt psrc]]])
            ]

(* -------------------------------------------------------------------- *)
let c_section_main_itemkind ?(supthf : string option) (rth : string) (th : string) (lents_ik : EcScope.docentity list) (env : EcEnv.env) =
  [
    ul ~a:[a_class ["item-list"]]
      (List.map (fun lent_ik -> c_section_main_itemkind_li ?supthf rth th lent_ik env) lents_ik)
  ]

(* -------------------------------------------------------------------- *)
let c_section_main ?(supthf : string option) (rth : string) (th : string) (lents : EcScope.docentity list) (env : EcEnv.env) =
  let iks = [`Type; `Operator; `Axiom; `Lemma; `ModuleType; `Module; `Theory] in
  List.concat
    (List.map (fun ik ->
      let lents_ik = List.filter (fun ent ->
        match ent with
        | ItemDoc (_, (md, ikp, _, _)) -> md = `Specific && ikp = ik
        | SubDoc ((_, (_, ikp, _, _)), _) -> ikp = ik) lents
      in
      match lents_ik with
      | [] -> []
      | _ ->  [
                let iks = itemkind_str_pl ik in
                section ~a:[a_id iks; a_title iks; a_class ["item-section"]] [
                  h2 ~a:[a_class ["section-heading"]] [txt iks];
                  div ~a:[a_class ["item-list-container"]] (c_section_main_itemkind ?supthf rth th lents_ik env)
                ]
              ]
      )
    iks)

let c_body ?(supths : string option) ?(supthf : string option) (rth : string) (th : string) (tstr : string) (gdoc : string list) (ldocents : EcScope.docentity list) (env : EcEnv.env) : [> Html_types.body] elt =
  let sidebar = c_sidebar th ldocents in
  let page_heading =
    div ~a:[a_class ["page-heading-container"]]
      (h1 ~a:[a_class ["page-heading"]] [txt tstr]
        ::
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
                  ])
  in
  let sec_intro = c_section_intro rth gdoc env in
  let sec_main = c_section_main ?supthf rth th ldocents env in
  body (sidebar :: [main (page_heading :: sec_intro @ sec_main)])

(* -------------------------------------------------------------------- *)
let c_page ?(supths : string option) ?(supthf : string option) (rth : string) (th : string) (tstr : string) (gdoc : string list) (ldocents : EcScope.docentity list) (env : EcEnv.env) : [> Html_types.html] elt =
    html (c_head tstr) (c_body ?supths ?supthf rth th tstr gdoc ldocents env)

(* -------------------------------------------------------------------- *)
let emit_page (dp : string) (fn : string) (page : [> Html_types.html ] elt) =
  let wp = Filename.concat dp fn ^ ".html" in
  let file = open_out wp in
  let fmt = Format.formatter_of_out_channel file in
    pp () fmt page;
    Format.fprintf fmt "@.";
    close_out file

(* -------------------------------------------------------------------- *)
let emit_pages (dp : string) (th : string) (tstr : string) (gdoc : string list) (ldocents : EcScope.docentity list) (env : EcEnv.env) =
  let rec c_subpages ?supths ?supthf th docents =
    match docents with
    | [] -> []
    | de :: docents' ->
        match de with
        | ItemDoc _ -> c_subpages ?supths ?supthf th docents'
        | SubDoc ((sgdoc, (smd, _, sth, _)), sldocents) ->
             let ststr = (if smd = `Abstract then "Abstract " else "") ^ "Theory " ^ sth in
             let stsupf =
                match supthf with
                | None -> th
                | Some supf -> c_filename [supf; th]
             in
             let stf = c_filename [stsupf; sth] in
              (stf, c_page ~supths:th ~supthf:stsupf th sth ststr sgdoc sldocents env)
              :: c_subpages ~supths:th ~supthf:stsupf sth sldocents
              @ c_subpages ?supths ?supthf th docents'
  in
  let spgs = c_subpages th ldocents in
  List.iter (fun fnpg -> emit_page dp (fst fnpg) (snd fnpg)) spgs;
  emit_page dp th (c_page th th tstr gdoc ldocents env)


(* -------------------------------------------------------------------- *)
let construct_docitem = ()

let construct_docblock = ()

let construct_docsection = ()

let construct_docpage = ()

let construct_docmodel = ()



(* -------------------------------------------------------------------- *)
(* input = input name, scope contains all documentation items *)
(* let generate_html ?(outdirp : string option) (fname : string option) (scope : EcScope.scope) : unit = *)
(*   match fname with *)
(*   | Some fn -> *)
(*       let kind = *)
(*         try  EcLoader.getkind (Filename.extension fn) *)
(*         with EcLoader.BadExtension _ -> assert false *)
(*       in *)
(*       let dp = *)
(*         match outdirp with *)
(*         | None -> Filename.dirname fn *)
(*         | Some outdirp -> *)
(*           try *)
(*             if Sys.is_directory outdirp *)
(*             then outdirp *)
(*             else raise (Invalid_argument (Format.sprintf "%s is not an existing directory." outdirp)) *)
(*           with *)
(*           | _ as ex -> Printf.eprintf "Exception: %s\n." (Printexc.to_string ex); raise ex *)
(*       in *)
(*       let fn = Filename.basename fn in *)
(*       let th = Filename.remove_extension fn in *)
(*       let tstr = thkind_str kind  ^ " " ^ th in *)
(*       begin *)
(*         try emit_pages dp th tstr (get_gdocstrings scope) (get_ldocentities scope) (env scope) with *)
(*         | _ as ex -> Printf.eprintf "Exception: %s\n." (Printexc.to_string ex); raise ex *)
(*       end *)
(*   | None -> () *)

let generate_documentation
      ?(outdir : string option)
      ~(format : EcDocFormat.t)
      (filename : string)
      (scope : EcScope.scope) : unit =
  let filekind =
    try  EcLoader.getkind (Filename.extension filename)
    with EcLoader.BadExtension ext as ex ->
      Printf.eprintf "Unrecognized extension %s (in file %s)\n%!" ext filename; raise ex
  in
  let dp =
    match outdir with
    | None -> Filename.dirname filename
    | Some outdir ->
       try
         if Sys.is_directory outdir
         then outdir
         else raise (Invalid_argument (Format.sprintf "%s is not an existing directory" outdir))
       with
       | _ as ex -> Printf.eprintf "Exception: %s\n%!" (Printexc.to_string ex); raise ex
  in
  let fn = Filename.basename filename in
  let th = Filename.remove_extension fn in
  let tstr = thkind_str filekind  ^ " " ^ th in
  print_endline "End doc reached successfully"
  (* begin *)
  (*   try emit_pages dp th tstr (get_gdocstrings scope) (get_ldocentities scope) (env scope) with *)
  (*   | _ as ex -> Printf.eprintf "Exception: %s\n%!" (Printexc.to_string ex); raise ex *)
  (* end *)
