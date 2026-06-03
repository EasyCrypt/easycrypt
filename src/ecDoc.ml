(* -------------------------------------------------------------------- *)
open Tyxml.Html

open EcScope

(* -------------------------------------------------------------------- *)
module DocText = struct
  type t = string

  let of_markdown s = s
  let to_markdown t = t
end

module DocModel = struct
  type page_id = string list

  type section_id = {
      sid_page : page_id;
      sid_key : string;
    }

  type item_id = {
      iid_page : page_id;
      iid_kind : itemkind;
      iid_name : string;
    }

  type item_target =
    | PageTarget of page_id

  type t = docpage list

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
      item_docs : docblock list;
      item_source : string list;
      item_target : item_target option;
    }

  and docblock = DocText.t

  let filename_of_pageid ?ext (id : page_id) : string =
    let base = String.concat "!" id in
    match ext with
    | None -> base
    | Some ext -> base ^ ext

  let rec docpages_of_docpage (page : docpage) : docpage list =
    page :: List.concat (List.map docpages_of_docpage page.page_subpages)

  let docpages_of_docmodel (model : t) : docpage list =
    List.concat (List.map docpages_of_docpage model)
end

module DocBuilder = struct
  module M = DocModel

  let docblock_of_docstring (s : string) : M.docblock =
    DocText.of_markdown s

  let docblocks_of_docstrings (ss : string list) : M.docblock list =
    List.map docblock_of_docstring ss

  let pageid_of_name ?pid (name : string) : M.page_id =
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
        ~(pid : M.page_id)
        (docstr, (mode, kind, name, src))
      : M.docitem =
    {
      item_id = {
        iid_page = pid;
        iid_kind = kind;
        iid_name = name;
      };
      item_mode = mode;
      item_docs = docblocks_of_docstrings docstr;
      item_source = src;
      item_target = None;
    }

  let docitem_of_subdoc
        ~(pid : M.page_id)
        (docstr, (mode, kind, name, src))
      : M.docitem =
    let child_pid = pageid_of_name ~pid name in
    {
      item_id = {
        iid_page = pid;
        iid_kind = kind;
        iid_name = name;
      };
      item_mode = mode;
      item_docs = docblocks_of_docstrings docstr;
      item_source = src;
      item_target = Some (M.PageTarget child_pid);
    }

  let docitem_of_docent ~(pid : M.page_id) (docent : docentity) : M.docitem =
    match docent with
    | ItemDoc (docstr, item) ->
       docitem_of_itemdoc ~pid (docstr, item)

    | SubDoc ((docstr, item), _) ->
       docitem_of_subdoc ~pid (docstr, item)

  let docitems_of_docents
        ~(pid : M.page_id)
        (docents : docentity list)
      : M.docitem list =
    List.map (docitem_of_docent ~pid) docents

  let docsection_of_docitems
        ~(pid : M.page_id)
        ~(skey : string)
        ~(title : string)
        (docitems : M.docitem list)
      : M.docsection =
    {
      section_id = { sid_page = pid; sid_key = skey; };
      section_title = title;
      section_items = docitems;
    }

  let docsection_of_docitems_by_kind
        ~(pid : M.page_id)
        ~(kind : itemkind)
        (docitems : M.docitem list)
      : M.docsection option =
    let
      items = (List.filter (fun it -> it.M.item_id.iid_kind = kind) docitems)
    in
    match items with
    | [] -> None
    | _ ->
       let title = namepl_of_itemkind kind in
       let skey = sectionkey_of_itemkind kind in
       Some (docsection_of_docitems ~pid:pid ~skey:skey ~title:title items)

  let docsections_of_docitems_by_kind
        ~(pid : M.page_id)
        (docitems : M.docitem list)
      : M.docsection list =
    List.filter_map (fun ik -> docsection_of_docitems_by_kind ~pid:pid ~kind:ik docitems) all_itemkinds

  let rec docpage_of_docent
            ?(pid : M.page_id option)
            (docent : docentity)
          : M.docpage option =
    match docent with
    | ItemDoc _ -> None
    | SubDoc ((docstr, (mode, _kind, name, _src)), docents) ->
       let pageid = pageid_of_name ?pid name in
       let docitems = docitems_of_docents ~pid:pageid docents in
       let subpages =
         List.filter_map (docpage_of_docent ~pid:pageid) docents
       in
       Some {
         page_id = pageid;
         page_parent = pid;
         page_title = pagetitle_of_mode_and_name mode name;
         page_intro = docblocks_of_docstrings docstr;
         page_sections =
           docsections_of_docitems_by_kind ~pid:pageid docitems;
         page_subpages = subpages;
       }

  let root_page_of_scope ~(thname : string) ~(thmode : mode) (scope : EcScope.scope) : M.docpage =
    let pageid = [thname] in
    let docents = get_ldocentities scope in
    let docitems = docitems_of_docents ~pid:pageid docents in
    let subpages =
      List.filter_map (docpage_of_docent ~pid:pageid) docents
    in
    {
      page_id = pageid;
      page_parent = None;
      page_title = pagetitle_of_mode_and_name thmode thname;
      page_intro = docblocks_of_docstrings (get_gdocstrings scope);
      page_sections =
        docsections_of_docitems_by_kind ~pid:pageid docitems;
      page_subpages = subpages;
    }
end

module DocMarkdown = struct
  module M = DocModel

  let page_level = 1
  let section_level = 2
  let item_level = 3

  let refname_of_pageid (pid : M.page_id) : string =
    M.filename_of_pageid ~ext:".md" pid

  let heading (level : int) (title : string) : string =
    String.make level '#' ^ " " ^ title

  let page_heading (title : string) : string =
    heading page_level title

  let section_heading (title : string) : string =
    heading section_level title

  let item_heading (title : string) : string =
    heading item_level title

  let render_combine (ss : string list) : string =
    ss
    |> List.filter (fun s -> s <> "")
    |> String.concat "\n\n"

  let render_inline_code (s : string) : string =
    "`" ^ s ^ "`"

  let render_link ~(label : string) ~(target : string) : string =
    Printf.sprintf "[%s](%s)" label target

  let render_docblock (docblock : M.docblock) : string =
    DocText.to_markdown docblock

  let render_docblocks (docblocks : M.docblock list) : string =
    docblocks
    |> List.map render_docblock
    |> render_combine

  let render_source (src : string list) : string =
    match src with
    | [] -> ""
    | lines ->
       "```easycrypt\n"
       ^ String.concat "\n" lines
       ^ "\n```"

  let render_item_target (target : M.item_target) : string =
    match target with
    | M.PageTarget pid ->
       refname_of_pageid pid

  let render_item_title (docitem : M.docitem) : string =
    let title = render_inline_code docitem.item_id.iid_name in
    match docitem.item_target with
    | None ->
       title
    | Some target ->
       render_link ~label:title ~target:(render_item_target target)

  let render_item (docitem : M.docitem) : string =
    let title = render_item_title docitem in
    let docs = render_docblocks docitem.item_docs in
    let src = render_source docitem.item_source in
    [
      item_heading title;
      docs;
      src;
    ]
    |> render_combine

  let render_section (docsection : M.docsection) : string =
    let title = docsection.section_title in
    let docitems = render_combine (List.map render_item docsection.section_items) in
    [
      section_heading title;
      docitems;
    ]
    |> render_combine

  let render_page (docpage : M.docpage) : string =
    let title = docpage.page_title in
    let intro = render_docblocks docpage.page_intro in
    let docsections = render_combine (List.map render_section docpage.page_sections) in
    [
      page_heading title;
      intro;
      docsections;
    ]
    |> render_combine

  let render_page_tree (docpage : M.docpage) : string list =
    docpage
    |> M.docpages_of_docpage
    |> List.map render_page

  type rendered_file = {
      file_name : string;
      file_content : string;
    }

  let render_file (docpage : M.docpage) : rendered_file =
    {
      file_name = refname_of_pageid docpage.page_id;
      file_content = render_page docpage;
    }

  let render_file_tree (docpage : M.docpage) : rendered_file list =
    docpage
    |> M.docpages_of_docpage
    |> List.map render_file

  let render_model (model : M.t) : rendered_file list =
    model
    |> List.map render_file_tree
    |> List.concat
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
      (scope : scope) : unit=
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
  let page = DocBuilder.root_page_of_scope th `Specific scope in
  List.iter print_endline (DocMarkdown.render_page_tree page)
                (* begin *)
                (*   try emit_pages dp th tstr (get_gdocstrings scope) (get_ldocentities scope) (env scope) with *)
                (*   | _ as ex -> Printf.eprintf "Exception: %s\n%!" (Printexc.to_string ex); raise ex *)
                (* end *)
