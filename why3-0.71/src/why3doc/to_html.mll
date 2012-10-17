(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-2011                                               *)
(*    François Bobot                                                      *)
(*    Jean-Christophe Filliâtre                                           *)
(*    Claude Marché                                                       *)
(*    Andrei Paskevich                                                    *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Library General Public           *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)

(* Why3 to HTML *)

{

  open Format

  (* command line parsing *)

  let usage_msg = sprintf
    "Usage: %s [-o directory] [file...]"
    (Filename.basename Sys.argv.(0))

  let opt_output = ref None
  let opt_queue = Queue.create ()
  let opt_body = ref false

  let option_list = Arg.align [
    "-o", Arg.String (fun s -> opt_output := Some s),
      "<dir>  Print files in <dir>";
    "--output", Arg.String (fun s -> opt_output := Some s),
      "  same as -o";
    "-b", Arg.Set opt_body,
      "  outputs HTML body only";
  ]

  let add_opt_file x = Queue.add x opt_queue

  let () = Arg.parse option_list add_opt_file usage_msg

  (* let count = ref 0 *)
  (* let newline fmt () = incr count; fprintf fmt "\n%3d: " !count *)
  (* let () = newline () *)
  let newline fmt () = fprintf fmt "\n"

  let is_keyword =
    let ht = Hashtbl.create 97 in
    List.iter
      (fun s -> Hashtbl.add ht s ())
      [ "theory"; "end";
        "type"; "function"; "predicate"; "clone"; "use";
        "import"; "export"; "axiom"; "inductive"; "goal"; "lemma";

        "match"; "with"; "let"; "in"; "if"; "then"; "else";
        "forall"; "exists";

        "as"; "assert"; "begin";
        "do"; "done"; "downto"; "else";
        "exception"; "val"; "for"; "fun";
        "if"; "in";
        "module"; "mutable";
        "rec"; "then"; "to";
        "try"; "while"; "invariant"; "variant"; "raise"; "label";
      ];
    fun s -> Hashtbl.mem ht s

}

let ident = ['A'-'Z' 'a'-'z' '_'] ['A'-'Z' 'a'-'z' '0'-'9' '_']*

rule scan fmt = parse
  | "(*)"  { fprintf fmt "(*)"; scan fmt lexbuf }
  | "(*"   { fprintf fmt "<font color=\"990000\">(*";
             comment fmt lexbuf;
             fprintf fmt "</font>";
             scan fmt lexbuf }
  | eof    { () }
  | ident as s
           { if is_keyword s then begin
               fprintf fmt "<font color=\"green\">%s</font>" s
             end else
               fprintf fmt "%s" s;
             scan fmt lexbuf }
  | "<"    { fprintf fmt "&lt;"; scan fmt lexbuf }
  | "&"    { fprintf fmt "&amp;"; scan fmt lexbuf }
  | "\n"   { newline fmt (); scan fmt lexbuf }
  | '"'    { fprintf fmt "\""; string fmt lexbuf; scan fmt lexbuf }
  | "'\"'"
  | _ as s { fprintf fmt "%s" s; scan fmt lexbuf }

and comment fmt = parse
  | "(*"   { fprintf fmt "(*"; comment fmt lexbuf; comment fmt lexbuf }
  | "*)"   { fprintf fmt "*)" }
  | eof    { () }
  | "\n"   { newline fmt (); comment fmt lexbuf }
  | '"'    { fprintf fmt "\""; string fmt lexbuf; comment fmt lexbuf }
  | "<"    { fprintf fmt "&lt;"; comment fmt lexbuf }
  | "&"    { fprintf fmt "&amp;"; comment fmt lexbuf }
  | "'\"'"
  | _ as s { fprintf fmt "%s" s; comment fmt lexbuf }

and string fmt = parse
  | '"'    { fprintf fmt "\"" }
  | "<"    { fprintf fmt "&lt;"; string fmt lexbuf }
  | "&"    { fprintf fmt "&amp;"; string fmt lexbuf }
  | "\\" _
  | _ as s { fprintf fmt "%s" s; string fmt lexbuf }

{

  let style_css fname =
    let c = open_out fname in
    output_string c
"a:visited {color : #416DFF; text-decoration : none; }
a:link {color : #416DFF; text-decoration : none;}
a:hover {color : Red; text-decoration : none; background-color: #5FFF88}
a:active {color : Red; text-decoration : underline; }
.keyword { font-weight : bold ; color : Red }
.keywordsign { color : #C04600 }
.superscript { font-size : 4 }
.subscript { font-size : 4 }
.comment { color : Green }
.constructor { color : Blue }
.type { color : #5C6585 }
.string { color : Maroon }
.warning { color : Red ; font-weight : bold }
.info { margin-left : 3em; margin-right : 3em }
.code { color : #465F91 ; }
h1 { font-size : 20pt ; text-align: center; }
h2 { font-size : 20pt ; border: 1px solid #000000; margin-top: 5px; margin-bottom: 2px;text-align: center; background-color: #90BDFF ;padding: 2px; }
h3 { font-size : 20pt ; border: 1px solid #000000; margin-top: 5px; margin-bottom: 2px;text-align: center; background-color: #90DDFF ;padding: 2px; }
h4 { font-size : 20pt ; border: 1px solid #000000; margin-top: 5px; margin-bottom: 2px;text-align: center; background-color: #90EDFF ;padding: 2px; }
h5 { font-size : 20pt ; border: 1px solid #000000; margin-top: 5px; margin-bottom: 2px;text-align: center; background-color: #90FDFF ;padding: 2px; }
h6 { font-size : 20pt ; border: 1px solid #000000; margin-top: 5px; margin-bottom: 2px;text-align: center; background-color: #90BDFF ; padding: 2px; }
div.h7 { font-size : 20pt ; border: 1px solid #000000; margin-top: 5px; margin-bottom: 2px;text-align: center; background-color: #90DDFF ; padding: 2px; }
div.h8 { font-size : 20pt ; border: 1px solid #000000; margin-top: 5px; margin-bottom: 2px;text-align: center; background-color: #F0FFFF ; padding: 2px; }
div.h9 { font-size : 20pt ; border: 1px solid #000000; margin-top: 5px; margin-bottom: 2px;text-align: center; background-color: #FFFFFF ; padding: 2px; }
.typetable { border-style : hidden }
.indextable { border-style : hidden }
.paramstable { border-style : hidden ; padding: 5pt 5pt}
body { background-color : White }
tr { background-color : White }
td.typefieldcomment { background-color : #FFFFFF }
pre { margin-bottom: 4px }
div.sig_block {margin-left: 2em}";
    close_out c

  let css =
    let css_fname = match !opt_output with
      | None -> "style.css"
      | Some dir -> Filename.concat dir "style.css"
    in
    if !opt_body then
      None
    else begin
      if not (Sys.file_exists css_fname) then style_css css_fname;
      Some css_fname
    end

  let print_header fmt ?(title="") () =
    fprintf fmt "<html>@\n<head>@\n";
    begin match css with
      | None -> ()
      | Some f -> fprintf fmt
          "<link rel=\"stylesheet\" href=\"%s\" type=\"text/css\">@\n" f
    end;
    fprintf fmt "<title>%s</title>@\n" title;
    fprintf fmt "</head>@\n<body>@\n"

  let print_footer fmt () =
    fprintf fmt "</body></html>\n"

  let do_file fname =
    (* input *)
    let cin = open_in fname in
    let lb = Lexing.from_channel cin in
    (* output *)
    let f = Filename.basename fname in
    let base =
      match !opt_output with
        | None -> f
        | Some dir -> Filename.concat dir f
    in
    let fhtml = base ^ ".html" in
    let cout = open_out fhtml in
    let fmt = formatter_of_out_channel cout in
    if not !opt_body then print_header fmt ~title:f ();
    fprintf fmt "<pre>@\n";
    scan fmt lb;
    fprintf fmt "</pre>@\n";
    if not !opt_body then print_footer fmt ();
    close_out cout

  let () =
    Queue.iter do_file opt_queue

}

(*
Local Variables:
compile-command: "unset LANG; make -C ../.. bin/why3doc.opt"
End:
*)

