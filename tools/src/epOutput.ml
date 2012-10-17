(** State of the output file *)

type output_state = {
  mutable cout : out_channel;
  mutable fmt : Format.formatter;
  mutable vpos : int;
  mutable hpos : int;
  mutable max_hpos : int;
  mutable max_vpos : int;
  mutable indent_level : int;
  mutable pending_indent : bool;
}

let key = 5
let quad = 10
let sim = 3 

let output = {
  pending_indent = false;
  cout = stdout;
  fmt = Format.std_formatter;
  vpos = 0;
  hpos = 0;
  max_hpos = 0;
  max_vpos = 0;
  indent_level = 0;
}

let check_pending_indent () = output.pending_indent
  
(** Header of filname.tex *)
let print_header () =
  let pp = Format.fprintf output.fmt in
  pp "\\documentclass[a4paper,10pt]{article}@\n";
  pp "@\n";
  pp "\\usepackage{amsmath}@\n";
  pp "\\usepackage{amsfonts}@\n";
  pp "\\usepackage{stmaryrd}@\n";
(*  pp "\\usepackage{array}@\n";
  pp "\\usetikzlibrary{shapes,fit,chains,backgrounds}@\n";*)
  pp "%%\\usepackage[active,tightpage,auctex]{preview}@\n";
  pp "%%\\PreviewEnvironment{tabular*}@\n";
  pp "@\n";
  pp "@\n";
  pp "\\begin{document}@\n";
  pp "@\n";
  pp "@\n";
  pp "\\small@\n";
  pp "\\paragraph{}@\n";
  pp "\\fbox{@\n";
  Format.fprintf output.fmt 
    "\\begin{tabular*}{%d pt}{l}@\n" 
    (output.max_hpos + 30);
  pp "\\ensuremath{@\n";
  pp "%%@\n";
  pp "\\begin{array}[t]{l}@\n"

(** Use to divide when the vertical position is greater than max_vpos  *)
let print_another_array () =
  let pp = Format.fprintf output.fmt in
  pp "@\n";
  pp "\\end{array}@\n";
  pp "%%@\n";
  pp "}@\n";
  pp "\\\\@\n";
  pp "\\end{tabular*}}@\n";
  pp "\\paragraph{}@\n";
  pp "\\fbox{@\n";
  Format.fprintf output.fmt 
    "\\begin{tabular*}{%d pt}{l}@\n" 
    (output.max_hpos + 30);
  pp "\\ensuremath{@\n";
  pp "%%@\n";
  pp "\\begin{array}[t]{l}@\n"


(** Footer of filname.tex *)
let print_footer () =
  let pp = Format.fprintf output.fmt in
  pp "@\n";
  pp "\\end{array}@\n";
  pp "%%@\n";
  pp "}@\n";
  pp "\\\\@\n";
  (*pp "\\hline@\n";*)
  pp "\\end{tabular*}}@\n";
  pp "\\end{document}@\n"



let set_pending_indent () =
  output.pending_indent <- true

(** If pending_indent is set, we add to the indent_level *)
let flush_pending_indent () =
  if output.pending_indent then
    output.indent_level <- output.indent_level + 1;
  output.pending_indent <- false

(** We check if its necessary add other array *)    
let check_for_separation () =
  if (output.vpos >= output.max_vpos) then
    (output.vpos <- 0; print_another_array ())

(** Print a newline if its necessary *)
let add_newline () = 
  if output.hpos <> 0 then
    (output.hpos <- 0;
     output.vpos <- output.vpos + 1;
     Format.fprintf output.fmt "\\\\@\n";
     flush_pending_indent ();
     check_for_separation ())

(** Put another level of indentation *)
let add_indent () = 
  output.indent_level <- output.indent_level + 1 ;
  add_newline ()

(** Remove one level of indentation *)
let del_indent () = 
  if output.pending_indent then
    output.pending_indent <- false
  else
    (output.indent_level <- output.indent_level - 1;
     add_newline ())




let create_output filename = 
  output.cout <- open_out filename; 
  output.fmt <- Format.formatter_of_out_channel output.cout;
  print_header ()

let close_output () =
  print_footer ();
  Format.fprintf output.fmt "@.";
  close_out output.cout

(* Generate a list of "\quad\quad ..." according to the level *)
let rec list_indent  = function
  | 0 -> " "
  | n -> String.concat "" ["\\quad"; list_indent (n-1)]
  

let add_item item size =
  let sep = (if output.hpos = 0 then "" else " \  ") in
  let s_sep = (if output.hpos = 0 then 0 else sim ) in
  let ind = (if output.hpos <> 0 then "" else list_indent output.indent_level ) in
  let n = (if output.hpos <> 0 then 0 else output.indent_level * quad) in
  output.hpos <- output.hpos + size + s_sep + n;
  Format.fprintf output.fmt "%s%s%s" ind sep item

let add_emptyline () =
  add_newline ();
  output.vpos <- output.vpos + 1;
  Format.fprintf output.fmt "\\\\@\n" 

let get_indent_level () = output.indent_level
let get_indent_size () = output.indent_level * quad

let add_newline_item item size =
  add_newline ();
  add_item item size

let set_max_height = function
  | 0 -> output.max_vpos <- 43
  | n -> output.max_vpos <- n

let set_max_width  = function
  | 0 -> output.max_hpos <- 330
  | n -> output.max_hpos <- n

let get_actual_hposition () = output.hpos
let get_max_hpos () = output.max_hpos
let check_hspace_for n = 
  (output.hpos + n + (get_indent_size ()) + sim <= output.max_hpos)


