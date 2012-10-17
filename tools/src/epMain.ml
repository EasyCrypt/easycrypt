let cmd     = ref ""
let outf    = ref ""
let files   = ref []
let max_height = ref 0
let max_width  = ref 0 

let spec =
  [
    ("-o", Arg.String  (fun x -> outf := x), "set output file");
    ("-w", Arg.Int (fun n -> max_width := n), "set width of output");
    ("-h", Arg.Int (fun n -> max_height := n), "set height of output")
  ]

let usage () = "usage : " ^ !cmd ^ " [options] files"

let parse () =
  cmd := Array.get Sys.argv 0;
  let infile x = files := x :: !files in
    Arg.parse spec infile (usage ());
    if (List.length !files) <> 1 then
      (Printf.eprintf "Error no input file \n"; exit 1)

let open_file s =
  try 
    open_in s
  with Sys_error s ->
    Printf.eprintf "%s" s; exit 1
      
let read_file x = 
  let ch = open_file x in
  let lexbuf = Lexing.from_channel ch in
  let ls = 
    try 
      EpParser.codeplus EpLexer.token lexbuf 
    with Parsing.Parse_error ->
      Printf.eprintf "Parse error in %s\n" x; exit 1
  in
    close_in ch; ls


let output_file () = 
  let fullname = List.hd !files in
  let dir =  Filename.dirname fullname in
  let name = Filename.basename fullname in
  let file_tex = String.concat "" [Filename.chop_extension name; ".tex"] in
  let full_file_tex = Filename.concat dir file_tex in
  full_file_tex

let _ = 
  parse (); 
  let file  = List.hd !files in 
  let xs = read_file file in
  EpOutput.set_max_width !max_width;
  EpOutput.set_max_height!max_height;
  let outf = if (!outf = "") then (output_file ()) else !outf in
  EpOutput.create_output outf;
  EpProcess.start xs;
  EpOutput.close_output ()



