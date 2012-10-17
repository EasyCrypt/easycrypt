
let index_compare s n x = 
  let rec f m = 
    match m with
      | m when m < 0 -> true
      | m when m + n >= String.length s -> false
      | m -> 
	  if s.[n+m] == x.[m] then f (m-1) else false
  in
    f (String.length x - 1)
      
      
let index_of s n = 
  let rec f m = 
    match m with 
      | m when m = String.length s -> -1
      | m -> if index_compare s m n then m else f (m+1)
  in
    f 0
  

let is_whitespace x =  x == ' ' || x == '\t'

let trim x = 
  let lix = String.length x - 1 in
  let ix1 = ref 0 and ix2 = ref lix in
    while !ix1 <= lix && is_whitespace x.[!ix1] do incr ix1 done;
    while !ix2 >= 0   && is_whitespace x.[!ix2] do decr ix2 done;
    if ix1 > ix2 then "" else String.sub x !ix1 (!ix2 - !ix1 + 1) 
      

module Preview = 
struct
  

  let split_snippet s six =
    let ix1 = String.index_from s six '(' 
    and ix2 = String.index_from s six '+'
    and ix3 = String.index_from s six 'x'
    and ix4 = String.index_from s six ')' in
      (String.sub s (ix1+1) (ix2-ix1-1),
       String.sub s (ix2+1) (ix3-ix2-1),
       String.sub s (ix3+1) (ix4-ix3-1)
      )
	
  let find_snippet s = 
    let ix1 = index_of s "Snippet" 
    and ix2 = index_of s "ended." in
      if ix1 < 0 || ix2 < 0 || ix2 <= ix1
      then None
      else begin
	try
	  let ns = String.sub s (ix1+8) (ix2-ix1-8) in
	  let n  = int_of_string (trim ns) in
	  let r  = split_snippet s ix1 in
	    Some (n,r)
	with Failure s -> None
      end

let process_log_line s = 
  let spperpt = 65536 in    
  match find_snippet s with
    | None                -> []
    | Some (n,(s1,s2,s3)) -> 
	   let n1, n2, n3 =
	     int_of_string s1,
	     int_of_string s2,
	     int_of_string s3 
      in [ (n, ((n3 / spperpt)-11, (n1+n2) / spperpt)) ]
		
let process_log f = 
  let c       = open_in f in

    let rec f acc =
      try
	     let s = input_line c in
   	  let r = process_log_line s in
	      f (acc @ r) 
      with End_of_file -> acc
    in
    let r = f [] in close_in c; r

let template_file s =
  String.concat "\n"
    ["\\documentclass[a4paper,10pt]{article}";
     "\\usepackage{amsmath}";
     "\\usepackage{amsfonts}";
(*     "\\usepackage{stmaryrd}";
     "\\usepackage{xspace}";
     "\\usepackage{url}";*)
     "\\usepackage{array}";
(*     "\\usetikzlibrary{shapes,fit,chains}";*)
     "\\usepackage[active,tightpage,auctex]{preview}";
     "\\PreviewEnvironment{array}";
     "\\begin{document}";
     "\\pagestyle{empty}";
     s;
     "\\end{document}"]

let make_preview s =
  String.concat "\n"
     ["\\begin{preview}";
     "\\begin{tabular}{l}";
     "\\small";
     "\\ensuremath{";
     "%";
     "\\begin{array}[t]{@{}l@{}}";
     s;
     "\\end{array}";
     "%";
     "}";
     "\\\\";
     "\\end{tabular}";
     "\\end{preview}"]
 


let process_preview c n = 
  let c = template_file c in
  let fn = Filename.temp_file n ".tex" in
  Printf.printf "preview file %s\n" fn;
  let fc = open_out fn in
  Printf.fprintf fc "%s\n" c; close_out fc;
  let dn = Filename.dirname fn in
  let _  = Sys.command
    (Printf.sprintf "pdflatex -output-directory %s %s %s"
	                  dn fn (if false then "" else " >& /dev/null"))
  in
  let ln = Filename.chop_extension fn ^ ".log" in
    process_log ln
	  


end


