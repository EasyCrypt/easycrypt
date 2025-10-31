(* -------------------------------------------------------------------- *)
open Ptree

(* -------------------------------------------------------------------- *)
let parse (name : string) (input : IO.input) : Ptree.pprogram =
  let lexbuf = Lexing.from_channel input in
  Lexing.set_filename lexbuf name;
  Parser.program Lexer.main lexbuf

(* -------------------------------------------------------------------- *)
let print_source_for_range (fmt : Format.formatter) (range : range) (name : string) =
  let lines = File.lines_of name in
  let nlines = Enum.count lines in

  let begin_ = fst range.rg_begin - 1 in
  let end_ = fst range.rg_end in

  let ctxt = 2 in
  let ctxt_s = max 0 (begin_ - ctxt) in
  let ctxt_e = min nlines (end_ + ctxt) in

  let lines = Enum.skip ctxt_s lines in
  let lines = Enum.take (ctxt_e - ctxt_s) lines in

  let sz = int_of_float (ceil (log10 (float_of_int end_ +. 1.))) in

  begin
    let doline (i : int) = Format.sprintf "%d---------" i in
    Format.fprintf fmt "%*s  | %s@."
      sz ""
      (String.concat "" (List.map doline (List.init 7 identity)));
  end;
  Enum.iteri
    (fun i line ->
      let lineno = ctxt_s + i in
      let mark = if begin_ <= lineno && lineno < end_ then ">" else " " in
      Format.fprintf fmt "%*d %s| %s@." sz (lineno + 1) mark line)
    lines
