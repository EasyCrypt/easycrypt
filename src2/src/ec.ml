let _ =
  let lexbuf = Lexer.new_lexbuf (Some Sys.argv.(1)) in

    while true do
      match Lexer.read lexbuf with
        | prog, false -> List.iter Commands.process prog
        | _   , true  -> exit 0
    done
