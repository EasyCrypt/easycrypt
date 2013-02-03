open Ocamlbuild_plugin

let run_and_read      = Ocamlbuild_pack.My_unix.run_and_read
let blank_sep_strings = Ocamlbuild_pack.Lexers.blank_sep_strings

let find_packages () =
  blank_sep_strings &
    Lexing.from_string &
      run_and_read "ocamlfind list | cut -d' ' -f1"

let find_syntaxes () = ["camlp4o"; "camlp4r"]

let ocamlfind = fun command -> S[A"ocamlfind"; command]

let internal_libraries = fun libraries ->
  List.iter (fun x -> ocaml_lib (x ^ "/" ^ x)) libraries

let _ = dispatch begin function
   | Before_options ->
       Options.ocamlc     := ocamlfind & S[A"ocamlc"  ; A"-rectypes"];
       Options.ocamlopt   := ocamlfind & S[A"ocamlopt"; A"-rectypes"];
       Options.ocamldep   := ocamlfind & A"ocamldep"  ;
       Options.ocamldoc   := ocamlfind & A"ocamldoc"  ;
       Options.ocamlmktop := ocamlfind & A"ocamlmktop";

   | After_rules ->
       (* Numerical warnings *)
       begin
         let wflag mode wid =
           let mode = match mode with
             | `Enable  -> "+"
             | `Disable -> "-"
             | `Mark    -> "@"
           in
             S[A"-w"; A(Printf.sprintf "%s%d" mode wid)]
         in
           for i = 1 to 29 do
             flag ["ocaml"; "compile"; Printf.sprintf "warn_+%d" i] & (wflag `Enable  i);
             flag ["ocaml"; "compile"; Printf.sprintf "warn_-%d" i] & (wflag `Disable i);
             flag ["ocaml"; "compile"; Printf.sprintf "warn_@%d" i] & (wflag `Mark    i)
           done
       end;

       (* ocaml / link / ocamlfind *)
       flag ["ocaml"; "link"] & A"-linkpkg";

       (* menhir & --explain/--trace *)
       flag ["ocaml"; "parser"; "menhir"; "menhir_explain"] & A"--explain";
       flag ["ocaml"; "parser"; "menhir"; "menhir_trace"  ] & A"--trace";

       (* pkg_* switches *)
       List.iter begin fun pkg ->
         flag ["ocaml"; "compile";  "pkg_"^pkg] & S[A"-package"; A pkg];
         flag ["ocaml"; "ocamldep"; "pkg_"^pkg] & S[A"-package"; A pkg];
         flag ["ocaml"; "doc";      "pkg_"^pkg] & S[A"-package"; A pkg];
         flag ["ocaml"; "link";     "pkg_"^pkg] & S[A"-package"; A pkg];
       end (find_packages ());

       (* syntax_* switches *)
       List.iter begin fun syntax ->
         flag ["ocaml"; "compile";  "syntax_"^syntax] & S[A"-syntax"; A syntax];
         flag ["ocaml"; "ocamldep"; "syntax_"^syntax] & S[A"-syntax"; A syntax];
         flag ["ocaml"; "doc";      "syntax_"^syntax] & S[A"-syntax"; A syntax];
         flag ["ocaml"; "infer_interface"; "syntax_"^syntax] & S[A"-syntax"; A syntax];
       end (find_syntaxes ());

       (* Threads switches *)
       flag ["ocaml"; "pkg_threads"; "compile"] (S[A "-thread"]);
       flag ["ocaml"; "pkg_threads"; "link"] (S[A "-thread"]);

   | _ -> ()
end
