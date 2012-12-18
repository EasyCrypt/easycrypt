open Ocamlbuild_plugin

let run_and_read      = Ocamlbuild_pack.My_unix.run_and_read
let blank_sep_strings = Ocamlbuild_pack.Lexers.blank_sep_strings

let find_packages () =
  blank_sep_strings &
    Lexing.from_string &
      run_and_read "ocamlfind list | cut -d' ' -f1"

let ocamlfind = fun command -> S[A"ocamlfind"; command]

let internal_libraries = fun libraries ->
  List.iter (fun x -> ocaml_lib (x ^ "/" ^ x)) libraries

let _ = dispatch begin function
   | Before_options ->
       Options.ocamlc     := ocamlfind & A"ocamlc";
       Options.ocamlopt   := ocamlfind & A"ocamlopt";
       Options.ocamldep   := ocamlfind & A"ocamldep";
       Options.ocamldoc   := ocamlfind & A"ocamldoc";
       Options.ocamlmktop := ocamlfind & A"ocamlmktop"

   | After_rules ->
       flag ["ocaml"; "link"] & A"-linkpkg";

       (* pkg_* switches *)
       List.iter begin fun pkg ->
         flag ["ocaml"; "compile";  "pkg_"^pkg] & S[A"-package"; A pkg];
         flag ["ocaml"; "ocamldep"; "pkg_"^pkg] & S[A"-package"; A pkg];
         flag ["ocaml"; "doc";      "pkg_"^pkg] & S[A"-package"; A pkg];
         flag ["ocaml"; "link";     "pkg_"^pkg] & S[A"-package"; A pkg];
       end (find_packages ());

       (* Preprocessing *)
       flag ["ocaml"; "pp"; "deriving"] (A"deriving");

       (* Threads swicthes *)
       flag ["ocaml"; "pkg_threads"; "compile"] (S[A "-thread"]);
       flag ["ocaml"; "pkg_threads"; "link"] (S[A "-thread"]);

   | _ -> ()
end
