open Ocamlbuild_plugin

let _ = dispatch begin function
   | After_options ->
       Options.ocamlc   := S[!Options.ocamlc  ; A"-rectypes"];
       Options.ocamlopt := S[!Options.ocamlopt; A"-rectypes"];

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

       (* menhir & --explain/--trace *)
       flag ["ocaml"; "parser"; "menhir"; "menhir_explain"] & A"--explain";
       flag ["ocaml"; "parser"; "menhir"; "menhir_trace"  ] & A"--trace";

       (* Threads switches *)
       flag ["ocaml"; "pkg_threads"; "compile"] (S[A "-thread"]);
       flag ["ocaml"; "pkg_threads"; "link"] (S[A "-thread"]);

   | _ -> ()
end
