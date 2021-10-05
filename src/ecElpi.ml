open Elpi.API

let setup =
  Setup.init [Elpi__Builtin.std_builtins] "." []

let program el lts =
  let fl = Compile.default_flags in
  let ps = List.map (fun (loc, t) -> Utils.clause_of_term 0 loc t) lts in
  Compile.program fl el ps

let query p loc q =
  let cq = Query.compile p loc q in
  Compile.optimize cq

let query_once p loc q =
  let exec = query p loc q in
  Execute.once exec

let _ =
  let (el, strs) = setup in
  let lf : Ast.Loc.t = {
      source_name    = "foo";
      source_start   = 0;
      source_stop    = 0;
      line           = 0;
      line_starts_at = 0;
  } in
  (*TODO: we should use the smart constructors in RawData to build the term or terms.*)
  let t = RawOpaqueData.of_loc lf in
  let lts = [(lf, t)] in
  let p = program el lts in
  let lq : Ast.Loc.t = {
      source_name    = "bar";
      source_start   = 0;
      source_stop    = 0;
      line           = 0;
      line_starts_at = 0;
  } in
  let q = Query.Query { predicate="bar"; arguments=N} in
  query_once p lq q
