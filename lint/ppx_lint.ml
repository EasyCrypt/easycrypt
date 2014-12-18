(* -------------------------------------------------------------------- *)
open Ast_mapper
open Parsetree

(* -------------------------------------------------------------------- *)
type error =
| CatchAllInTryWith
| CatchAllInMatch

exception Error of Location.t * error

(* -------------------------------------------------------------------- *)
let string_of_error = function
  | CatchAllInTryWith -> "catch all in try...with..."
  | CatchAllInMatch   -> "catch all in match...with"

(* -------------------------------------------------------------------- *)
let error_of_exn = function
  | Error (loc, error) ->
      Some (Location.error ~loc (string_of_error error))
  | _ -> None

(* -------------------------------------------------------------------- *)
let () = Location.register_error_of_exn error_of_exn

(* -------------------------------------------------------------------- *)
let rec is_wild_pattern (p : pattern) =
  match p.ppat_desc with
  | Ppat_any   -> true
  | Ppat_var _ -> true

  | Ppat_alias (p, _) ->
      is_wild_pattern p

  | Ppat_or (p1, p2) ->
      is_wild_pattern p1 || is_wild_pattern p2

  | Ppat_constraint (p, _) ->
      is_wild_pattern p

  | Ppat_extension ({ Asttypes.txt = "catchall" }, _) ->
      false

  | Ppat_extension (_, PPat (p, _)) ->
     is_wild_pattern p

  | _ -> false

(* -------------------------------------------------------------------- *)
let is_wild_case (c : case) =
  is_wild_pattern c.pc_lhs

(* -------------------------------------------------------------------- *)
let rec catchall_mapper =
  { default_mapper with
      expr = fun mapper expr ->
        match expr.pexp_desc with
        | Pexp_try (e, clauses) ->
            if List.exists is_wild_case clauses then
              Format.eprintf "Lint: %a %s\n%!"
                Location.print_loc expr.pexp_loc
                (string_of_error CatchAllInTryWith);
          let e = catchall_mapper.expr mapper e in
          let clauses = catchall_mapper.cases mapper clauses in
          { expr with pexp_desc = Pexp_try (e, clauses) }
        | _ -> default_mapper.expr mapper expr }

(* -------------------------------------------------------------------- *)
let () = register "catchall" (fun _ -> catchall_mapper)
