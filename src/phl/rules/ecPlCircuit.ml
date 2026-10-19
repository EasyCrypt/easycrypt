(* -------------------------------------------------------------------- *)
open EcAst
open EcEnv
open EcTypes
open EcFol
open EcLowCircuits
open EcCircuits

(* -------------------------------------------------------------------- *)
exception CircuitInvalid
exception CircuitExceptions

(* -------------------------------------------------------------------- *)
let form_list_from_iota (hyps : LDecl.hyps) (f : form) : form list =
  match sform_of_form f with
  | SFop ((p, _), [n; m]) when EcPath.p_equal p EcCoreLib.CI_List.p_iota ->
    let n = int_of_form hyps n in
    let m = int_of_form hyps m in
    List.init (BI.to_int m) (fun i -> f_int BI.(add n (of_int i)))
  | _ -> raise (DestrError "iota")

(* -------------------------------------------------------------------- *)
let rec destr_conjunction (hyps : LDecl.hyps) (f : form) : form list =
  let redmode = { (circ_red hyps) with zeta = false } in

  match sform_of_form (EcCallbyValue.norm_cbv redmode hyps f) with
  | SFand (_, (f1, f2)) ->
    destr_conjunction hyps f1 @ destr_conjunction hyps f2

  | SFop ((p, _), [pred; lst]) when EcPath.p_equal p EcCoreLib.CI_List.p_all -> begin
    match form_list_from_iota hyps lst with
    | fs -> List.map (fun farg -> f_app pred [farg] tbool) fs
    | exception DestrError _ -> [f]
  end

  | _ -> [f]

(* -------------------------------------------------------------------- *)
(* The atomic parts of the precondition, as _open_ circuits:
     /\ p_i => [p_i]_i,
     a = b  => [a.[i] = b.[i]]_i
   The explicit equations [pv = v] (program variable = value) are first
   recorded in the state. *)
let process_pre (hyps : LDecl.hyps) ~(st : state) (f : form) :
    state * circuit list =
  let fs = destr_conjunction hyps f in

  let process_equality (s : state) (f : form) : state =
    let f = EcCallbyValue.norm_cbv (circ_red hyps) hyps f in
    match sform_of_form f with
    | SFeq (a, b) -> begin
      match
        ( EcCallbyValue.norm_cbv (circ_red hyps) hyps a,
          EcCallbyValue.norm_cbv (circ_red hyps) hyps b )
      with
      | {f_node = Fpvar (PVloc pv, m); _}, fv
      | fv, {f_node = Fpvar (PVloc pv, m); _} ->
        update_state_pv s m pv (circuit_of_form st hyps fv)
      | _ -> s
    end
    | _ -> s
  in

  let st = List.fold_left process_equality st fs in

  (* The conjuncts convertible to circuits, in the state above. *)
  let process_form (f : form) : circuit list =
    match sform_of_form f with
    | SFeq (f1, f2) ->
      let c1 =
        circuit_of_form st hyps (EcCallbyValue.norm_cbv (circ_red hyps) hyps f1)
      in
      let c2 =
        circuit_of_form st hyps (EcCallbyValue.norm_cbv (circ_red hyps) hyps f2)
      in
      circuit_eqs c1 c2
    | _ -> begin
      try
        [
          circuit_of_form st hyps (EcCallbyValue.norm_cbv (circ_red hyps) hyps f);
        ]
      with _ -> []
    end
  in

  let cs =
    List.fold_left (fun acc f -> List.rev_append (process_form f) acc) [] fs
    |> List.rev
  in
  st, cs

(* -------------------------------------------------------------------- *)
let solve_post ~(st : state) ~(pres : circuit list) (hyps : LDecl.hyps) (post : form)
    : bool =
  let env = LDecl.toenv hyps in
  let lap = EcCircuits.stopwatch env in
  let posts = destr_conjunction hyps post in
  lap "Done with postcondition normalization (destr_conj)";
  let pres = List.map (state_close_circuit st) pres in

  posts |> List.to_seq
  |> Seq.concat_map (fun post ->
         match sform_of_form post with
         | SFeq (f1, f2) -> circuits_of_equality ~st ~hyps f1 f2 |> List.to_seq
         | _ ->
           Seq.return (circuit_of_form st hyps post |> state_close_circuit st))
  |> List.of_seq
  |> circuit_check_posts ~env ~pres
