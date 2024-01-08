(* ==================================================================== *)
open Typing
open Aig

(* ==================================================================== *)
let circuit_of_spec (rs : reg list) (p : adef) : reg =
  assert (List.length rs = List.length p.arguments);
  assert (List.for_all2 (fun r (_, `W n) -> List.length r = n) rs p.arguments);

  let rec of_expr (env : unit) (e : aexpr) : reg =
    match e.node with
    | EIncr (_, e) ->
      Circuit.incr_dropc (of_expr env e)

    | EAdd (_, c, (e1, e2)) -> begin
      let e1 = of_expr env e1 in
      let e2 = of_expr env e2 in
      match c with
      | true  -> Circuit.addc e1 e2
      | false -> Circuit.add_dropc e1 e2
      end

    | ESub (_, (e1, e2)) ->
      let e1 = of_expr env e1 in
      let e2 = of_expr env e2 in
      Circuit.sub_dropc e1 e2

    | EMul (us, hld, _, (e1, e2)) -> begin
      let e1 = of_expr env e1 in
      let e2 = of_expr env e2 in

      match us, hld with
      | `U, `D -> Circuit.umul e1 e2
      | `U, `H -> Circuit.umulh e1 e2
      | `U, `L -> Circuit.umull e1 e2
      | `S, `D -> Circuit.smul e1 e2
      | `S, `H -> Circuit.smulh e1 e2
      | `S, `L -> Circuit.umull e1 e2
      end

    | ENot (_, e) ->
      Circuit.lnot_ (of_expr env e)

    | EOr (_, (e1, e2)) ->
      let e1 = of_expr env e1 in
      let e2 = of_expr env e2 in
      Circuit.lor_ e1 e2

    | EAnd (_, (e1, e2)) ->
      let e1 = of_expr env e1 in
      let e2 = of_expr env e2 in
      Circuit.land_ e1 e2

    | EShift (lr, la, (e1, e2)) ->
      let e1 = of_expr env e1 in
      let e2 = of_expr env e2 in
      Circuit.shift ~side:lr ~sign:la e1 e2

    | ESat (us, `W size, e) -> begin
      let e = of_expr env e in
      match us with
      | `U -> Circuit.uextend ~size e
      | `S -> Circuit.sextend ~size e
      end

    | ESlice _ ->
      assert false

    | EConcat (_, es) ->
      List.flatten (List.map (of_expr env) es)

    | ERepeat (_, (e, n)) ->
      List.flatten (List.make n (of_expr env e))

    | EMap _ ->
      assert false

    | EApp _ ->
      assert false

    | ELet _ ->
      assert false

    | EVar _ ->
      assert false

    | ECast _ ->
      assert false

    | EInt _ ->
      assert false
  in

  of_expr () p.body
