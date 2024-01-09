(* ==================================================================== *)
open Typing
open Aig

(* ==================================================================== *)
let rec log2 n =
  if n <= 1 then 0 else 1 + log2 (n asr 1)
  
(* ==================================================================== *)
module Env : sig
  type env

  val empty : env

  module Fun : sig
    val get : env -> ident -> aargs * aexpr

    val bind : env -> ident -> aargs * aexpr -> env
  end

  module Var : sig
    val get : env -> ident -> reg

    val bind : env -> ident -> reg -> env
    
    val bindall : env -> (ident * reg) list -> env
  end
end = struct
  type binding = Var of reg | Fun of aargs * aexpr

  type env = (ident, binding) Map.t

  let empty : env =
    Map.empty

  module Fun = struct
    let get (env : env) (x : ident) =
      match Map.find_opt x env with
      | Some (Fun (a, f)) -> (a, f)
      | _ -> raise Not_found

    let bind (env : env) (x : ident) ((a, f): aargs * aexpr) : env =
      Map.add x (Fun (a, f)) env
  end

  module Var = struct
    let get (env : env) (x : ident) =
      match Map.find_opt x env with
      | Some (Var r) -> r
      | _ -> raise Not_found

    let bind (env : env) (x : ident) (r: reg) : env =
      Map.add x (Var r) env

    let bindall (env : env) (xr : (ident * reg) list) : env =
      List.fold_left (fun env (x, r) -> bind env x r) env xr
  end
end

type env = Env.env

(* ==================================================================== *)
let circuit_of_spec (rs : reg list) (p : adef) : reg =
  assert (List.length rs = List.length p.arguments);
  assert (List.for_all2 (fun r (_, `W n) -> List.length r = n) rs p.arguments);

  let rec of_expr_ (env : env) (e : aexpr) : reg =
    match e.node with
    | EIncr (_, e) ->
      Circuit.incr_dropc (of_expr env e)

    | EAdd (_, c, (e1, e2)) -> begin
      let e1 = of_expr env e1 in
      let e2 = of_expr env e2 in
      match c with
      | `Word -> Circuit.add_dropc e1 e2
      | `Sat `S -> Circuit.ssadd e1 e2
      | `Sat `U -> Circuit.usadd e1 e2
      end

    | ESub (_, (e1, e2)) ->
      let e1 = of_expr env e1 in
      let e2 = of_expr env e2 in
      Circuit.sub_dropc e1 e2

    | EMul (k, _, (e1, e2)) -> begin
      let e1 = of_expr env e1 in
      let e2 = of_expr env e2 in

      match k with
      | `U `D -> Circuit.umul e1 e2
      | `U `H -> Circuit.umulh e1 e2
      | `U `L -> Circuit.umull e1 e2
      | `S `D -> Circuit.smul e1 e2
      | `S `H -> Circuit.smulh e1 e2
      | `S `L -> Circuit.umull e1 e2
      | `US   -> Circuit.usmul e1 e2
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
      | `U -> Circuit.sat ~signed:false ~size e
      | `S -> Circuit.sat ~signed:true ~size e
      end

    | ESlice (e, ({ node = EInt offset }, size, scale)) ->
      let e = of_expr env e in
      let offset = offset * scale in
      let size = size * scale in
      List.take size (List.drop offset e)

    | ESlice (e, (offset, size, scale)) ->
      let lgscale = log2 scale in
      assert (1 lsl lgscale = scale);

      let e = of_expr env e in
      let offset = of_expr env offset in

      let offset = List.make lgscale Aig.false_ @ offset in
      let size = size * scale in

      List.take size (Circuit.lsr_ e offset)

    | EConcat (_, es) ->
      List.flatten (List.map (of_expr env) es)

    | ERepeat (_, (e, n)) ->
      List.flatten (List.make n (of_expr env e))

    | EMap ((`W n, _), (a, f), es) ->
      let anames = List.map fst a in
      let es = List.map (of_expr env) es in
      let es = List.map (Circuit.explode ~size:n) es in
      let es = List.transpose es in

      let es = es |> List.map (fun es ->
          let env = Env.Var.bindall env (List.combine anames es) in
          of_expr env f
        )

      in List.flatten es

    | EApp (f, args) ->
      let a, f = Env.Fun.get env f in
      let anames = List.map fst a in
      let args = List.map (of_expr env) args in
      let env = Env.Var.bindall env (List.combine anames args) in
      of_expr env f

    | ELet ((x, None, v), e) ->
      let v = of_expr env v in
      of_expr (Env.Var.bind env x v) e

    | ELet ((x, Some a, v), e) ->
      let env = Env.Fun.bind env x (a, v) in
      of_expr env e

    | EVar x ->
      Env.Var.get env x

    | EInt i -> begin
      match e.type_ with
      | `W n -> Circuit.of_int ~size:n i
      | _ -> assert false
    end

  and of_expr (env : env) (e : aexpr) : reg =
    let r = of_expr_ env e in

    begin
      match e.type_ with
      | `W n ->
        if List.length r <> n then begin
          Format.eprintf "%d %d@." (List.length r) n;
          Format.eprintf "%a@."
            (Yojson.Safe.pretty_print ~std:true)
            (Typing.aexpr_to_yojson e);
          assert false
        end
      | _ -> ()
    end; r
  in

  let env =
    let bindings  = List.combine (List.map fst p.arguments) rs in
    Env.Var.bindall Env.empty bindings in

  of_expr env p.body
