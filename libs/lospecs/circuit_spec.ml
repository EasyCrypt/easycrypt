(* ==================================================================== *)
open Ast
open Aig
  
(* ==================================================================== *)
let load_from_file ~(filename : string) =
  let specs = File.with_file_in filename (Io.parse filename) in
  let specs = Typing.tt_program Typing.Env.empty specs in
  specs

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
let circuit_of_specification (rs : reg list) (p : adef) : reg =
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

    | ECmp (`W _, us, k, (e1, e2)) ->
      let e1 = of_expr env e1 in
      let e2 = of_expr env e2 in
      let c =
        match us, k with
        | `S, `Gt -> Circuit.sgt e1 e2
        | `S, `Ge -> Circuit.sge e1 e2
        | `U, `Gt -> Circuit.ugt e1 e2
        | `U, `Ge -> Circuit.uge e1 e2
      in [c]

    | ENot (_, e) ->
      Circuit.lnot_ (of_expr env e)

    | EOr (_, (e1, e2)) ->
      let e1 = of_expr env e1 in
      let e2 = of_expr env e2 in
      Circuit.lor_ e1 e2

    | EXor (_, (e1, e2)) ->
      let e1 = of_expr env e1 in
      let e2 = of_expr env e2 in
      Circuit.lxor_ e1 e2

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

    | EExtend (us, `W size, e) -> begin
      let e = of_expr env e in
      match us with
      | `U -> Circuit.uextend ~size e
      | `S -> Circuit.sextend ~size e
      end

    | EPopCount (size, e) ->
      Circuit.popcount ~size:(get_size size) (of_expr env e)

    | ESlice (e, ({ node = EInt offset }, size, scale)) ->
      let e = of_expr env e in
      let offset = offset * scale in
      let size = size * scale in
      List.take size (List.drop offset e)

    | ESlice (e, (offset, size, scale)) ->
      let lgscale = Circuit.log2 scale in
      assert (1 lsl lgscale = scale);

      let e = of_expr env e in
      let offset = of_expr env offset in

      let offset = List.make lgscale Aig.false_ @ offset in
      let size = size * scale in

      List.take size (Circuit.lsr_ e offset)

    | EAssign (e, ({ node = EInt offset }, size, scale), v) ->
      let e = of_expr env e in
      let v = of_expr env v in
      let offset = offset * scale in
      let size = size * scale in
      let pre, e = List.split_at offset e in
      let e, post = List.split_at size e in
      pre @ v @ post

    | EAssign (e, (offset, size, scale), v) ->
      let esz = atype_as_aword e.type_ in

      let lgscale = Circuit.log2 scale in
      assert (1 lsl lgscale = scale);

      let e = of_expr env e in
      let offset = of_expr env offset in
      let v = of_expr env v in

      let offset = List.make lgscale Aig.false_ @ offset in
      let size = size * scale in

      let m = List.make size Aig.true_ in
      let m = Circuit.uextend ~size:esz m in
      let m = Circuit.lnot_ (Circuit.lsl_ m offset) in

      let v = Circuit.uextend ~size:esz v in
      let v = Circuit.lsl_ v offset in

      Circuit.lor_ (Circuit.land_ e m) v

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

    | ECond (c, (e1, e2)) ->
      let c = of_expr env c in
      let e1 = of_expr env e1 in
      let e2 = of_expr env e2 in

      Circuit.mux2_reg e2 e1 (Circuit.ors c)

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
            (Ast.aexpr_to_yojson e);
          assert false
        end
      | _ -> ()
    end; r
  in

  let env =
    let bindings  = List.combine (List.map fst p.arguments) rs in
    Env.Var.bindall Env.empty bindings in

  of_expr env p.body
