(* ---------------------------------------------------------------- *)
open Deps
open Typing

(* WIP: Not capable of running the full example yet *)
(* and some things do not work/ have incorrect semantics *)
let rec bd_aexpr (e: aexpr) : deps =
  let { node = e_; type_ = t_; } = e in
  match e_ with 
  | ECast (e_, t_) -> bd_aexpr e_ (* fix semantic for non identity casts *)
  | EVar v -> (match t_ with 
    | `W n -> (copy ~offset:(0) ~size:(n) (Ident.name v)) 
    | _ -> (copy ~offset:0 ~size:256 (Ident.name v))) (* assuming integers have 256 bits *) 
  | EInt i -> empty ~size:(256) (* Need to know how to handle this case, probably good enough for now *)
  | ESlide (eb, (eo, cnt, sz)) -> (* verify indianess on this *)
      (match eo.node with
      | EInt i -> eb |> bd_aexpr |> offset ~offset:(-i) |> restrict ~min:(0) ~max:(cnt*sz)
      | _ -> 
        let n = (match eb.type_ with | `W n -> n | _ -> failwith "cant var slice int") 
        in let bdb = eb 
          |> bd_aexpr 
          |> chunk ~csize:(n) ~count:(1) 
        in let bdo = eo
          |> bd_aexpr 
          |> (let rec bitlen (m:int) = (match m with | 1 -> 1 | m -> 1 + bitlen (m/2)) in
          collapse ~csize:(bitlen n) ~count:(1)) |> Map.Int.find 0 |> constant ~size:(n) 
          (* Best guess without specific knowledge, result depends on ceil(log2(base_size)) bits of index *)
        in merge bdb bdo |> restrict ~min:0 ~max:(cnt*sz)) (* Need to check how to handle variable offsets *)
  | EMap ((`W n, `W m), (params, fb), args) -> 
      let bdfb = bd_aexpr fb in
      let bdargs = List.map bd_aexpr args in
      let subs = List.combine params bdargs in
      let k = (match fb.type_ with | `W k -> k | _ -> failwith "anon fun in map should ret word") in
      0 --^ m 
        |> Enum.map (fun i ->
          List.fold_left (fun d (v, t) -> propagate ~offset:(i*n) (v |> fst |> Ident.name) t d) bdfb subs 
          |> offset ~offset:(i*k))
        |> Enum.fold merge (empty ~size:0)
  | EConcat (`W n, args) -> 
      (match (List.hd args).type_ with
      | `W m -> aggregate ~csize:(m) (Enum.map bd_aexpr (List.enum args))
      | _ -> failwith "Cannot concat words (typing should catch this)")
  | ERepeat (`W n, (e, i)) -> (
      let rec doit (acc: deps list) (d: deps) (i: int) =
        match i with
        | 0 -> acc
        | _ -> doit (d::acc) d (i-1)
      in aggregate ~csize:(n/i) (List.enum (doit [] (bd_aexpr e) i)))
  | EShift (lr, la, eb, es) -> 
      let bd = bd_aexpr eb in
      (match (es.node, eb.type_) with
      | (EInt i, `W n) -> 
        let d = 
          (let i = (match lr with | `L -> i | `R -> -i) 
          in restrict ~min:(0) ~max:(n) (offset ~offset:(i) bd)) 
        in (match (lr, la) with
          | (`R, `A) -> Option.default (empty ~size:(0)) (Option.map (fun d1 -> constant ~size:(n) d1 |> restrict ~max:(n) ~min:(n-i)) (Map.Int.find_opt (n-1) bd)) |> merge d
          | _ -> d)
      | (_, `W n) -> 
          let (db, ds) = (bd_aexpr eb, bd_aexpr es) in
          merge (chunk ~csize:n ~count:1 db) (ds |> enlarge ~min:0 ~max:n |> chunk ~csize:n ~count:1)
      | _ -> failwith "Cant slice non-word")
  | ESat (su, e, n) -> (* first sat approximation: sat-length bits depend on everything *)
      (match e.type_ with
      | `W m -> 
        let d = bd_aexpr e in
        let hd = d 
          |> restrict ~min:n ~max:m 
          |> offset ~offset:(-n) 
          |> chunk ~csize:(m-n) ~count:1
          |> (fun d -> Option.default Map.String.empty (Map.Int.find_opt 0 d))
          |> constant ~size:m
        in merge d hd
      | _ -> failwith "Cannot saturate/clamp integers, convert to word first")
  | ELet ((v, e1), e2) -> 
      let bd1, bd2 = (bd_aexpr e1, bd_aexpr e2) in
      propagate ~offset:0 (Ident.name v) bd1 bd2
  | EAdd (c, `W n, (e1, e2)) -> (* add and sub assuming no overflow *)
      let (d1, d2) = (bd_aexpr e1, bd_aexpr e2) in
      1 --^ n |> Enum.fold (fun d i -> d 
        |> merge (offset ~offset:(i) d1) 
        |> merge (offset ~offset:(i) d2)) (merge d1 d2)
      |> (match c with | `C -> (fun a -> a) | `NC -> restrict ~min:(0) ~max:(n))
  | ESub (`W n, (e1, e2)) -> 
      let (d1, d2) = (bd_aexpr e1, bd_aexpr e2) in
      1 --^ n |> Enum.fold (fun d i -> d 
        |> merge (offset ~offset:(i) d1) 
        |> merge (offset ~offset:(i) d2)) (merge d1 d2)
      |> restrict ~min:(0) ~max:(n)
  | EOr  (`W n, (e1, e2)) -> merge (bd_aexpr e1) (bd_aexpr e2)
  | EAnd (`W n, (e1, e2)) -> merge (bd_aexpr e1) (bd_aexpr e2)
  | EMul (su, dhl, `W n, (e1, e2)) -> 
      let (d1, d2) = (bd_aexpr e1, bd_aexpr e2) in
      1 --^ (match dhl with |`D -> n | _ -> 2*n) |> Enum.fold (fun d i -> d 
        |> merge (offset ~offset:(i) d1) 
        |> merge (offset ~offset:(i) d2)) (merge d1 d2)
      |> (match dhl with 
      | `D -> restrict ~min:(0) ~max:(n) 
      | `H -> (fun d -> d |> restrict ~min:(n) ~max:(2*n) |> offset ~offset:(-n))
      | `L -> restrict ~min:(0) ~max:(n))

  (* propagate v deps to t deps in d *)
and propagate ~(offset:int) (v: symbol) (t: deps) (d: deps) : deps =
  Map.Int.map (fun d1 -> 
    match (Map.String.find_opt v d1) with
    | None -> d1
    | Some si -> si |> Set.Int.enum 
      |> Enum.fold (fun acc i -> merge1 acc (Option.default (Map.String.empty) (Map.Int.find_opt (i + offset) t))) (Map.String.remove v d1)) d

let bd_adef (df: adef) =
  bd_aexpr df.body
