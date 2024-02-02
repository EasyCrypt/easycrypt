(* ---------------------------------------------------------------- *)
open Deps
open Ast

let rec log2 n =
  if n <= 1 then 0 else 1 + log2 (n asr 1)

(* WIP: Not capable of running the full example yet *)
(* and some things do not work/ have incorrect semantics *)
let rec bd_aexpr (ctxt: (aargs * deps) IdentMap.t) (e: aexpr) : deps =
  let { node = e_; type_ = t_; } = e in
  match e_ with 
  | EVar v -> (match t_ with 
    | `W n -> copy ~offset:(0) ~size:(n) v 
    | _ -> copy ~offset:0 ~size:256 v) (* assuming integers have 256 bits *) 

  | EInt i -> empty ~size:(256) (* Need to know how to handle this case, probably good enough for now *)

  | ESlice (eb, (es, len, scale)) -> (* verify indianess on this & check new syntax *)
      (match es.node with
      | EInt i -> eb |> (bd_aexpr ctxt) |> offset ~offset:(-i*scale) |> restrict ~min:(0) ~max:(len*scale)
      | _ -> 
        let n = (match eb.type_ with | `W n -> n | _ -> failwith "cant var slice int") 
        in let bdb_ = bd_aexpr ctxt eb
        in let bdb = 
          0 --^ n / scale 
          |> Enum.fold (fun d i -> offset bdb_ ~offset:(-i*scale) |> merge d) bdb_
          |> restrict ~min:(0) ~max:(len*scale)
        in let bdo = es
          |> (bd_aexpr ctxt) (* |> (fun d -> if Map.Int.is_empty d then empty ~size:(1) else d) *)
          |> collapse ~csize:(log2 n + 1) ~count:(1) 
          |> (fun d -> Map.Int.find_opt 0 d 
          |> Option.default IdentMap.empty) 
          |> constant ~size:(n) 
          (* Best guess without specific knowledge, result depends on ceil(log2(base_size)) bits of index *)
        in merge bdb bdo |> restrict ~min:0 ~max:(len*scale)) (* Need to check how to handle variable offsets *)

  | EMap ((`W n, `W m), (params, fb), args) -> 
      let bdfb = (bd_aexpr ctxt) fb in
      let bdargs = List.map (bd_aexpr ctxt) args in
      let subs = List.combine params bdargs in
      let k = (match fb.type_ with | `W k -> k | _ -> failwith "anon fun in map should ret word") in
      0 --^ m 
        |> Enum.map (fun i ->
          List.fold_left (fun d (v, t) -> propagate ~offset:(i*n) (v |> fst) t d) bdfb subs 
          |> offset ~offset:(i*k))
        |> Enum.fold merge (empty ~size:0)

  | EConcat (`W n, args) -> 
      (match (List.hd args).type_ with
      | `W m -> aggregate ~csize:(m) (Enum.map (bd_aexpr ctxt) (List.enum args))
      | _ -> failwith "Cannot concat words (typing should catch this)")

  | ERepeat (`W n, (e, i)) ->
      (*let rec doit (acc: deps list) (d: deps) (i: int) =
        match i with
        | 0 -> acc
        | _ -> doit (d::acc) d (i-1)
      in aggregate ~csize:(n/i) (List.enum (doit [] ((bd_aexpr ctxt) e) i))) *)
      let bd = bd_aexpr ctxt e 
      in aggregate ~csize:(n/i) (List.init i (fun _ -> bd) |> List.enum)

  | EShift (lr, la, (eb, es)) -> 
      let bd = (bd_aexpr ctxt) eb in
      (match (es.node, eb.type_) with
      | (EInt i, `W n) -> 
        let d = 
          (let i = (match lr with | `L -> i | `R -> -i) 
          in restrict ~min:(0) ~max:(n) (offset ~offset:(i) bd)) 
        in (match (lr, la) with
          | (`R, `A) -> Option.default (empty ~size:(0)) (Option.map (fun d1 -> constant ~size:(n) d1 |> restrict ~max:(n) ~min:(n-i)) (Map.Int.find_opt (n-1) bd)) |> merge d
          | _ -> d)
      | (_, `W n) -> 
          let (db, ds) = ((bd_aexpr ctxt) eb, (bd_aexpr ctxt) es) in
          merge (chunk ~csize:n ~count:1 db) (ds |> enlarge ~min:0 ~max:n |> chunk ~csize:n ~count:1)
      | _ -> failwith "Cant slice non-word")

  | EExtend (us, `W n, e) ->
      (match e.type_ with
      | `W m -> 
          (match us with
          | `U -> 
            let d = (bd_aexpr ctxt) e in
            enlarge ~min:0 ~max:n d
          | `S -> 
            let d = (bd_aexpr ctxt) e in
            constant ~size:(n-m) (Option.default IdentMap.empty (Map.Int.find_opt (m-1) d))
            |> offset ~offset:m
            |> merge (enlarge ~min:0 ~max:n d)
          )
      | _ -> failwith "Cannot extend integers, only words") (* check this *)

  | ESat (us, `W n, e) -> (* first sat approximation: sat-length bits depend on everything *)
      (match e.type_ with (* check this *)
      | `W m -> 
        let d = (bd_aexpr ctxt) e in
        let hd = d 
          |> restrict ~min:n ~max:m 
          |> offset ~offset:(-n) 
          |> chunk ~csize:(m-n) ~count:1
          |> (fun d -> Option.default IdentMap.empty (Map.Int.find_opt 0 d))
          |> constant ~size:n
        in restrict ~min:0 ~max:n d |> merge hd
      | _ -> failwith "Cannot saturate/clamp integers, convert to word first")

  | EApp (f, es) -> 
    (match IdentMap.find_opt f ctxt with
      | None -> failwith (String.concat " " [(Ident.name f); "function binding not found"])
      | Some (args, d) -> 
        let subs = List.combine 
                  (List.map (fun arg -> arg |> fst) args) 
                  (List.map (bd_aexpr ctxt) es) in
        List.fold_left (fun d sub -> propagate ~offset:0 (fst sub) (snd sub) d) d subs
    )

  | ELet ((v, args, e1), e2) -> (* expand this *)
      (match args with
        | None | Some [] ->
          let bd1, bd2 = ((bd_aexpr ctxt) e1, (bd_aexpr ctxt) e2) in
          propagate ~offset:0 v bd1 bd2
        | Some args -> 
          bd_aexpr (IdentMap.add v (args, ((bd_aexpr ctxt) e1)) ctxt) e2
      )

  | ECond (ec, (ect, ecf)) ->
      let bd, bdt, bdf = ((bd_aexpr ctxt) ec, (bd_aexpr ctxt) ect, (bd_aexpr ctxt) ecf) in
      (match ect.type_ with
      | `W n -> chunk ~csize:n ~count:1 bd |> merge bdt |> merge bdf
      | _ -> failwith "Should return word"
      )

  | ENot (`W n, e) ->
      (bd_aexpr ctxt) e (* bits depend on bits in the same pos *)

  | EIncr (`W n, e) -> (* semantics = e + 1 *)
      let d = (bd_aexpr ctxt) e in
      1 --^ n |> Enum.fold (fun d_ i -> d_
        |> merge (offset ~offset:(i) d)) d
      |> restrict ~min:(0) ~max:(n) 

  | EAdd (`W n, us, (e1, e2)) -> (* add and sub assuming no overflow *)
      let (d1, d2) = ((bd_aexpr ctxt) e1, (bd_aexpr ctxt) e2) in
      (match us with
      | `Word -> 
        1 --^ n |> Enum.fold (fun d i -> d 
          |> merge (offset ~offset:(i) d1) 
          |> merge (offset ~offset:(i) d2)) (merge d1 d2)
        |> restrict ~min:(0) ~max:(n)
      | `Sat _ -> merge (chunk ~csize:(n) ~count:1 d1) (chunk ~csize:(n) ~count:1 d2)
      )

  | ESub (`W n, (e1, e2)) -> 
      let (d1, d2) = ((bd_aexpr ctxt) e1, (bd_aexpr ctxt) e2) in
      1 --^ n |> Enum.fold (fun d i -> d 
        |> merge (offset ~offset:(i) d1) 
        |> merge (offset ~offset:(i) d2)) (merge d1 d2)
      |> restrict ~min:(0) ~max:(n)

  | EOr  (`W n, (e1, e2)) -> merge ((bd_aexpr ctxt) e1) ((bd_aexpr ctxt) e2)

  | EAnd (`W n, (e1, e2)) -> merge ((bd_aexpr ctxt) e1) ((bd_aexpr ctxt) e2)

  (* check this, maybe sub for a worse bound *)
  | EMul (mulk, `W n, (e1, e2)) -> (* recheck n bounds for consistency *)
      let (d1, d2) = ((bd_aexpr ctxt) e1, (bd_aexpr ctxt) e2) in
      1 --^ (match mulk with | `U `D | `S `D | `US -> n | _ -> 2*n) |> Enum.fold (fun d i -> d 
        |> merge (offset ~offset:(i) d1) 
        |> merge (offset ~offset:(i) d2)) (merge d1 d2)
      |> (match mulk with 
      | `U `D | `S `D | `US -> restrict ~min:(0) ~max:(2*n) 
      | `U `H | `S `H       -> (fun d -> d |> restrict ~min:(n) ~max:(2*n) |> offset ~offset:(-n))
      | `U `L | `S `L       -> restrict ~min:(0) ~max:(n)
      )

  | ECmp (`W n, us, gte, (e1, e2)) -> (* check this *)
      let d = merge ((bd_aexpr ctxt) e1) ((bd_aexpr ctxt) e2) in
        d |> chunk ~csize:n ~count:1
          |> (fun d -> Option.default IdentMap.empty (Map.Int.find_opt 0 d))
          |> constant ~size:1
          (* Alternative for last two lines is |> restrict ~min:0 ~max:1 *)

  | EAssign (eb, (eo, len, scale), er) ->
      let () = assert (len == 1) in
      let bd = bd_aexpr ctxt eb in
      let od = bd_aexpr ctxt eo in
      let rd = bd_aexpr ctxt er in
      let k = (match eb.type_ with | `W n -> n | _ -> failwith "Cant slice assign an int") in
      1 --^ (k/scale) |> Enum.fold (fun d i -> 
        merge (offset ~offset:(scale*i) rd) d) rd
      |> merge rd |> merge bd |> merge (chunk ~csize:k ~count:1 od) 



  (* propagate v deps to t deps in d *)
and propagate ~(offset:int) (v: ident) (t: deps) (d: deps) : deps =
  Map.Int.map (fun d1 -> 
    match (IdentMap.find_opt v d1) with
    | None -> d1
    | Some si -> si |> Set.Int.enum 
      |> Enum.fold (fun acc i -> merge1 acc (Option.default (IdentMap.empty) (Map.Int.find_opt (i + offset) t))) (IdentMap.remove v d1)) d

let bd_adef (df: adef) =
  bd_aexpr IdentMap.empty df.body 
