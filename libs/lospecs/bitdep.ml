(* ---------------------------------------------------------------- *)
open Deps
open Typing

let rec bd_aexpr (e: aexpr) : deps =
  let { node = e_; type_ = t_; } = e in
  match e_ with 
  | ECast (e_, t_) -> bd_aexpr e_ (* fix semantic for non identity casts *)
  | EVar v -> (match t_ with | `W n -> (copy ~offset:(0) ~size:(n) (Ident.name v)) | _ -> failwith "Vars should be words") 
  | EInt i -> empty ~size:(256) (* Need to know how to handle this case, probably good enough for now *)
  | ESlide (eb, (eo, cnt, sz)) -> 
      (match eo.node with
      | EInt i -> failwith "Need to implement fixed base slices"
      | _ -> bd_aexpr eb) (* Need to check how to handle variable offsets *)
  (* Map should gen deps for params in terms of fb and then chunk those and sub params for args *)
  (* temp sol is to just chunk full dep *)
  | EMap ((`W n, `W m), (params, fb), args) -> chunk ~csize:(n) ~count:(m) (bd_aexpr fb)
  | EConcat (`W n, args) -> 
      (match (List.hd args).type_ with
      | `W m -> aggregate ~csize:(m) (Enum.map bd_aexpr (List.enum (List.rev args)))
      | _ -> failwith "Cannot concat words (typing should catch this)")
  | ERepeat (`W n, (e, i)) -> (
      let rec doit (acc: deps list) (d: deps) (i: int) =
        match i with
        | 0 -> acc
        | _ -> doit (d::acc) d (i-1)
      in aggregate ~csize:(n/i) (List.enum (doit [] (bd_aexpr e) i)))
  | EShift (lr, la, eb, es) -> (* need to add arith right sign bit dependency *)
      let bd = bd_aexpr eb in
      (match (es.node, eb.type_) with
      | (EInt i, `W n) -> 
        let d = 
          (let i = (match lr with | `L -> i | `R -> -i) 
          in restrict ~min:(0) ~max:(n) (offset ~offset:(i) bd)) 
        in (match (lr, la) with
          | (`R, `A) -> Option.default (empty ~size:(0)) (Option.map (fun d1 -> constant ~size:(n) d1 |> restrict ~max:(n) ~min:(n-i)) (Map.Int.find_opt (n-1) bd)) |> merge d
          | _ -> d)
      | _ -> failwith "Variable shifts not implemented yet")
  | EAdd (c, `W n, (e1, e2)) -> 
      let (d1, d2) = (bd_aexpr e1, bd_aexpr e2) in
      1 --^ n |> Enum.fold (fun d i -> d 
        |> merge (offset ~offset:(i) d1) 
        |> merge (offset ~offset:(i) d2)) (merge d1 d2)
      |> (match c with | `C -> (fun a -> a) | `NC -> restrict ~min:(0) ~max:(n))
  | ESub (`W n, (e1, e2)) -> merge (bd_aexpr e1) (bd_aexpr e2) (* still not implemented, FIXTHIS *)
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
  | _ -> failwith "Not implemented yet"

let bd_adef (df: adef) =
  bd_aexpr df.body
