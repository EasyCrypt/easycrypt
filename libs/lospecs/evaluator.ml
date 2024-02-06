open Ast

type bitword = Z.t * int 

let default_int_size = 256

let full_bitmask (n:int) : Z.t = 
  Z.((one lsl n) - one)

let from_int_list (lst: int list) (n: int) : bitword =
  (List.fold_left (fun acc x -> Z.((acc lsl n) + ((of_int x) land (full_bitmask n)))) Z.zero lst,
  n* (List.length lst))

let sbw_to_sbint ((bw, bn): bitword) : Z.t = 
  if (bw < Z.(one lsl (Int.sub bn 1))) then bw else Z.(bw - (one lsl bn))

(* change endianness *)
let bs_bw ((bw, bn): bitword) : bitword =
  assert (bn mod 8 == 0);
  let bw_list = List.fold_left_map (fun acc x -> (Z.(acc asr 8), Z.(acc land (full_bitmask 8)))) bw (List.init (bn / 8) (fun _ -> ())) |> snd in
  let bw_list = List.rev bw_list in
  (List.fold_left (fun acc x -> Z.(acc lsl 8 + x)) Z.zero bw_list, bn)

(* needs to be tested *)
let sbint_to_sbw (i: Z.t) (n: int) : bitword =
  if i >= Z.zero then (Z.(i land (full_bitmask (Int.sub n 1))), n)
  else (Z.(erem i (one lsl n)), n)

let from_int (i: int) (n:int) ~(signed: bool) =
  if signed then sbint_to_sbw (Z.of_int i) n else
  (Z.((of_int i) land (full_bitmask n)), n)

(* Currently only for 128 and 256 bit words *)
let from_bytes (bs: bytes) ~(lit_end: bool) =
  let n = Bytes.length bs in 
  let bs = Bytes.to_seq bs |> List.of_seq in
  begin
    assert ((n == 16) || (n == 32));
    let bs = if lit_end then List.rev bs else bs in
    (List.fold_left (fun acc x -> Z.((acc lsl 8) + (Char.code x |> of_int))) Z.zero bs, 8*n)
  end

let to_bytes ((bw, bn): bitword) ~(lit_end: bool) : bytes =
  assert ((bn mod 8) == 0);
  List.fold_left_map (fun acc x -> (Z.(acc asr 8), Z.((acc land (full_bitmask 8)) |> to_int |> Char.chr))) bw (0 --^ (bn/8) |> List.of_enum) |> snd |> String.of_list |> Bytes.of_string

(* assuming argument is signed *)
let usat ((bw, bn): bitword) (n: int) : bitword = 
  let k = sbw_to_sbint (bw, bn) in
  if (k < Z.(one lsl n)) then 
    if (k >= Z.zero) then (bw, n) else (Z.zero, n) 
  else (full_bitmask n, n)

let ssat ((bw, bn): bitword) (n: int) : bitword =
  let v = sbw_to_sbint (bw, bn) in
  if v >= Z.(one lsl (Int.sub n 1)) then (full_bitmask (n-1), n) else
  if v < Z.(- ( one lsl (Int.sub n 1))) then (Z.(one lsl (Int.sub n 1)), n)
  else ((if v >= Z.zero then v else Z.(v + (one lsl n))), n)

let bi_usat (z: Z.t) (n: int) : Z.t =
  if z < Z.zero then Z.zero else
  if z >= Z.(one lsl n) then full_bitmask n
  else z

let bi_ssat (z: Z.t) (n: int) : Z.t = 
  if z < Z.(-(one lsl (Int.sub n 1))) then Z.(-(one lsl (Int.sub n 1)))
  else if z >= Z.(one lsl (Int.sub n 1)) then full_bitmask (n-1)
  else z

let rec eval_aexpr (fctxt: (aargs * aexpr) IdentMap.t) (ctxt: bitword IdentMap.t) (e: aexpr) : bitword =
  let { node = e_; type_ = t_; } = e in
  match e_ with 
  | EVar v -> (match t_ with 
    | `W n -> (match IdentMap.find_opt v ctxt with
      | Some bw -> bw
      | None -> failwith ("Variable " ^ (Ident.name v) ^ " not in evaluation context"))
    | _ -> failwith "vars shouldn't be integers?") (* assuming integers have 256 bits *) 


  | EInt i -> (match t_ with
    | `W n -> (Z.((of_int i) land (full_bitmask n)), n)
    | _ -> (Z.of_int i, default_int_size) )
  (* Need to know how to handle this case, probably good enough for now *)

  | ESlice (eb, (es, len, scale)) -> (* verify indianess on this & check new syntax *)
      let bw = eval_aexpr fctxt ctxt eb in
      let sz = len*scale in
      let sa = (match es.node with
      | EInt sa -> sa
      | _       -> eval_aexpr fctxt ctxt es |> fst |> Z.to_int) * scale
      in begin 
        assert (sa + sz <= snd bw);
        (Z.(((fst bw) asr sa) land ((one lsl (sz)) - one)), sz)
      end

  (* FIXME: Make sure map is correct, maybe refactor *)
  | EMap ((`W n, `W m), (params, fb), args) -> 
      let bwargs = List.map (eval_aexpr fctxt ctxt) args in
      let bwargs = begin 
        assert (List.fold_left (&&) true (List.map (fun x -> snd x == n*m) bwargs));
        List.map fst bwargs
      end in
      let subs = List.combine (List.map fst params) bwargs in
(*      let k = (match fb.type_ with | `W k -> k | _ -> failwith "anon fun in map should ret word") in *)
      let (res, n_) = 0 --^ m 
        |> Enum.map (fun i -> 
          let map_ctxt = List.fold_left (fun acc x -> IdentMap.add (fst x) (Z.((snd x asr (Int.mul i n)) land (full_bitmask n)), n) acc) ctxt subs
          in let (res, n_) = eval_aexpr fctxt (map_ctxt) fb 
          in begin
            assert (Z.(res < (one lsl n_)));
            (Z.(res lsl (Int.mul i n_)), n_)
          end
        ) |> Enum.fold 
            (fun (bw, n_) (acc_bw, acc_n) -> 
              (Z.(bw lor acc_bw), 
               (if acc_n == -1 
                then n_ 
                else (acc_n)))) (* assert(acc_n == n_); *)
        (Z.zero, -1)
      in (res, n_*m)

  | EConcat (`W n, args) -> 
    let args = List.map (eval_aexpr fctxt ctxt) args in
    let args = List.rev args in (* change order *)
    begin 
      assert (List.map snd args |> List.fold_left (+) 0 == n);
      (List.fold_left (fun acc (bw, bn) -> Z.((acc lsl bn) + bw)) (Z.of_int 0) args, n)
    end

  | ERepeat (`W n, (e, i)) -> 
    let (bw, bn) = eval_aexpr fctxt ctxt e in
    begin
      assert (bn*i == n);
      let v = (0 --^ i |> Enum.fold (fun acc x -> 
      Z.((acc lsl (bn)) + bw)) (Z.of_int 0))
      in (v, n)
    end

  (* might need refactoring *)
  | EShift (lr, la, (eb, es)) -> 
      let (bb, sz) = eval_aexpr fctxt ctxt eb in
      let bs = eval_aexpr fctxt ctxt es |> fst |> Z.to_int in
      ((match (lr, la) with
      | (`L,  _) -> Z.((bb lsl bs) land (full_bitmask sz))
      | (`R, `L) -> Z.(bb asr bs)
      | (`R, `A) -> Z.(bb asr bs +
                    (if bb land (one lsl (Int.sub sz 1)) <> zero
                    then (one lsl sz) - (one lsl (Int.max (Int.sub sz bs) 0))
                    else zero
                    ))
      ), sz)

  | EExtend (us, `W n, e) ->
    (match us with
    | `U -> 
      let bw = eval_aexpr fctxt ctxt e in
      (fst bw, n)
    | `S -> 
      let bw = eval_aexpr fctxt ctxt e in
      if Z.((fst bw) < (one lsl (Int.sub (snd bw) 1)))
      then ((fst bw), n)
      else (Z.((fst bw) - (one lsl (snd bw)) + (one lsl (n))), n)
    )



  | ESat (us, `W n, e) -> 
    let bw = eval_aexpr fctxt ctxt e in
    (match us with
     | `U -> usat bw n 
     | `S -> ssat bw n)
 
  | EApp (f, es) -> 
    (match IdentMap.find_opt f fctxt with
      | None -> failwith (String.concat " " [(Ident.name f); "function binding not found"])
      | Some (args, fe) -> 
        let () = assert (List.compare_lengths args es == 0) in
        let subs = List.combine 
                  (List.map (fun arg -> arg |> fst) args) 
                  (List.map (eval_aexpr fctxt ctxt) es  ) in
        eval_aexpr fctxt (List.fold_left (fun m (a, v) -> IdentMap.add a v m) ctxt subs) fe
    )

  | ELet ((v, args, e1), e2) -> (* expand this *)
      (match args with
        | None | Some [] ->
            let bw1 = eval_aexpr fctxt ctxt e1 in
            eval_aexpr fctxt (IdentMap.add v bw1 ctxt) e2
        | Some args -> 
            eval_aexpr (IdentMap.add v (args, e1) fctxt) ctxt e2
      )


  (* using C style semantics for conditionals *)
  | ECond (ec, (ect, ecf)) ->
      let bd, bdt, bdf = (eval_aexpr fctxt ctxt ec, eval_aexpr fctxt ctxt ect, eval_aexpr fctxt ctxt ecf) in
      if Z.((fst bd) <> zero) then bdt else bdf


  | ENot (`W n, e) ->
      let bw = eval_aexpr fctxt ctxt e in
      begin 
        assert (snd bw == n);
        (Z.((fst bw) lxor (full_bitmask n)), snd bw)
      end


  | EIncr (`W n, e) -> (* semantics = e + 1 *)
    let bw = eval_aexpr fctxt ctxt e in
    begin
      assert (n == snd bw);
      (Z.(((fst bw) + one) land (full_bitmask n)), n)
    end

    (* TEST THIS *)
  | EAdd (`W n, us, (e1, e2)) -> 
    let bw1 = eval_aexpr fctxt ctxt e1 in
    let bw2 = eval_aexpr fctxt ctxt e2 in
    let () = (assert (snd bw1 == snd bw2 && snd bw1 == n)) in
    let res = Z.( (sbw_to_sbint bw1) + (sbw_to_sbint bw2)) in
    (match us with
    | `Word   -> (Z.(res land (full_bitmask n)), n) (* FIXME: Fix sat add *)
    | `Sat `U -> sbint_to_sbw (bi_usat res n) n
    | `Sat `S -> sbint_to_sbw (bi_ssat res n) n) (* check this *)
 
  | ESub (`W n, (e1, e2)) -> 
      let b1 = eval_aexpr fctxt ctxt e1 in
      let b2 = eval_aexpr fctxt ctxt e2 in
      begin
        assert (snd b1 == snd b2);
        assert (snd b1 == n);
        let res = Z.((fst b1) - (fst b2)) in
        if Z.(res < zero) then 
        (Z.(res + (one lsl n)), n)
        else (res, n)
      end

  | EOr  (`W n, (e1, e2)) -> 
    let b1 = eval_aexpr fctxt ctxt e1 in
    let b2 = eval_aexpr fctxt ctxt e2 in
    begin
      assert (snd b1 == snd b2);
      assert (snd b1 == n);
      (Z.((fst b1) lor (fst b2)), n)
    end

  | EAnd (`W n, (e1, e2)) -> 
    let b1 = eval_aexpr fctxt ctxt e1 in
    let b2 = eval_aexpr fctxt ctxt e2 in
    begin
      assert (snd b1 == snd b2);
      assert (snd b1 == n);
      (Z.((fst b1) land (fst b2)), n)
    end


  (* need to check semantics later *)
  | EMul (mulk, `W n, (e1, e2)) -> (* recheck n bounds for consistency *)
      let bw1 = eval_aexpr fctxt ctxt e1 in
      let bw2 = eval_aexpr fctxt ctxt e2 in
      begin
        assert (snd bw1 == n); 
        assert (snd bw1 == snd bw2);
        (match mulk with 
        | `US -> let sbw2 = if (fst bw2) < Z.(one lsl (Int.sub n 1)) then (fst bw2) else Z.((fst bw2) - (one lsl n)) in
                 let res = Z.((fst bw1) * sbw2) in
                 (Z.( (if res < zero then res + (one lsl (Int.mul 2 n)) else res) land (full_bitmask (Int.mul 2 n ))), 2*n)
        | `U hld -> let res = Z.((fst bw1) * (fst bw2)) in 
        (match hld with
          | `H -> (Z.((res asr n) land (full_bitmask n)), n)
          | `L -> (Z.( res land (full_bitmask n)), n)
          | `D -> (Z.( res land (full_bitmask (Int.mul 2 n))), 2*n))
        | `S hld -> 
          let sbw1 = if (fst bw1) < Z.(one lsl (Int.sub n 1)) then (fst bw1) else Z.((fst bw1) - (one lsl n)) in
          let sbw2 = if (fst bw2) < Z.(one lsl (Int.sub n 1)) then (fst bw2) else Z.((fst bw2) - (one lsl n)) in
          let res = Z.(sbw1 * sbw2) in
          let res = (if Z.(res < zero) then Z.(erem res (one lsl (Int.mul n 2))) else res) in
          (match hld with
          | `H -> (Z.((res asr n) land (full_bitmask n)), n)
          | `L -> (Z.( res land (full_bitmask n)), n)
          | `D -> (Z.( res land (full_bitmask (Int.mul 2 n))), 2*n))
        )
      end


 
  | ECmp (`W n, us, gte, (e1, e2)) -> (* check this *)
    let bw1 = eval_aexpr fctxt ctxt e1 in
    let bw2 = eval_aexpr fctxt ctxt e2 in
    let (b1, b2) = (match us with
    | `U -> (fst bw1, fst bw2)
    | `S -> ((if Z.((fst bw1) < (one lsl (Int.sub n 1))) then (fst bw1) else Z.((fst bw1) - (one lsl n))),
             (if Z.((fst bw2) < (one lsl (Int.sub n 1))) then (fst bw2) else Z.((fst bw2) - (one lsl n)))))
    in ((match gte with
    | `Gt -> if b1 >  b2 then Z.one else Z.zero
    | `Ge -> if b1 >= b2 then Z.one else Z.zero
    ), n)


  (* eventually maybe extend this to len > 1 ? *)
  | EAssign (eb, (eo, len, scale), er) -> 
    let () = assert (len == 1) in
    let (wb, nb) = eval_aexpr fctxt ctxt eb in
    let (wo, no) = eval_aexpr fctxt ctxt eo in
    let (wr, nr) = eval_aexpr fctxt ctxt er in
(*    let k = (match eb.type_ with | `W n -> n | _ -> failwith "Cant slice assign an int") in *)
    let mask = Z.((full_bitmask nr) lsl (Int.mul (to_int wo) scale)) in
    let arr_mask = Z.((full_bitmask nb) lxor mask) in
    (Z.((wb land arr_mask) lor ((wr lsl (Int.mul (to_int wo) scale)) land mask)), nb)


(*
  (* propagate v deps to t deps in d *)
and propagate ~(offset:int) (v: ident) (t: deps) (d: deps) : deps =
  Map.Int.map (fun d1 -> 
    match (IdentMap.find_opt v d1) with
    | None -> d1
    | Some si -> si |> Set.Int.enum 
      |> Enum.fold (fun acc i -> merge1 acc (Option.default (IdentMap.empty) (Map.Int.find_opt (i + offset) t))) (IdentMap.remove v d1)) d
*)

let eval_adef (df: adef) (args: bitword list) : bitword =
  assert (List.compare_lengths df.arguments args == 0);
  assert (List.fold (&&) true (List.map (fun ((_, bsz), (_, `W n)) -> bsz == n) (List.combine args df.arguments)));
  eval_aexpr (IdentMap.empty) (List.combine (List.map fst df.arguments) args |> List.enum |> IdentMap.of_enum) df.body
