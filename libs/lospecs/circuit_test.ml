(* -------------------------------------------------------------------- *)
open Lospecs

(* -------------------------------------------------------------------- *)
module C = struct
  include Lospecs.Aig
  include Lospecs.Circuit
  include Lospecs.Circuit_avx2.FromSpec ()
end
(* -------------------------------------------------------------------- *)
let as_seq1 (type t) (xs : t list) =
  match xs with [x] -> x | _ -> assert false

(* -------------------------------------------------------------------- *)
let as_seq2 (type t) (xs : t list) =
  match xs with [x; y] -> (x, y) | _ -> assert false

(* -------------------------------------------------------------------- *)
let pp_bytes (fmt : Format.formatter) (b : bytes) =
  Bytes.iter
    (fun b -> Format.fprintf fmt "%02x" (Char.code b))
    b

(* -------------------------------------------------------------------- *)
let srange_ (i : int) =
  assert (0 < i && i <= Sys.int_size);
  let v = (1 lsl (i - 1)) in
  (-v, v-1)

(* -------------------------------------------------------------------- *)
let srange (i : int) =
  let vm, vM = srange_ i in Iter.(--) vm vM

(* -------------------------------------------------------------------- *)
let urange_ (i : int) =
  assert (0 < i && i <= Sys.int_size - 1);
  (0, (1 lsl i) - 1)

(* -------------------------------------------------------------------- *)
let urange (i : int) =
  let vm, vM = urange_ i in Iter.(--) vm vM

(* -------------------------------------------------------------------- *)
let product (type t) (s : t Iter.t list) =
  let rec doit (s : t Iter.t list) : t list Iter.t =
    match s with
    | [] ->
      Iter.of_list [[]]
    | s1 :: s ->
      Iter.map (fun (x, xs) -> x :: xs) (Iter.product s1 (doit s))
  in doit s

(* -------------------------------------------------------------------- *)
type op = {
  name  : string;
  args  : (int * [`U | `S]) list;
  out   : [`U | `S];
  mk    : C.reg list -> C.reg;
  reff  : int list -> int;
}

(* -------------------------------------------------------------------- *)
let bar (name : string) (total : int) =
  let open Progress.Line in
  list [
      spinner ~color:(Progress.Color.ansi `green) ()
    ; rpad (max 20 (String.length name)) (const name)
    ; bar total
    ; lpad (2 * 7 + 1) (count_to total)
  ]

(* -------------------------------------------------------------------- *)
let test (op : op) =
  let rs, vs =
    let reg_of_arg (name : int) ((sz, s) : int * [`U | `S]) =
      let r = C.reg ~size:sz ~name in
      let v = match s with `U -> urange sz | `S -> srange sz in
      (r, v)
    in List.split (List.mapi reg_of_arg op.args)
  in

  let sz = List.sum (List.map fst op.args) in

  assert (sz <= Sys.int_size - 1);

  let total = 1 lsl sz in
  let bar = bar op.name total in

  let circuit = op.mk rs in

  let test (vs : int list) =
    let vsa = Array.of_list vs in
    let env ((n, k) : C.var) = (vsa.(n) lsr k) land 0b1 <> 0 in
    let out = List.map (C.eval env) circuit in
    let out =
      match op.out with
      | `S -> C.sint_of_bools out
      | `U -> C.uint_of_bools out in
    let exp = op.reff vs in

    if out <> exp then begin
      Progress.interject_with (fun () ->
        Format.eprintf "%s(%a) = out: %d / exp: %d@."
          op.name
          (Format.pp_print_list
             ~pp_sep:(fun fmt () -> Format.pp_print_string fmt ", ")
             Format.pp_print_int)
          vs
          out
          exp
      );
      assert false
    end
  in

  Progress.with_reporter bar (fun f ->
    Iter.iter
      (fun vs -> test vs; f 1)
      (product vs)
  )

(* -------------------------------------------------------------------- *)
let test_uextend () =
  let op (isize : int) (osize : int) : op =
    { name = (Format.sprintf "uextend<%d,%d>" isize osize)
    ; args = [(isize, `U)]
    ; out  = `U
    ; mk   = (fun rs -> C.uextend ~size:osize (as_seq1 rs))
    ; reff = (fun vs -> as_seq1 vs)
    }

  in test (op 8 16)

(* -------------------------------------------------------------------- *)
let test_sextend () =
  let op (isize : int) (osize : int) : op =
    { name = (Format.sprintf "sextend<%d,%d>" isize osize)
    ; args = [(isize, `S)]
    ; out  = `S
    ; mk   = (fun rs -> C.sextend ~size:osize (as_seq1 rs))
    ; reff = (fun vs -> as_seq1 vs)
    }

  in test (op 8 16)

(* -------------------------------------------------------------------- *)
let test_shift ~(side : [`L | `R]) ~(sign : [`U | `S]) =
  let str_side = match side with `L -> "left" | `R -> "right" in
  let str_sign = match sign with `U -> "u" | `S -> "s" in

  let op (size : int) : op =
    let module M = (val Word.word ~sign ~size) in

    let sim (v : int) (i : int) =
      M.to_int (match side with
        | `L -> M.shiftl (M.of_int v) i
        | `R -> M.shiftr (M.of_int v) i
      )
    in

    let asign = match sign with `U -> `L | `S -> `A in

    { name = (Format.sprintf "shift<%s,%s,%d>" str_side str_sign size)
    ; args = [(size, sign); (4, `U)]
    ; out  = sign
    ; mk   = (fun rs -> let x, y = as_seq2 rs in C.shift ~side ~sign:asign x y)
    ; reff = (fun vs -> let x, y = as_seq2 vs in sim x y)
    }

  in

  test (op 8);
  test (op 14)

(* -------------------------------------------------------------------- *)
let test_opp () =
  let op (size : int) : op =
    let module M = (val Word.sword ~size) in

    let sim (x : int) : int =
      M.to_int (M.neg (M.of_int x)) in

    { name = (Format.sprintf "opp<%d>" size)
    ; args = [(size, `S)]
    ; out  = `S
    ; mk   = (fun rs -> C.opp (as_seq1 rs))
    ; reff = (fun vs -> sim (as_seq1 vs))
    }

  in test (op 13)

(* -------------------------------------------------------------------- *)
let test_add () =
  let op (size : int) : op =
    let module M = (val Word.sword ~size) in

    let sim (x : int) (y : int) : int =
      M.to_int (M.add (M.of_int x) (M.of_int y)) in

    { name = (Format.sprintf "add<%d>" size)
    ; args = List.make 2 (size, `S)
    ; out  = `S
    ; mk   = (fun rs -> let x, y = as_seq2 rs in C.add_dropc x y)
    ; reff = (fun vs -> let x, y = as_seq2 vs in sim x y)
    }

  in test (op 9)

(* -------------------------------------------------------------------- *)
let test_incr () =
  let op (size : int) : op =
    let module M = (val Word.uword ~size) in

    let sim (x : int) : int =
      M.to_int (M.add (M.of_int x) M.one) in

    { name = (Format.sprintf "incr<%d>" size)
    ; args = [(size, `U)]
    ; out  = `U
    ; mk   = (fun rs -> C.incr_dropc (as_seq1 rs))
    ; reff = (fun vs -> sim (as_seq1 vs));
  }

  in test (op 11)

(* -------------------------------------------------------------------- *)
let test_sub () =
  let op (size : int) : op =
    let module M = (val Word.sword ~size) in

    let sim (x : int) (y : int) : int =
      M.to_int (M.sub (M.of_int x) (M.of_int y)) in

    { name = (Format.sprintf "sub<%d>" size)
    ; args = List.make 2 (size, `S)
    ; out  = `S
    ; mk   = (fun rs -> let x, y = as_seq2 rs in C.sub_dropc x y)
    ; reff = (fun vs -> let x, y = as_seq2 vs in sim x y)
    }

  in test (op 9)

(* -------------------------------------------------------------------- *)
let test_umul () =
  let op (sz1 : int) (sz2 : int) : op = {
    name = (Format.sprintf "umul<%d,%d>" sz1 sz2);
    args = [(sz1, `U); (sz2, `U)];
    out  = `U;
    mk   = (fun rs -> let x, y = as_seq2 rs in C.umul x y);
    reff = (fun vs -> let x, y = as_seq2 vs in (x * y));
  } in

  test (op 10 8)

(* -------------------------------------------------------------------- *)
let test_smul () =
  let op (sz1 : int) (sz2 : int) : op = {
    name = (Format.sprintf "smul<%d,%d>" sz1 sz2);
    args = [(sz1, `S); (sz2, `S)];
    out  = `S;
    mk   = (fun rs -> let x, y = as_seq2 rs in C.smul x y);
    reff = (fun vs -> let x, y = as_seq2 vs in (x * y));
  } in

  test (op 10 8)

(* -------------------------------------------------------------------- *)
let test_smul_u8_s8 () =
  let op () : op = {
    name = "smul_u8_s8";
    args = [(8, `U); (8, `S)];
    out  = `S;
    mk   = (fun rs ->
              let x, y = as_seq2 rs in
              C.smul
                (C.uextend ~size:16 x)
                (C.sextend ~size:16 y));
    reff = (fun vs -> let x, y = as_seq2 vs in (x * y));
  } in

  test (op ())

  (* -------------------------------------------------------------------- *)
let test_ssat () =
  let op (isize : int) (osize: int) : op =
    let saturate =
      let vm, vM = srange_ osize in
      fun (i : int) -> min vM (max vm i)
    in

 {  name = (Format.sprintf "ssat<%d,%d>" isize osize);
    args = [(isize, `S)];
    out  = `S;
    mk   = (fun rs -> C.sat ~signed:true ~size:osize (as_seq1 rs));
    reff = (fun vs -> saturate (as_seq1 vs)); } in

  test (op 10 4);
  test (op 15 7);
  test (op 17 16)

(* -------------------------------------------------------------------- *)
let test_usat () =
  let op (isize : int) (osize: int) : op =
    let saturate =
      let vm, vM = urange_ osize in
      fun (i : int) -> min vM (max vm i)
    in

 {  name = (Format.sprintf "usat<%d,%d>" isize osize);
    args = [(isize, `S)];
    out  = `U;
    mk   = (fun rs -> C.sat ~signed:false ~size:osize (as_seq1 rs));
    reff = (fun vs -> saturate (as_seq1 vs)); } in

  test (op 10 4);
  test (op 15 7)

(* -------------------------------------------------------------------- *)
let test_sgt () =
  let op (size : int) =
    {  name = Format.sprintf "sgt<%d>" size;
        args = [(size, `S); (size, `S)];
        out  = `U;
        mk   = (fun rs -> let x, y = as_seq2 rs in [C.sgt x y]);
        reff = (fun vs -> let x, y = as_seq2 vs in if x > y then 1 else 0); }

  in
  test (op 10)

(* -------------------------------------------------------------------- *)
let test_sge () =
  let op (size : int) =
    {  name = Format.sprintf "sge<%d>" size;
        args = [(size, `S); (size, `S)];
        out  = `U;
        mk   = (fun rs -> let x, y = as_seq2 rs in [C.sge x y]);
        reff = (fun vs -> let x, y = as_seq2 vs in if x >= y then 1 else 0); }

  in
  test (op 10)

(* -------------------------------------------------------------------- *)
let test_ugt () =
  let op (size : int) =
    {  name = Format.sprintf "ugt<%d>" size;
        args = [(size, `U); (size, `U)];
        out  = `U;
        mk   = (fun rs -> let x, y = as_seq2 rs in [C.ugt x y]);
        reff = (fun vs -> let x, y = as_seq2 vs in if x > y then 1 else 0); }

  in
  test (op 10)

(* -------------------------------------------------------------------- *)
let test_uge () =
  let op (size : int) =
    {  name = Format.sprintf "uge<%d>" size;
        args = [(size, `U); (size, `U)];
        out  = `U;
        mk   = (fun rs -> let x, y = as_seq2 rs in [C.uge x y]);
        reff = (fun vs -> let x, y = as_seq2 vs in if x >= y then 1 else 0); }

  in
  test (op 10)

(* -------------------------------------------------------------------- *)
type mvalue = M256 of Avx2.m256 | M128 of Avx2.m128

module MValue : sig
  type kind = [`M256 | `M128]  

  val random : kind -> mvalue

  val to_bytes : endianess:Avx2.endianess -> mvalue -> bytes

  val of_bytes : endianess:Avx2.endianess -> bytes -> mvalue

  val pp :
    endianess:Avx2.endianess ->
    size:Avx2.size ->
    Format.formatter ->
    mvalue ->
    unit
end = struct
  type kind = [`M256 | `M128]  

  let random (k : kind) =
    match k with
    | `M256 -> M256 (Avx2.M256.random ())
    | `M128 -> M128 (Avx2.M128.random ())

  let to_bytes ~(endianess : Avx2.endianess) (m : mvalue) =
    match m with
    | M256 v -> Avx2.M256.to_bytes ~endianess:`Little v
    | M128 v -> Avx2.M128.to_bytes ~endianess:`Little v

  let of_bytes ~(endianess : Avx2.endianess) (m : bytes) =
    match Bytes.length m with
    | 32 -> M256 (Avx2.M256.of_bytes ~endianess m)
    | 16 -> M128 (Avx2.M128.of_bytes ~endianess m)
    | _  -> assert false

    let pp
    ~(endianess : Avx2.endianess)
    ~(size : Avx2.size)
    (fmt : Format.formatter)
    (m : mvalue)
  =
    match m with
    | M256 v -> Avx2.M256.pp ~endianess ~size fmt v
    | M128 v -> Avx2.M128.pp ~endianess ~size fmt v
end

(* -------------------------------------------------------------------- *)
type vpop = {
  name : string;
  args : MValue.kind list;
  mk : C.reg list -> C.reg;
  reff : mvalue list -> mvalue;
}

(* -------------------------------------------------------------------- *)
let call_m256_m256
  (f  : Avx2.m256 -> Avx2.m256)
  (vs : mvalue list)
  : mvalue
=
  match vs with
  | [M256 v] -> M256 (f v)
  | _ -> assert false

(* -------------------------------------------------------------------- *)
let call_m256_m128
  (f  : Avx2.m256 -> Avx2.m128)
  (vs : mvalue list)
  : mvalue
=
  match vs with
  | [M256 v] -> M128 (f v)
  | _ -> assert false

(* -------------------------------------------------------------------- *)
let call_m256_m128_m256
  (f  : Avx2.m256 -> Avx2.m128 -> Avx2.m256)
  (vs : mvalue list)
  : mvalue
=
  match vs with
  | [M256 v1; M128 v2] -> M256 (f v1 v2)
  | _ -> assert false

(* -------------------------------------------------------------------- *)
let call_m256x2_m256
  (f  : Avx2.m256 -> Avx2.m256 -> Avx2.m256)
  (vs : mvalue list)
  : mvalue
=
  match vs with
  | [M256 v1; M256 v2] -> M256 (f v1 v2)
  | _ -> assert false

(* -------------------------------------------------------------------- *)
let test_vp (total : int) (op : vpop) =
  let rs = op.args |> List.mapi (fun i arg ->
    match arg with
    | `M256 -> C.reg ~size:256 ~name:i
    | `M128 -> C.reg ~size:128 ~name:i
  ) in

  let circuit = op.mk rs in

  let test () =
    let vs = List.map MValue.random op.args in
    let avs = Array.of_list vs in
    let avs = Array.map (MValue.to_bytes ~endianess:`Little) avs in

    let env ((n, i) : C.var) = C.get_bit avs.(n) i in

    let o =
      match op.reff vs with
      | M256 v -> Avx2.M256.to_bytes ~endianess:`Little v
      | M128 v -> Avx2.M128.to_bytes ~endianess:`Little v
    in

    let o' = List.map (C.eval env) circuit in
    let o' = C.bytes_of_bools o' in

    if o <> o' then begin
      Progress.interject_with (fun () ->
        vs |> List.iter (fun v ->
          Format.eprintf "%a@."
          (MValue.pp ~endianess:`Big ~size:`U32)
          v
        );
        Format.eprintf "%a@."
          (MValue.pp ~endianess:`Big ~size:`U32)
          (MValue.of_bytes ~endianess:`Little o);
        Format.eprintf "%a@."
          (MValue.pp ~endianess:`Big ~size:`U32)
          (MValue.of_bytes ~endianess:`Little o')
      );
      assert false
    end
  in

  Progress.with_reporter (bar op.name total) (fun f ->
    Iter.iter
      (fun _ -> test (); f 1)
      (Iter.(--) 0 (total-1))
  )

(* -------------------------------------------------------------------- *)
let test_vpadd_16u16 () =
  let op = {
    name = "vpadd_16u16";
    args = List.make 2 `M256;
    mk = (fun rs -> let x, y = as_seq2 rs in C.vpadd_16u16 x y);
    reff = call_m256x2_m256 Avx2.mm256_add_epi16;
  } in

  test_vp 10000 op

(* -------------------------------------------------------------------- *)
let test_vpadd_32u8 () =
  let op = {
    name = "vpadd_32u8";
    args = List.make 2 `M256;
    mk = (fun rs -> let x, y = as_seq2 rs in C.vpadd_32u8 x y);
    reff = call_m256x2_m256 Avx2.mm256_add_epi8;
  } in

  test_vp 10000 op

(* -------------------------------------------------------------------- *)
let test_vpsub_16u16 () =
  let op = {
    name = "vpsub_16u16";
    args = List.make 2 `M256;
    mk = (fun rs -> let x, y = as_seq2 rs in C.vpsub_16u16 x y);
    reff = call_m256x2_m256 Avx2.mm256_sub_epi16;
  } in

  test_vp 10000 op

(* -------------------------------------------------------------------- *)
let test_vpsub_32u8 () =
  let op = {
    name = "vpsub_32u8";
    args = List.make 2 `M256;
    mk = (fun rs -> let x, y = as_seq2 rs in C.vpsub_32u8 x y);
    reff = call_m256x2_m256 Avx2.mm256_sub_epi8;
  } in

  test_vp 10000 op

(* -------------------------------------------------------------------- *)
let test_vpsra_16u16 () =
  let op (offset : int) = {
    name = Format.sprintf "vpsra_16u16<%d>" offset;
    args = [`M256];
    mk = (fun rs -> C.vpsra_16u16 (as_seq1 rs) offset);
    reff = call_m256_m256 (fun x -> Avx2.mm256_srai_epi16 x offset);
  } in

  Iter.iter (fun i -> test_vp 10000 (op i)) (Iter.(--) 0x00 0x10)

(* -------------------------------------------------------------------- *)
let test_vpsrl_16u16 () =
  let op (offset : int) = {
    name = Format.sprintf "vpsrl_16u16<%d>" offset;
    args = [`M256];
    mk = (fun rs -> C.vpsrl_16u16 (as_seq1 rs) offset);
    reff = call_m256_m256 (fun x -> Avx2.mm256_srli_epi16 x offset);
  } in

  Iter.iter (fun i -> test_vp 10000 (op i)) (Iter.(--) 0x00 0x10)

(* -------------------------------------------------------------------- *)
let test_vpand_256 () =
  let op = {
    name = "vpand_256";
    args = List.make 2 `M256;
    mk = (fun rs -> let x, y = as_seq2 rs in C.vpand_256 x y);
    reff = call_m256x2_m256 Avx2.mm256_and_si256;
  } in

  test_vp 10000 op

(* -------------------------------------------------------------------- *)
let test_vpmulh_16u16 () =
  let op = {
    name = "vpmulh_16u16";
    args = List.make 2 `M256;
    mk = (fun rs -> let x, y = as_seq2 rs in C.vpmulh_16u16 x y);
    reff = call_m256x2_m256 Avx2.mm256_mulhi_epu16;
  } in

  test_vp 200 op

(* -------------------------------------------------------------------- *)
let test_vpmulhrs_16u16 () =
  let op = {
    name = "vpmulhrs_16u16";
    args = List.make 2 `M256;
    mk = (fun rs -> let x, y = as_seq2 rs in C.vpmulhrs_16u16 x y);
    reff = call_m256x2_m256 Avx2.mm256_mulhrs_epi16;
  } in

  test_vp 200 op

(* -------------------------------------------------------------------- *)
let test_vpackus_16u16 () =
  let op = {
    name = "vpackus_16u16";
    args = List.make 2 `M256;
    mk = (fun rs -> let x, y = as_seq2 rs in C.vpackus_16u16 x y);
    reff = call_m256x2_m256 Avx2.mm256_packus_epi16;
  } in

  test_vp 10000 op

(* -------------------------------------------------------------------- *)
let test_vpackss_16u16 () =
  let op = {
    name = "vpackss_16u16";
    args = List.make 2 `M256;
    mk = (fun rs -> let x, y = as_seq2 rs in C.vpackss_16u16 x y);
    reff = call_m256x2_m256 Avx2.mm256_packs_epi16;
  } in

  test_vp 10000 op

(* -------------------------------------------------------------------- *)
let test_vpmaddubsw_256 () =
  let op = {
    name = "vpmaddubsw_256";
    args = List.make 2 `M256;
    mk = (fun rs -> let x, y = as_seq2 rs in C.vpmaddubsw_256 x y);
    reff = call_m256x2_m256 Avx2.mm256_maddubs_epi16;
  } in

  test_vp 200 op

(* -------------------------------------------------------------------- *)
let test_vpermd () =
  let op = {
    name = "vpermd";
    args = List.make 2 `M256;
    mk = (fun rs -> let x, y = as_seq2 rs in C.vpermd x y);
    reff = call_m256x2_m256 (fun x y -> Avx2.mm256_permutevar8x32_epi32 y x);
  } in

  test_vp 10000 op

(* -------------------------------------------------------------------- *)
let test_vpermq () =
  let op (imm8 : int) = {
    name = Format.sprintf "vpermq<%d>" imm8;
    args = [`M256];
    mk = (fun rs -> C.vpermq (as_seq1 rs) imm8);
    reff = call_m256_m256 (fun x -> Avx2.mm256_permute4x64_epi64 x imm8);
  } in

  test_vp 10000 (op 0x23);
  test_vp 10000 (op 0xf7)

(* -------------------------------------------------------------------- *)
let test_vbshufb_256 () =
  let op = {
    name = "vbshufb_256";
    args = List.make 2 `M256;
    mk = (fun rs -> let x, y = as_seq2 rs in C.vpshufb_256 x y);
    reff = call_m256x2_m256 Avx2.mm256_shuffle_epi8;
  } in

  test_vp 10000 op

(* -------------------------------------------------------------------- *)
let test_vpcmpgt_16u16 () =
  let op = {
    name = "vpcmpgt_16u16";
    args = List.make 2 `M256;
    mk = (fun rs -> let x, y = as_seq2 rs in C.vpcmpgt_16u16 x y);
    reff = call_m256x2_m256 Avx2.mm256_cmpgt_epi16;
  } in

  test_vp 10000 op

(* -------------------------------------------------------------------- *)
let test_vpmovmskb_u256u64 () =
  let op = {
    name = "vpmovmskb_u256u64";
    args = [`M256];
    mk = (fun rs -> C.uextend ~size:256 (C.vpmovmskb_u256u64 (as_seq1 rs)));
    reff = (fun vs ->
      match vs with
      | [M256 v] ->
        let out = Avx2.mm256_movemask_epi8 v in
        let out = Int64.logand (Int64.of_int32 out) 0xffffffffL in
        M256 (Avx2.M256.oftuple_64 (out, 0L, 0L, 0L))
      | _ ->
        assert false
    )
  } in

  test_vp 10000 op

(* -------------------------------------------------------------------- *)
let test_vpunpckl_32u8 () =
  let op = {
    name = "test_vpunpckl_32u8";
    args = List.make 2 `M256;
    mk = (fun rs -> let x, y = as_seq2 rs in C.vpunpckl_32u8 x y);
    reff = call_m256x2_m256 Avx2.mm256_unpacklo_epi8;
  } in

  test_vp 10000 op

(* -------------------------------------------------------------------- *)
let test_vpblend_16u16 () =
  let op (imm8 : int) = {
    name = Format.sprintf "test_vpblend_16u16<%d>" imm8;
    args = List.make 2 `M256;
    mk = (fun rs -> let x, y = as_seq2 rs in C.vpblend_16u16 x y imm8);
    reff = call_m256x2_m256 (fun x y -> Avx2.mm256_blend_epi16 x y imm8);
  } in
  
  test_vp 10000 (op 0x00);
  test_vp 10000 (op 0x3f);
  test_vp 10000 (op 0xaa)

(* -------------------------------------------------------------------- *)
let test_extracti128 () =
  let op (i : int) = {
    name = Format.sprintf "test_extracti128<%d>" i;
    args = [`M256];
    mk = (fun rs -> C.vpextracti128 (as_seq1 rs) i);
    reff = call_m256_m128 (fun x -> Avx2.mm256_extracti128_si256 x i);
  } in

  test_vp 10000 (op 0);
  test_vp 10000 (op 1)

(* -------------------------------------------------------------------- *)
let test_inserti128 () =
  let op (i : int) = {
    name = Format.sprintf "test_inserti128<%d>" i;
    args = [`M256; `M128];
    mk = (fun rs -> let x, y = as_seq2 rs in C.vpinserti128 x y i);
    reff = call_m256_m128_m256 (fun x y -> Avx2.mm256_inserti128_si256 x y i);
  } in

  test_vp 10000 (op 0);
  test_vp 10000 (op 1)


(* -------------------------------------------------------------------- *)
let shift () =
  let module CAvx2 = Circuit_avx2.FromSpec () in

  let i = 1 in

  let h = C.reg ~size:128 ~name:0 in
  let l = C.reg ~size:128 ~name:1 in

  let f ((v, i) : C.var) =
    match v with
    | 0 -> false
    | 1 -> true
    | _ -> assert false in

  let c1 =
    let hl = l @ h in
    let hli = CAvx2.vpsll_4u64 hl i in
    let hl64i = CAvx2.vpsrl_4u64 hl (64 - i) in
    let hl64il = CAvx2.vpslldq_256 hl64i 8 in
    let hli = Circuit.lxor_ hli hl64il in
    let l64ir = CAvx2.vpsrldq_128 (CAvx2.vpextracti128 hl64i 0) 8 in
    let h = CAvx2.vpextracti128 hli 1 in
    let h = Circuit.lxor_ h l64ir in
    let l = CAvx2.vpextracti128 hli 0 in

    l @ h in

  let c2 =
    Circuit.shift ~side:`L ~sign:`L (l @ h) (Circuit.w8 i) in

  let v1 = Aig.evals f c1 in
  let v2 = Aig.evals f c2 in

  let v1 = Avx2.M256.of_bytes ~endianess:`Little (Circuit.bytes_of_bools v1) in
  let v2 = Avx2.M256.of_bytes ~endianess:`Little (Circuit.bytes_of_bools v2) in

  Format.eprintf "%a@."
    (Avx2.M256.pp ~size:`U64 ~endianess:`Big)
    v1;
    Format.eprintf "%a@."
    (Avx2.M256.pp ~size:`U64 ~endianess:`Big)
    v2;

  Format.eprintf "%b@." (List.for_all2 (==) c1 c2)

  


(* -------------------------------------------------------------------- *)
let test_bvueq () =
  let op (size : int) : op =
    let module M = (val Word.sword ~size) in

    let sim (x : int) (y : int) : int =
      if x = y then 1 else 0
    in

    { name = (Format.sprintf "bvueq<%d>" size)
    ; args = List.make 2 (size, `U)
    ; out  = `U
    ; mk   = (fun rs -> let x, y = as_seq2 rs in [C.bvueq x y])
    ; reff = (fun vs -> let x, y = as_seq2 vs in sim x y)
    }

  in test (op 9)
  
(* -------------------------------------------------------------------- *)
let test_bvseq () =
  let op (size : int) : op =
    let module M = (val Word.sword ~size) in

    let sim (x : int) (y : int) : int =
      if x = y then 1 else 0
    in

    { name = (Format.sprintf "bvseq<%d>" size)
    ; args = List.make 2 (size, `S)
    ; out  = `U
    ; mk   = (fun rs -> let x, y = as_seq2 rs in [C.bvseq x y])
    ; reff = (fun vs -> let x, y = as_seq2 vs in sim x y)
    }

  in test (op 9)
  

(* -------------------------------------------------------------------- *)
let test_mod () =
  let op (size : int) : op =
    let module M = (val Word.sword ~size) in

    let sim (x : int) (y : int) : int =
      if y = 0 then x else
      x mod y
    in

    { name = (Format.sprintf "mod<%d>" size)
    ; args = List.make 2 (size, `U)
    ; out  = `U
    ; mk   = (fun rs -> let x, y = as_seq2 rs in C.urem x y)
    ; reff = (fun vs -> let x, y = as_seq2 vs in sim x y)
    }

  in test (op 9)

(* -------------------------------------------------------------------- *)
let test_smod () =
  let op (size : int) : op =
    let module M = (val Word.sword ~size) in

    let sim (x : int) (y : int) : int =
      if y = 0 then x else
      let u = x mod y in
      if u < 0 then y + u else u
    in

    { name = (Format.sprintf "smod<%d>" size)
    ; args = List.make 2 (size, `S)
    ; out  = `S
    ; mk   = (fun rs -> let x, y = as_seq2 rs in C.smod x y)
    ; reff = (fun vs -> let x, y = as_seq2 vs in sim x y)
    }

  in test (op 9)
  


(* -------------------------------------------------------------------- *)
let tests = [
  ("opp" , test_opp );
  ("incr", test_incr);
  ("add" , test_add );
  ("sub" , test_sub );
  ("umul", test_umul);
  ("smul", test_smul);
  ("ssat", test_ssat);
  ("usat", test_usat);

  ("sgt", test_sgt);
  ("sge", test_sge);

  ("ugt", test_ugt);
  ("uge", test_uge);

  ("lsl", (fun () -> test_shift ~side:`L ~sign:`U));
  ("lsr", (fun () -> test_shift ~side:`R ~sign:`U));

  ("asl", (fun () -> test_shift ~side:`L ~sign:`S));
  ("asr", (fun () -> test_shift ~side:`R ~sign:`S));

  ("smul_u8_s8", test_smul_u8_s8);

  ("uextend", test_uextend);
  ("sextend", test_sextend);

  ("smod", test_smod);
  ("mod", test_mod);

  ("bvueq", test_bvueq);
  ("bvseq", test_bvseq);

  ("vpadd_16u16"      , test_vpadd_16u16      );
  ("vpadd_32u8"       , test_vpadd_32u8       );
  ("vpsub_16u16"      , test_vpsub_16u16      );
  ("vpsub_32u8"       , test_vpsub_32u8       );
  ("vpsra_16u16"      , test_vpsra_16u16      );
  ("vpsrl_16u16"      , test_vpsrl_16u16      );
  ("vpand_256"        , test_vpand_256        );
  ("vpmulh_16u16"     , test_vpmulh_16u16     );
  ("vpmulhrs_16u16"   , test_vpmulhrs_16u16   );
  ("vpackus_16u16"    , test_vpackus_16u16    );
  ("vpackss_16u16"    , test_vpackss_16u16    );
  ("vpmaddubsw_256"   , test_vpmaddubsw_256   );
  ("vpermd"           , test_vpermd           );
  ("vpermq"           , test_vpermq           );
  ("vbshufb_256"      , test_vbshufb_256      );
  ("vpcmpgt_16u16"    , test_vpcmpgt_16u16    );
  ("vpmovmskb_u256u64", test_vpmovmskb_u256u64);
  ("vpunpckl_32u8"    , test_vpunpckl_32u8    );
  ("vpblend_16u16"    , test_vpblend_16u16    );
  ("vpextracti128"    , test_extracti128      );
  ("vpinserti128"     , test_inserti128       );
]

(* -------------------------------------------------------------------- *)
let main () =
  let tests =
    let n = Array.length Sys.argv in
    if n <= 1 then
      List.map snd tests
    else
      let names = Array.sub Sys.argv 1 (n - 1) in
      let names = Set.of_array names in
      let tests = List.filter (fun (x, _) -> Set.mem x names) tests in
      List.map snd tests in

  Random.self_init ();

  List.iter (fun f -> f ()) tests

(* ==================================================================== *)
module PolyCompress() = struct
  let pc_permidx_s =
    C.w256
      "0x00000000_00000004_00000001_00000005_00000002_00000006_00000003_00000007"

  let pc_shift2_s =
    C.w16 0x1001

  let pc_mask_s =
    C.w16 0x000f

  let pc_shift1_s =
    C.w16 0x0200

  let jvx16 =
    C.w256
      "0x4ebf4ebf_4ebf4ebf_4ebf4ebf_4ebf4ebf_4ebf4ebf_4ebf4ebf_4ebf4ebf_4ebf4ebf"

  let jqx16 =
    C.w256
      "0xd010d010_d010d010_d010d010_d010d010_d010d010_d010d010_d010d010_d010d01"

  let poly_compress
    (rp_0 : C.reg)
    (rp_1 : C.reg)
    (rp_2 : C.reg)
    (rp_3 : C.reg)
    (a_0  : C.reg)
    (a_1  : C.reg)
    (a_2  : C.reg)
    (a_3  : C.reg)
    (a_4  : C.reg)
    (a_5  : C.reg)
    (a_6  : C.reg)
    (a_7  : C.reg)
    (a_8  : C.reg)
    (a_9  : C.reg)
    (a_10 : C.reg)
    (a_11 : C.reg)
    (a_12 : C.reg)
    (a_13 : C.reg)
    (a_14 : C.reg)
    (a_15 : C.reg)
  : C.reg
  =
    let open C in

    let qx16 = jqx16 in
    let r = a_0 in
    let r_0 = vpsub_16u16 r qx16 in
    let t = vpsra_16u16 r_0 0x0f in
    let t_0 = vpand_256 t qx16 in
    let r_1 = vpadd_16u16 t_0 r_0 in
    let a_0_0 = r_1 in
    let r_2 = a_1 in
    let r_3 = vpsub_16u16 r_2 qx16 in
    let t_1 = vpsra_16u16 r_3 0x0f in
    let t_2 = vpand_256 t_1 qx16 in
    let r_4 = vpadd_16u16 t_2 r_3 in
    let a_1_0 = r_4 in
    let r_5 = a_2 in
    let r_6 = vpsub_16u16 r_5 qx16 in
    let t_3 = vpsra_16u16 r_6 0x0f in
    let t_4 = vpand_256 t_3 qx16 in
    let r_7 = vpadd_16u16 t_4 r_6 in
    let a_2_0 = r_7 in
    let r_8 = a_3 in
    let r_9 = vpsub_16u16 r_8 qx16 in
    let t_5 = vpsra_16u16 r_9 0x0f in
    let t_6 = vpand_256 t_5 qx16 in
    let r_10 = vpadd_16u16 t_6 r_9 in
    let a_3_0 = r_10 in
    let r_11 = a_4 in
    let r_12 = vpsub_16u16 r_11 qx16 in
    let t_7 = vpsra_16u16 r_12 0x0f in
    let t_8 = vpand_256 t_7 qx16 in
    let r_13 = vpadd_16u16 t_8 r_12 in
    let a_4_0 = r_13 in
    let r_14 = a_5 in
    let r_15 = vpsub_16u16 r_14 qx16 in
    let t_9 = vpsra_16u16 r_15 0x0f in
    let t_10 = vpand_256 t_9 qx16 in
    let r_16 = vpadd_16u16 t_10 r_15 in
    let a_5_0 = r_16 in
    let r_17 = a_6 in
    let r_18 = vpsub_16u16 r_17 qx16 in
    let t_11 = vpsra_16u16 r_18 0x0f in
    let t_12 = vpand_256 t_11 qx16 in
    let r_19 = vpadd_16u16 t_12 r_18 in
    let a_6_0 = r_19 in
    let r_20 = a_7 in
    let r_21 = vpsub_16u16 r_20 qx16 in
    let t_13 = vpsra_16u16 r_21 0x0f in
    let t_14 = vpand_256 t_13 qx16 in
    let r_22 = vpadd_16u16 t_14 r_21 in
    let a_7_0 = r_22 in
    let r_23 = a_8 in
    let r_24 = vpsub_16u16 r_23 qx16 in
    let t_15 = vpsra_16u16 r_24 0x0f in
    let t_16 = vpand_256 t_15 qx16 in
    let r_25 = vpadd_16u16 t_16 r_24 in
    let a_8_0 = r_25 in
    let r_26 = a_9 in
    let r_27 = vpsub_16u16 r_26 qx16 in
    let t_17 = vpsra_16u16 r_27 0x0f in
    let t_18 = vpand_256 t_17 qx16 in
    let r_28 = vpadd_16u16 t_18 r_27 in
    let a_9_0 = r_28 in
    let r_29 = a_10 in
    let r_30 = vpsub_16u16 r_29 qx16 in
    let t_19 = vpsra_16u16 r_30 0x0f in
    let t_20 = vpand_256 t_19 qx16 in
    let r_31 = vpadd_16u16 t_20 r_30 in
    let a_10_0 = r_31 in
    let r_32 = a_11 in
    let r_33 = vpsub_16u16 r_32 qx16 in
    let t_21 = vpsra_16u16 r_33 0x0f in
    let t_22 = vpand_256 t_21 qx16 in
    let r_34 = vpadd_16u16 t_22 r_33 in
    let a_11_0 = r_34 in
    let r_35 = a_12 in
    let r_36 = vpsub_16u16 r_35 qx16 in
    let t_23 = vpsra_16u16 r_36 0x0f in
    let t_24 = vpand_256 t_23 qx16 in
    let r_37 = vpadd_16u16 t_24 r_36 in
    let a_12_0 = r_37 in
    let r_38 = a_13 in
    let r_39 = vpsub_16u16 r_38 qx16 in
    let t_25 = vpsra_16u16 r_39 0x0f in
    let t_26 = vpand_256 t_25 qx16 in
    let r_40 = vpadd_16u16 t_26 r_39 in
    let a_13_0 = r_40 in
    let r_41 = a_14 in
    let r_42 = vpsub_16u16 r_41 qx16 in
    let t_27 = vpsra_16u16 r_42 0x0f in
    let t_28 = vpand_256 t_27 qx16 in
    let r_43 = vpadd_16u16 t_28 r_42 in
    let a_14_0 = r_43 in
    let r_44 = a_15 in
    let r_45 = vpsub_16u16 r_44 qx16 in
    let t_29 = vpsra_16u16 r_45 0x0f in
    let t_30 = vpand_256 t_29 qx16 in
    let r_46 = vpadd_16u16 t_30 r_45 in
    let a_15_0 = r_46 in
    let x16p = jvx16 in
    let v = x16p in
    let shift1 = vpbroadcast_16u16 pc_shift1_s in
    let mask = vpbroadcast_16u16 pc_mask_s in
    let shift2 = vpbroadcast_16u16 pc_shift2_s in
    let permidx = pc_permidx_s in
    let f0 = a_0_0 in
    let f1 = a_1_0 in
    let f2 = a_2_0 in
    let f3 = a_3_0 in
    let f0_0 = vpmulh_16u16 f0 v in
    let f1_0 = vpmulh_16u16 f1 v in
    let f2_0 = vpmulh_16u16 f2 v in
    let f3_0 = vpmulh_16u16 f3 v in
    let f0_1 = vpmulhrs_16u16 f0_0 shift1 in
    let f1_1 = vpmulhrs_16u16 f1_0 shift1 in
    let f2_1 = vpmulhrs_16u16 f2_0 shift1 in
    let f3_1 = vpmulhrs_16u16 f3_0 shift1 in
    let f0_2 = vpand_256 f0_1 mask in
    let f1_2 = vpand_256 f1_1 mask in
    let f2_2 = vpand_256 f2_1 mask in
    let f3_2 = vpand_256 f3_1 mask in
    let f0_3 = vpackus_16u16 f0_2 f1_2 in
    let f2_3 = vpackus_16u16 f2_2 f3_2 in
    let f0_4 = vpmaddubsw_256 f0_3 shift2 in
    let f2_4 = vpmaddubsw_256 f2_3 shift2 in
    let f0_5 = vpackus_16u16 f0_4 f2_4 in
    let f0_6 = vpermd permidx f0_5 in
    let rp_0_0 = f0_6 in
    let f0_7 = a_4_0 in
    let f1_3 = a_5_0 in
    let f2_5 = a_6_0 in
    let f3_3 = a_7_0 in
    let f0_8 = vpmulh_16u16 f0_7 v in
    let f1_4 = vpmulh_16u16 f1_3 v in
    let f2_6 = vpmulh_16u16 f2_5 v in
    let f3_4 = vpmulh_16u16 f3_3 v in
    let f0_9 = vpmulhrs_16u16 f0_8 shift1 in
    let f1_5 = vpmulhrs_16u16 f1_4 shift1 in
    let f2_7 = vpmulhrs_16u16 f2_6 shift1 in
    let f3_5 = vpmulhrs_16u16 f3_4 shift1 in
    let f0_10 = vpand_256 f0_9 mask in
    let f1_6 = vpand_256 f1_5 mask in
    let f2_8 = vpand_256 f2_7 mask in
    let f3_6 = vpand_256 f3_5 mask in
    let f0_11 = vpackus_16u16 f0_10 f1_6 in
    let f2_9 = vpackus_16u16 f2_8 f3_6 in
    let f0_12 = vpmaddubsw_256 f0_11 shift2 in
    let f2_10 = vpmaddubsw_256 f2_9 shift2 in
    let f0_13 = vpackus_16u16 f0_12 f2_10 in
    let f0_14 = vpermd permidx f0_13 in
    let rp_1_0 = f0_14 in
    let f0_15 = a_8_0 in
    let f1_7 = a_9_0 in
    let f2_11 = a_10_0 in
    let f3_7 = a_11_0 in
    let f0_16 = vpmulh_16u16 f0_15 v in
    let f1_8 = vpmulh_16u16 f1_7 v in
    let f2_12 = vpmulh_16u16 f2_11 v in
    let f3_8 = vpmulh_16u16 f3_7 v in
    let f0_17 = vpmulhrs_16u16 f0_16 shift1 in
    let f1_9 = vpmulhrs_16u16 f1_8 shift1 in
    let f2_13 = vpmulhrs_16u16 f2_12 shift1 in
    let f3_9 = vpmulhrs_16u16 f3_8 shift1 in
    let f0_18 = vpand_256 f0_17 mask in
    let f1_10 = vpand_256 f1_9 mask in
    let f2_14 = vpand_256 f2_13 mask in
    let f3_10 = vpand_256 f3_9 mask in
    let f0_19 = vpackus_16u16 f0_18 f1_10 in
    let f2_15 = vpackus_16u16 f2_14 f3_10 in
    let f0_20 = vpmaddubsw_256 f0_19 shift2 in
    let f2_16 = vpmaddubsw_256 f2_15 shift2 in
    let f0_21 = vpackus_16u16 f0_20 f2_16 in
    let f0_22 = vpermd permidx f0_21 in
    let rp_2_0 = f0_22 in
    let f0_23 = a_12_0 in
    let f1_11 = a_13_0 in
    let f2_17 = a_14_0 in
    let f3_11 = a_15_0 in
    let f0_24 = vpmulh_16u16 f0_23 v in
    let f1_12 = vpmulh_16u16 f1_11 v in
    let f2_18 = vpmulh_16u16 f2_17 v in
    let f3_12 = vpmulh_16u16 f3_11 v in
    let f0_25 = vpmulhrs_16u16 f0_24 shift1 in
    let f1_13 = vpmulhrs_16u16 f1_12 shift1 in
    let f2_19 = vpmulhrs_16u16 f2_18 shift1 in
    let f3_13 = vpmulhrs_16u16 f3_12 shift1 in
    let f0_26 = vpand_256 f0_25 mask in
    let f1_14 = vpand_256 f1_13 mask in
    let f2_20 = vpand_256 f2_19 mask in
    let f3_14 = vpand_256 f3_13 mask in
    let f0_27 = vpackus_16u16 f0_26 f1_14 in
    let f2_21 = vpackus_16u16 f2_20 f3_14 in
    let f0_28 = vpmaddubsw_256 f0_27 shift2 in
    let f2_22 = vpmaddubsw_256 f2_21 shift2 in
    let f0_29 = vpackus_16u16 f0_28 f2_22 in
    let f0_30 = vpermd permidx f0_29 in
    let rp_3_0 = f0_30 in

    let out = [
      rp_0_0; rp_1_0; rp_2_0; rp_3_0;
       a_0_0;  a_1_0;  a_2_0;  a_3_0;
       a_4_0;  a_5_0;  a_6_0;  a_7_0;
       a_8_0;  a_9_0; a_10_0; a_11_0;
      a_12_0; a_13_0; a_14_0; a_15_0;
    ] in

    List.flatten out
end

(* -------------------------------------------------------------------- *)
let poly_compress () : C.reg =
  let module M = PolyCompress() in

  let rp_0 = C.reg ~size:256 ~name:0x00 in
  let rp_1 = C.reg ~size:256 ~name:0x01 in
  let rp_2 = C.reg ~size:256 ~name:0x02 in
  let rp_3 = C.reg ~size:256 ~name:0x03 in
  let a_0  = C.reg ~size:256 ~name:0x04 in
  let a_1  = C.reg ~size:256 ~name:0x05 in
  let a_2  = C.reg ~size:256 ~name:0x06 in
  let a_3  = C.reg ~size:256 ~name:0x07 in
  let a_4  = C.reg ~size:256 ~name:0x08 in
  let a_5  = C.reg ~size:256 ~name:0x09 in
  let a_6  = C.reg ~size:256 ~name:0x0a in
  let a_7  = C.reg ~size:256 ~name:0x0b in
  let a_8  = C.reg ~size:256 ~name:0x0c in
  let a_9  = C.reg ~size:256 ~name:0x0d in
  let a_10 = C.reg ~size:256 ~name:0x0e in
  let a_11 = C.reg ~size:256 ~name:0x0f in
  let a_12 = C.reg ~size:256 ~name:0x10 in
  let a_13 = C.reg ~size:256 ~name:0x11 in
  let a_14 = C.reg ~size:256 ~name:0x12 in
  let a_15 = C.reg ~size:256 ~name:0x13 in

  M.poly_compress
    (rp_0 : C.reg) (rp_1 : C.reg) (rp_2 : C.reg) (rp_3 : C.reg)
    (a_0  : C.reg) (a_1  : C.reg) (a_2  : C.reg) (a_3  : C.reg)
    (a_4  : C.reg) (a_5  : C.reg) (a_6  : C.reg) (a_7  : C.reg)
    (a_8  : C.reg) (a_9  : C.reg) (a_10 : C.reg) (a_11 : C.reg)
    (a_12 : C.reg) (a_13 : C.reg) (a_14 : C.reg) (a_15 : C.reg)

(* -------------------------------------------------------------------- *)
let poly_compress () =
  Format.eprintf "%s@." "Constructing circuit...";

  let circuit = poly_compress () in

  let names = Array.of_list [
    "rp_0";
    "rp_1";
    "rp_2";
    "rp_3";
    "a_0" ;
    "a_1" ;
    "a_2" ;
    "a_3" ;
    "a_4" ;
    "a_5" ;
    "a_6" ;
    "a_7" ;
    "a_8" ;
    "a_9" ;
    "a_10";
    "a_11";
    "a_12";
    "a_13";
    "a_14";
    "a_15";
  ] in


  Format.eprintf "%s@." "Computing dependencies...";

  let deps = C.deps circuit in

  List.iter (fun ((lo, hi), deps) ->
    let vs =
         Iter.(--) lo hi
      |> Iter.fold (fun vs i ->
           let name = Format.sprintf "out_%03d" (i / 256) in
           C.VarRange.push vs (name, i mod 256)
         ) C.VarRange.empty in

    Format.eprintf "%a: %a@."
      (C.VarRange.pp Format.pp_print_string) vs
      (C.VarRange.pp
         (fun fmt i -> Format.fprintf fmt "%s" names.(i)))
      deps
  ) deps


(* -------------------------------------------------------------------- *)
(* let () = main () *)
let () = test_smod ()
