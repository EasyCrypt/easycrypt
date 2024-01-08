(* -------------------------------------------------------------------- *)
open Lospecs
open Lospecs.Circuit

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
  mk    : reg list -> reg;
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
      let r = Arith.reg ~size:sz ~name in
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
    let env ((n, k) : var) = (vsa.(n) lsr k) land 0b1 <> 0 in
    let out = List.map (eval env) circuit in
    let out =
      match op.out with
      | `S -> sint_of_bools out
      | `U -> uint_of_bools out in
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
    { name = (Printf.sprintf "uextend<%d,%d>" isize osize)
    ; args = [(isize, `U)]
    ; out  = `U
    ; mk   = (fun rs -> Arith.uextend ~size:osize (as_seq1 rs))
    ; reff = (fun vs -> as_seq1 vs)
    }

  in test (op 8 16)

(* -------------------------------------------------------------------- *)
let test_sextend () =
  let op (isize : int) (osize : int) : op =
    { name = (Printf.sprintf "sextend<%d,%d>" isize osize)
    ; args = [(isize, `S)]
    ; out  = `S
    ; mk   = (fun rs -> Arith.sextend ~size:osize (as_seq1 rs))
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

    { name = (Printf.sprintf "shift<%s,%s,%d>" str_side str_sign size)
    ; args = [(size, sign); (4, `U)]
    ; out  = sign
    ; mk   = (fun rs -> let x, y = as_seq2 rs in Arith.shift ~side ~sign x y)
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

    { name = (Printf.sprintf "opp<%d>" size)
    ; args = [(size, `S)]
    ; out  = `S
    ; mk   = (fun rs -> Arith.opp (as_seq1 rs))
    ; reff = (fun vs -> sim (as_seq1 vs))
    }

  in test (op 13)

(* -------------------------------------------------------------------- *)
let test_add () =
  let op (size : int) : op =
    let module M = (val Word.sword ~size) in

    let sim (x : int) (y : int) : int =
      M.to_int (M.add (M.of_int x) (M.of_int y)) in

    { name = (Printf.sprintf "add<%d>" size)
    ; args = List.make 2 (size, `S)
    ; out  = `S
    ; mk   = (fun rs -> let x, y = as_seq2 rs in Arith.add_dropc x y)
    ; reff = (fun vs -> let x, y = as_seq2 vs in sim x y)
    }

  in test (op 9)

(* -------------------------------------------------------------------- *)
let test_incr () =
  let op (size : int) : op =
    let module M = (val Word.uword ~size) in

    let sim (x : int) : int =
      M.to_int (M.add (M.of_int x) M.one) in

    { name = (Printf.sprintf "incr<%d>" size)
    ; args = [(size, `U)]
    ; out  = `U
    ; mk   = (fun rs -> Arith.incr_dropc (as_seq1 rs))
    ; reff = (fun vs -> sim (as_seq1 vs));
  }

  in test (op 11)

(* -------------------------------------------------------------------- *)
let test_sub () =
  let op (size : int) : op =
    let module M = (val Word.sword ~size) in

    let sim (x : int) (y : int) : int =
      M.to_int (M.sub (M.of_int x) (M.of_int y)) in

    { name = (Printf.sprintf "sub<%d>" size)
    ; args = List.make 2 (size, `S)
    ; out  = `S
    ; mk   = (fun rs -> let x, y = as_seq2 rs in Arith.sub_dropc x y)
    ; reff = (fun vs -> let x, y = as_seq2 vs in sim x y)
    }

  in test (op 9)

(* -------------------------------------------------------------------- *)
let test_umul () =
  let op (sz1 : int) (sz2 : int) : op = {
    name = (Printf.sprintf "umul<%d,%d>" sz1 sz2);
    args = [(sz1, `U); (sz2, `U)];
    out  = `U;
    mk   = (fun rs -> let x, y = as_seq2 rs in Arith.umul x y);
    reff = (fun vs -> let x, y = as_seq2 vs in (x * y));
  } in

  test (op 10 8)

(* -------------------------------------------------------------------- *)
let test_smul () =
  let op (sz1 : int) (sz2 : int) : op = {
    name = (Printf.sprintf "smul<%d,%d>" sz1 sz2);
    args = [(sz1, `S); (sz2, `S)];
    out  = `S;
    mk   = (fun rs -> let x, y = as_seq2 rs in Arith.smul x y);
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
              Arith.smul
                (Arith.uextend ~size:16 x)
                (Arith.sextend ~size:16 y));
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

 {  name = (Printf.sprintf "ssat<%d,%d>" isize osize);
    args = [(isize, `S)];
    out  = `S;
    mk   = (fun rs -> Arith.sat ~signed:true ~size:osize (as_seq1 rs));
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

 {  name = (Printf.sprintf "usat<%d,%d>" isize osize);
    args = [(isize, `S)];
    out  = `U;
    mk   = (fun rs -> Arith.sat ~signed:false ~size:osize (as_seq1 rs));
    reff = (fun vs -> saturate (as_seq1 vs)); } in

  test (op 10 4);
  test (op 15 7)

(* -------------------------------------------------------------------- *)
type vpop = {
  name : string;
  acount : int;
  mk : reg list -> reg;
  reff : Avx2.m256 list -> Avx2.m256;
}

(* -------------------------------------------------------------------- *)
let test_vp (total : int) (op : vpop) =
  let rs = List.init op.acount (fun i -> Arith.reg ~size:256 ~name:i) in

  let circuit = op.mk rs in

  let test () =
    let vs = List.init op.acount (fun _ -> Avx2.random ()) in
    let avs = Array.of_list vs in
    let avs = Array.map (Avx2.to_bytes ~endianess:`Little) avs in

    let env ((n, i) : var) = get_bit avs.(n) i in

    let o = op.reff vs in
    let o = Avx2.to_bytes ~endianess:`Little o in

    let o' = List.map (eval env) circuit in
    let o' = bytes_of_bools o' in

    if o <> o' then begin
      Progress.interject_with (fun () ->
        vs |> List.iter (fun v ->
          Format.eprintf "%a@."
          (Avx2.pp ~endianess:`Big ~size:`U32)
          v
        );
        Format.eprintf "%a@."
          (Avx2.pp ~endianess:`Big ~size:`U32)
          (Avx2.of_bytes ~endianess:`Little o);
        Format.eprintf "%a@."
          (Avx2.pp ~endianess:`Big ~size:`U32)
          (Avx2.of_bytes ~endianess:`Little o')
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
    acount = 2;
    mk = (fun rs -> let x, y = as_seq2 rs in Circuit.vpadd_16u16 x y);
    reff = (fun vs -> let x, y = as_seq2 vs in Avx2.mm256_add_epi16 x y);
  } in

  test_vp 10000 op

(* -------------------------------------------------------------------- *)
let test_vpsub_16u16 () =
  let op = {
    name = "vpsub_16u16";
    acount = 2;
    mk = (fun rs -> let x, y = as_seq2 rs in Circuit.vpsub_16u16 x y);
    reff = (fun vs -> let x, y = as_seq2 vs in Avx2.mm256_sub_epi16 x y);
  } in

  test_vp 10000 op

(* -------------------------------------------------------------------- *)
let test_vpsra_16u16 () =
  let op (offset : int) = {
    name = Format.sprintf "vpsra_16u16<%d>" offset;
    acount = 1;
    mk = (fun rs -> Circuit.vpsra_16u16 (as_seq1 rs) offset);
    reff = (fun vs -> Avx2.mm256_srai_epi16 (as_seq1 vs) offset);
  } in

  Iter.iter (fun i -> test_vp 10000 (op i)) (Iter.(--) 0x00 0x10)

(* -------------------------------------------------------------------- *)
let test_vpand_256 () =
  let op = {
    name = "vpand_256";
    acount = 2;
    mk = (fun rs -> let x, y = as_seq2 rs in Circuit.vpand_256 x y);
    reff = (fun vs -> let x, y = as_seq2 vs in Avx2.mm256_and_si256 x y);
  } in

  test_vp 10000 op

(* -------------------------------------------------------------------- *)
let test_vpmulh_16u16 () =
  let op = {
    name = "vpmulh_16u16";
    acount = 2;
    mk = (fun rs -> let x, y = as_seq2 rs in Circuit.vpmulh_16u16 x y);
    reff = (fun vs -> let x, y = as_seq2 vs in Avx2.mm256_mulhi_epu16 x y);
  } in

  test_vp 200 op

(* -------------------------------------------------------------------- *)
let test_vpmulhrs_16u16 () =
  let op = {
    name = "vpmulhrs_16u16";
    acount = 2;
    mk = (fun rs -> let x, y = as_seq2 rs in Circuit.vpmulhrs_16u16 x y);
    reff = (fun vs -> let x, y = as_seq2 vs in Avx2.mm256_mulhrs_epi16 x y);
  } in

  test_vp 200 op

(* -------------------------------------------------------------------- *)
let test_vpackus_16u16 () =
  let op = {
    name = "vpackus_16u16";
    acount = 2;
    mk = (fun rs -> let x, y = as_seq2 rs in Circuit.vpackus_16u16 x y);
    reff = (fun vs -> let x, y = as_seq2 vs in Avx2.mm256_packus_epi16 x y);
  } in

  test_vp 10000 op

(* -------------------------------------------------------------------- *)
let test_vpmaddubsw_256 () =
  let op = {
    name = "vpmaddubsw_256";
    acount = 2;
    mk = (fun rs -> let x, y = as_seq2 rs in Circuit.vpmaddubsw_256 x y);
    reff = (fun vs -> let x, y = as_seq2 vs in Avx2.mm256_maddubs_epi16 x y);
  } in

  test_vp 200 op

(* -------------------------------------------------------------------- *)
let test_vpermd () =
  let op = {
    name = "vpermd";
    acount = 2;
    mk = (fun rs -> let x, y = as_seq2 rs in Circuit.vpermd x y);
    reff = (fun vs -> let x, y = as_seq2 vs in Avx2.mm256_permutexvar_epi32 x y);
  } in

  test_vp 10000 op

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

  ("lsl", (fun () -> test_shift ~side:`L ~sign:`U));
  ("lsr", (fun () -> test_shift ~side:`R ~sign:`U));

  ("asl", (fun () -> test_shift ~side:`L ~sign:`S));
  ("asr", (fun () -> test_shift ~side:`R ~sign:`S));

  ("smul_u8_s8", test_smul_u8_s8);

  ("uextend", test_uextend);
  ("sextend", test_sextend);

  ("vpadd_16u16"   , test_vpadd_16u16   );
  ("vpsub_16u16"   , test_vpsub_16u16   );
  ("vpsra_16u16"   , test_vpsra_16u16   );
  ("vpand_256"     , test_vpand_256     );
  ("vpmulh_16u16"  , test_vpmulh_16u16  );
  ("vpmulhrs_16u16", test_vpmulhrs_16u16);
  ("vpackus_16u16" , test_vpackus_16u16 );
  ("vpmaddubsw_256", test_vpmaddubsw_256);
  ("vpermd"        , test_vpermd        );
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

(* -------------------------------------------------------------------- *)
let poly_compress () =
  Format.eprintf "%s@." "Constructing circuit...";

  let circuit = Circuit.poly_compress () in

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

  let deps = deps circuit in

  List.iter (fun ((lo, hi), deps) ->
    let vs =
         Iter.(--) lo hi
      |> Iter.fold (fun vs i ->
           let name = Format.sprintf "out_%03d" (i / 256) in
           VarRange.push vs (name, i mod 256)
         ) VarRange.empty in

    Format.eprintf "%a: %a@."
      (VarRange.pp Format.pp_print_string) vs
      (VarRange.pp
         (fun fmt i -> Format.fprintf fmt "%s" names.(i)))
      deps
  ) deps

(* -------------------------------------------------------------------- *)
let () = main ()
