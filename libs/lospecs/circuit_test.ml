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

  let bar =
    let open Progress.Line in
    list [
        spinner ~color:(Progress.Color.ansi `green) ()
      ; rpad (max 10 (String.length op.name)) (const op.name)
      ; bar total
      ; lpad (2 * 7 + 1) (count_to total)
    ]
  in

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
  test (op 15 7)

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
let test_vpermd () =
  let i = [0x00l; 0x04l; 0x01l; 0x05l; 0x02l; 0x06l; 0x03l; 0x07l] in
  let i = Arith.of_int32s i in

  let r = List.init 8 (fun _ -> Random.bits32 ()) in
  let r = Arith.of_int32s r in

  let env =
    let i = Array.of_list (List.map eval0 i) in
    let r = Array.of_list (List.map eval0 r) in

    fun ((n, k) : var) ->
      match n with
      | 0 when 0 <= k && k < 256 -> r.(k)
      | 1 when 0 <= k && k < 256 -> i.(k)
      | _ -> assert false
  in

  let o = vpermd (Arith.reg ~size:256 ~name:0) i in

  List.iteri (fun i o ->
    Format.eprintf "%0.4x: %a@." i pp_node o
  ) o;

(*
  let o =
    vpermd
      (Arith.reg ~size:256 ~name:0)
      (Arith.reg ~size:256 ~name:1) in
*)

  let i = List.map (eval env) i in
  let r = List.map (eval env) r in
  let o = List.map (eval env) o in

  List.iter (fun v ->
    Format.eprintf "%a@." (pp_reg ~size:8) v
  ) [i; r; o]

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
let () =
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
