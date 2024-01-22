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

let reg1 = C.reg ~size:256 ~name:0x00 
let reg2 = C.reg ~size:256 ~name:0x01

let pp_cdeps (deps) (names: string array) =
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
 
(* reg -> reg -> reg *)
let funcs =[("vpadd_16u16"      , C.vpadd_16u16      );
  ("vpadd_32u8"       , C.vpadd_32u8       );
  ("vpsub_16u16"      , C.vpsub_16u16      );
  ("vpsub_32u8"       , C.vpsub_32u8       );
  ("vpand_256"        , C.vpand_256        );
  ("vpmulh_16u16"     , C.vpmulh_16u16     );
  ("vpmulhrs_16u16"   , C.vpmulhrs_16u16   );
  ("vpackus_16u16"    , C.vpackus_16u16    );
  ("vpackss_16u16"    , C.vpackss_16u16    );
  ("vpmaddubsw_256"   , C.vpmaddubsw_256   );
  ("vpermd"           , C.vpermd           );
  ("vbshufb_256"      , C.vpshufb_256      );
  ("vpcmpgt_16u16"    , C.vpcmpgt_16u16    );
  ("vpunpckl_32u8"    , C.vpunpckl_32u8    );
]

(* reg -> int -> reg *)
let funcs2 =[
  ("vpsra_16u16"      , C.vpsra_16u16      );
  ("vpextracti128"    , C.vpextracti128    );
  ("vpsrl_16u16"      , C.vpsrl_16u16      );
  ("vpermq"           , C.vpermq           );
]

(* reg -> reg -> int -> reg *)
let funcs3 = [
  ("vpinserti128"     , C.vpinserti128     );
  ("vpblend_16u16"    , C.vpblend_16u16    );
]

(* reg -> reg *)
let func4 = [
  ("vpmovmskb_u256u64", C.vpmovmskb_u256u64);
]


let () = List.iter (fun (name, f) -> Format.eprintf "%s:@.%a" name (fun fmt f -> pp_cdeps (f reg1 reg2 |> C.deps) (Array.of_list ["reg1"; "reg2"])) f) funcs
