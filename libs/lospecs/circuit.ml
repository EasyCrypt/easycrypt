
(* ==================================================================== *)
open Aig

(* ==================================================================== *)
let sint_of_bools (bs : bool list) : int =
  assert (List.length bs <= Sys.int_size);

  let bs =
    match List.rev bs with
    | [] ->
      List.make Sys.int_size false
    | msb :: bs ->
      List.rev bs @ List.make (Sys.int_size - List.length bs) msb
  in

  List.fold_lefti
    (fun v i b -> if b then (1 lsl i) lor v else v)
    0 bs

(* -------------------------------------------------------------------- *)
let uint_of_bools (bs : bool list) : int =
  assert (List.length bs <= Sys.int_size - 1);

  List.fold_lefti
    (fun v i b -> if b then (1 lsl i) lor v else v)
    0 bs

(* -------------------------------------------------------------------- *)
let int32_of_bools (bs : bool list) : int32 =
  List.fold_lefti
    (fun v i b ->
       if b then
         Int32.logor (Int32.shift_left 1l i) v
       else
         v)
    0l bs

(* -------------------------------------------------------------------- *)
let explode (type t) ~(size : int) (r : t list) =
  assert (List.length r mod size == 0);

  let rec doit (acc : t list list) (r : t list) =
    if List.is_empty r then
      List.rev acc
    else
      let r1, r = List.split_nth size r in
      doit (r1 :: acc) r

  in doit [] r

(* -------------------------------------------------------------------- *)
let bytes_of_bools (bs : bool list) : bytes =
  let bs = List.to_seq (explode ~size:8 bs) in
  let bs = Seq.map (uint_of_bools %> Char.chr) bs in
  Bytes.of_seq bs

(* -------------------------------------------------------------------- *)
let pp_reg ~(size : int) (fmt : Format.formatter) (r : bool list) =
  assert (List.length r mod (size * 4) = 0);

  let r = explode ~size:(size * 4) r in
  let r = List.map int32_of_bools r in

  Format.fprintf fmt "%a"
    (Format.pp_print_list
       ~pp_sep:(fun fmt () -> Format.pp_print_string fmt "_")
       (fun fmt -> Format.fprintf fmt "%0.8lx"))
    r

(* ==================================================================== *)
let bit ~(position : int) (v : int) : bool =
  (v lsr position) land 0b1 <> 0

(* -------------------------------------------------------------------- *)
let bit32 ~(position : int) (v : int32) : bool =
  let open Int32 in
  logand (shift_right v position) 0b1l <> 0l

(* -------------------------------------------------------------------- *)
let bit64 ~(position : int) (v : int64) : bool =
  let open Int64 in
  logand (shift_right v position) 0b1L <> 0L

(* ==================================================================== *)
let of_int ~(size : int) (v : int) : reg =
  List.init size (fun i -> constant (bit ~position:i v))

(* -------------------------------------------------------------------- *)
let of_int32 (v : int32) : reg =
  List.init 32 (fun i -> constant (bit32 ~position:i v))

(* -------------------------------------------------------------------- *)
let of_int64 (v : int64) : reg =
  List.init 64 (fun i -> constant (bit64 ~position:i v))

(* -------------------------------------------------------------------- *)
let of_int32s (vs : int32 list) : reg =
  List.flatten (List.map of_int32 vs)

(* -------------------------------------------------------------------- *)
let of_bigint ~(size : int) (v : Z.t) : reg =
  assert (0 <= Z.compare v Z.zero);
  assert (Z.numbits v <= size);
  List.init size (fun i -> constant (Z.testbit v i))

(* -------------------------------------------------------------------- *)
let of_string ~(size : int) (s : string) : reg =
  of_bigint ~size (Z.of_string s)

(* ==================================================================== *)
let w8 (i : int) : reg =
  of_int ~size:8 i

(* -------------------------------------------------------------------- *)
let w16 (i : int) : reg =
  of_int ~size:16 i

(* -------------------------------------------------------------------- *)
let w32 (i : int32) : reg =
  of_int32 i

(* -------------------------------------------------------------------- *)
let w64 (i : int64) : reg =
  of_int64 i

(* -------------------------------------------------------------------- *)
let w128 (s : string) : reg =
  of_string ~size:128 s

(* -------------------------------------------------------------------- *)
let w256 (s : string) : reg =
  of_string ~size:256 s

(* ==================================================================== *)
let reg ~(size : int) ~(name : int) : reg =
  List.init size (fun i -> input (name, i))

(* ==================================================================== *)
let lnot_ (r : reg) : reg =
  List.map neg r

(* -------------------------------------------------------------------- *)
let lor_ (r1 : reg) (r2 : reg) : reg =
  List.map2 or_ r1 r2

(* -------------------------------------------------------------------- *)
let land_ (r1 : reg) (r2 : reg) : reg =
  List.map2 and_ r1 r2

(* -------------------------------------------------------------------- *)
let ors (r : node list) : node =
  List.fold_left or_ false_ r

(* -------------------------------------------------------------------- *)
let ands (r : node list) : node =
  List.fold_left and_ true_ r

(* -------------------------------------------------------------------- *)
let lshift ~(offset : int) (r : reg) : reg =
  List.make offset false_ @ r

(* -------------------------------------------------------------------- *)
let uextend ~(size : int) (r : reg) : reg =
  r @ List.make (max 0 (size - List.length r)) false_

(* -------------------------------------------------------------------- *)
let sextend ~(size : int) (r : reg) : reg =
  let lr = List.length r in

  if size > lr then
    match List.rev r with
    | [] ->
      List.make size false_
    | msb :: r ->
      List.rev_append r (List.make (size - lr + 1) msb)
  else
    r

(* -------------------------------------------------------------------- *)
let mux2 (n1 : node) (n2 : node) (c : node) =
  or_ (and_ (neg c) n1) (and_ c n2)

(* -------------------------------------------------------------------- *)
let mux2_reg (r1 : reg) (r2 : reg) (c : node) =
  assert (List.length r1 = List.length r2);
  List.map2 (fun n1 n2 -> mux2 n1 n2 c) r1 r2

(* -------------------------------------------------------------------- *)
let mux_reg (cr : (node * reg) list) (r : reg) : reg =
  List.fold_right (fun (c, r) s -> mux2_reg s r c) cr r

(* -------------------------------------------------------------------- *)
let c_rshift ~(offset : int) ~(sign : node) (c : node) (r : reg) =
  let l = List.length r in
  let s = List.drop offset r @ List.make (min offset l) sign in
  List.map2 (fun r1 s1 -> mux2 r1 s1 c) r s

(* -------------------------------------------------------------------- *)
let arshift ~(offset : int) (r : reg) =
  let sign = Option.default false_ (List.Exceptionless.last r) in
  let l = List.length r in
  List.drop offset r @ List.make (min offset l) sign

(* -------------------------------------------------------------------- *)
let lsr_ (r : reg) (s : reg) : reg =
  let _, r =
    List.fold_left (fun (i, r) c ->
      (i+1, c_rshift ~offset:(1 lsl i) ~sign:false_ c r)
    ) (0, r) s
  in r

(* -------------------------------------------------------------------- *)
let lsl_ (r : reg) (s : reg) : reg =
  List.rev (lsr_ (List.rev r) s)

(* -------------------------------------------------------------------- *)
let asl_ (r : reg) (s : reg) : reg =
  lsl_ r s

(* -------------------------------------------------------------------- *)
let asr_ (r : reg) (s : reg) : reg =
  let sign =
    Option.default false_ (List.Exceptionless.last r) in

  let _, r =
    List.fold_left (fun (i, r) c ->
      (i+1, c_rshift ~offset:(1 lsl i) ~sign c r)
    ) (0, r) s
  in r

(* -------------------------------------------------------------------- *)
let shift ~(side : [`L | `R]) ~(sign : [`U | `S]) =
  match side, sign with
  | `L, `U -> lsl_
  | `R, `U -> lsr_
  | `L, `S -> asl_
  | `R, `S -> asr_

(* -------------------------------------------------------------------- *)
let halfadder (a : node) (b : node) : node * node =
  (and_ a b, xor a b)

(* -------------------------------------------------------------------- *)
let incr (r : reg) : node * reg =
  List.fold_left_map halfadder true_ r

(* -------------------------------------------------------------------- *)
let incrc (r : reg) : reg =
  let c, r = incr r in r @ [c]

(* -------------------------------------------------------------------- *)
let incr_dropc (r : reg) : reg =
  snd (List.fold_left_map halfadder true_ r)

(* -------------------------------------------------------------------- *)
let opp (r : reg) : reg =
  incr_dropc (lnot_ r)

(* -------------------------------------------------------------------- *)
let fulladder (c : node) (a : node) (b : node) : node * node =
  let c1, s = halfadder a b in
  let c2, s = halfadder c s in
  (or_ c1 c2, s)

(* -------------------------------------------------------------------- *)
let addsub (m : node) (r1 : reg) (r2 : reg) : node * reg =
  assert(List.length r1 = List.length r2);

  List.fold_left_map
    (fun carry (a, b) -> fulladder carry a (xor b m))
    m (List.combine r1 r2)

(* -------------------------------------------------------------------- *)
let add (r1 : reg) (r2 : reg) : node * reg =
  addsub false_ r1 r2

(* -------------------------------------------------------------------- *)
let addc (r1 : reg) (r2 : reg) : reg =
  let c, r = add r1 r2 in r @ [c]

(* -------------------------------------------------------------------- *)
let add_dropc (r1 : reg) (r2 : reg) : reg =
  snd (add r1 r2)

(* -------------------------------------------------------------------- *)
let sub (r1 : reg) (r2 : reg) : node * reg =
  addsub true_ r1 r2

(* -------------------------------------------------------------------- *)
let sub_dropc (r1 : reg) (r2 : reg) : reg =
  snd (sub r1 r2)

(* -------------------------------------------------------------------- *)
let bmul (n : node) (r : reg) : reg =
  List.map (fun n' -> and_ n n') r

(* -------------------------------------------------------------------- *)
let umul_ (r1 : reg) (r2 : reg) : reg * reg =
  let n1 = List.length r1 in
  let n2 = List.length r2 in

  let prods = List.mapi (fun i n -> lshift ~offset:i (bmul n r2)) r1 in

  let out = List.fold_left addc (List.make n2 false_) prods in
  let out = List.take (n1 + n2) out in

  List.split_nth n2 out

(* -------------------------------------------------------------------- *)
let umul (r1 : reg) (r2 : reg) : reg =
  let o1, o2 = umul_ r1 r2 in o1 @ o2

(* -------------------------------------------------------------------- *)
let umull (r1 : reg) (r2 : reg) : reg =
  fst (umul_ r1 r2)

(* -------------------------------------------------------------------- *)
let umulh (r1 : reg) (r2 : reg) : reg =
  snd (umul_ r1 r2)

(* -------------------------------------------------------------------- *)
let smul_ (r1 : reg) (r2 : reg) : reg * reg =
  let nm, (r1, r2) =
    let n1 = List.length r1 in
    let n2 = List.length r2 in
    let nm = max n1 n2 in

    let r1 = sextend ~size:nm r1 in
    let r2 = sextend ~size:nm r2 in

    (nm, (r1, r2)) in

  let sbmul_r2 (n : node) =
    List.mapi (fun i n' ->
      let out = and_ n n' in
      if i+1 = nm then neg out else out
    ) r2 in

  let prods = List.mapi (fun i n ->
    let out = sbmul_r2 n in
    let out =
      match () with
      | _ when i = 0 -> out @ [true_]
      | _ when i+1 = nm -> (lnot_ out) @ [true_]
      | _ -> out @ [false_]
    in
    lshift ~offset:i out
  ) r1 in

  let out = List.fold_left addc (List.make (nm+1) false_) prods in

  List.split_nth nm (List.take (2 * nm) out)

(* -------------------------------------------------------------------- *)
let smul (r1 : reg) (r2 : reg) : reg =
  let sl, sh = smul_ r1 r2 in sl @ sh

(* -------------------------------------------------------------------- *)
let smull (r1 : reg) (r2 : reg) : reg =
  fst (smul_ r1 r2)

(* -------------------------------------------------------------------- *)
let ssat ~(size : int) (r : reg) : reg =
  assert (0 < size);
  assert (size < List.length r);

  let rl, rh = List.split_nth (size - 1) r in
  let rh, msb = List.split_nth (List.length rh - 1) rh in
  let msb = List.hd msb in

  let rm = List.make (size - 1) false_ @ [true_ ] in
  let rM = List.make (size - 1) true_  @ [false_] in
  let ro = rl @ [msb] in

  let cm = and_ msb (neg (ands rh)) in
  let cM = and_ (neg msb) (ors rh) in

  mux_reg [(cm, rm); (cM, rM)] ro

(* -------------------------------------------------------------------- *)
let usat ~(size : int) (r : reg) : reg =
  assert (size < List.length r);

  let rl, rh = List.split_nth size r in
  let rh, msb = List.split_nth (List.length rh - 1) rh in
  let msb = List.hd msb in

  let rm = List.make size false_ in
  let rM = List.make size true_ in
  let ro = rl in

  let cm = msb in
  let cM = and_ (neg msb) (ors rh) in

  mux_reg [(cm, rm); (cM, rM)] ro

(* -------------------------------------------------------------------- *)
let sat ~(signed : bool) ~(size : int) (r : reg) : reg =
  match signed with
  | true  -> ssat ~size r
  | false -> usat ~size r
