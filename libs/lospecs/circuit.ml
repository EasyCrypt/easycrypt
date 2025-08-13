
(* ==================================================================== *)
open Aig

(* ==================================================================== *)
let rec log2 n =
  if n <= 1 then 0 else 1 + log2 (n lsr 1)

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

let ubigint_of_bools (bs: bool list) : Z.t =
  List.fold_right 
    (fun b acc -> 
    Z.(+) (Z.shift_left acc 1) (if b then Z.one else Z.zero)) 
    bs 
    Z.zero

let sbigint_of_bools (bs: bool list) : Z.t = 
  let bs = List.rev bs in
  let msb = List.hd bs in
  let vbs = List.tl bs in
  List.fold_left 
    (fun acc b -> 
    Z.(+) (Z.shift_left acc 1) (if b then Z.one else Z.zero)) 
    (if msb then Z.neg Z.one else Z.zero)
    vbs

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
let split_msb (r : reg) : node * reg =
  let n = List.length r in
  let r, msb = List.split_nth (n-1) r in
  let msb = List.hd msb in
  msb, r

(* ==================================================================== *)
let lnot_ (r : reg) : reg =
  List.map neg r

(* -------------------------------------------------------------------- *)
let lor_ (r1 : reg) (r2 : reg) : reg =
  List.map2 or_ r1 r2

(* -------------------------------------------------------------------- *)
let lxor_ (r1 : reg) (r2 : reg) : reg =
  List.map2 xor r1 r2

(* -------------------------------------------------------------------- *)
let lxnor_ (r1 : reg) (r2 : reg) : reg =
  List.map2 xnor r1 r2

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
let mux2_2
  ~(k00 : node)
  ~(k01 : node)
  ~(k10 : node)
  ~(k11 : node)
  ((c1, c2) : node * node)
=
  mux2
    (mux2 k00 k01 c2)
    (mux2 k10 k11 c2)
    c1

(* -------------------------------------------------------------------- *)
let mux2_2reg
  ~(k00 : reg)
  ~(k01 : reg)
  ~(k10 : reg)
  ~(k11 : reg)
  ((c1, c2) : node * node)
=
  mux2_reg
    (mux2_reg k00 k01 c2)
    (mux2_reg k10 k11 c2)
    c1

(* -------------------------------------------------------------------- *)
let mux_reg (cr : (node * reg) list) (r : reg) : reg =
  List.fold_right (fun (c, r) s -> mux2_reg s r c) cr r

(* -------------------------------------------------------------------- *)
let ite (c : node) (t : reg) (f : reg) : reg =
  mux2_reg f t c

(* -------------------------------------------------------------------- *)
let c_rshift ~(lg2o : int) ~(sign : node) (c : node) (r : reg) =
  let len   = List.length r in
  let clamp = log2 len in
  let s =
    if lg2o > clamp then
      List.make len sign
    else
      let offset = 1 lsl lg2o in
      List.drop (min offset len) r @ List.make (min offset len) sign
  in
    List.map2 (fun r1 s1 -> mux2 r1 s1 c) r s

(* -------------------------------------------------------------------- *)
let arshift ~(offset : int) (r : reg) =
  let sign = Option.default false_ (List.Exceptionless.last r) in
  let l = List.length r in
  List.drop (min offset l) r @ List.make (min offset l) sign

(* -------------------------------------------------------------------- *)
let lsr_ (r as r0 : reg) (s : reg) : reg =
  let _, r =
    List.fold_left (fun (i, r) c ->
      (i+1, c_rshift ~lg2o:i ~sign:false_ c r)
    ) (0, r) s
  in assert (List.length r = List.length r0); r

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
      (i+1, c_rshift ~lg2o:i ~sign c r)
    ) (0, r) s
  in r

(* -------------------------------------------------------------------- *)
let shift ~(side : [`L | `R]) ~(sign : [`L | `A]) =
  match side, sign with
  | `L, `L -> lsl_
  | `R, `L -> lsr_
  | `L, `A -> asl_
  | `R, `A -> asr_


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
let smulh (r1 : reg) (r2 : reg) : reg =
  snd (smul_ r1 r2)

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

(* -------------------------------------------------------------------- *)
let ssadd (r1 : reg) (r2 : reg) : reg =
  let n1 = List.length r1 in
  let n2 = List.length r2 in
  let n = max n1 n2 in

  let r1 = sextend ~size:(n+1) r1 in
  let r2 = sextend ~size:(n+1) r2 in

  ssat ~size:n (add_dropc r1 r2)

(* -------------------------------------------------------------------- *)
let usadd (r1 : reg) (r2 : reg) : reg =
  let r = addc r1 r2 in
  usat ~size:(List.length r - 1) r

(* -------------------------------------------------------------------- *)
let usmul (r1 : reg) (r2 : reg) : reg =
  let n1 = List.length r1 in
  let n2 = List.length r2 in
  let nm = max n1 n2 in

  let r1 = uextend ~size:(2*nm) r1 in
  let r2 = sextend ~size:(2*nm) r2 in

  smull r1 r2

(* -------------------------------------------------------------------- *)
let ugte (eq : node) (r1 : reg) (r2 : reg) : node =
  let n1 = List.length r1 in
  let n2 = List.length r2 in
  let n  = max n1 n2 in
  let r1 = uextend ~size:n r1 in
  let r2 = uextend ~size:n r2 in

  List.fold_left2 (fun ct c1 c2 ->
    mux2_2 (c1, c2)
      ~k00:ct
      ~k01:Aig.false_
      ~k10:Aig.true_
      ~k11:ct
  ) eq r1 r2

(* -------------------------------------------------------------------- *)
let sgte (eq : node) (r1 : reg) (r2 : reg) : node =
  let msb1, r1 = split_msb r1 in
  let msb2, r2 = split_msb r2 in

  mux2_2 (msb1, msb2)
    ~k00:(ugte eq r1 r2)
    ~k01:Aig.true_
    ~k10:Aig.false_
    ~k11:(ugte eq r1 r2)

(* -------------------------------------------------------------------- *)
let bvueq (r1 : reg) (r2 : reg) : node = 
  let n1 = List.length r1 in
  let n2 = List.length r2 in
  let n = max n1 n2 in
  let r1 = uextend ~size:n r1 in
  let r2 = uextend ~size:n r2 in

  List.fold_left2 (fun ct c1 c2 ->
    mux2_2 (c1, c2)
      ~k00:ct
      ~k01:Aig.false_
      ~k10:Aig.false_
      ~k11:ct
  ) Aig.true_ r1 r2
  
(* -------------------------------------------------------------------- *)
let bvseq (r1 : reg) (r2 : reg) : node = 
  let n1 = List.length r1 in
  let n2 = List.length r2 in
  let n = max n1 n2 in
  let r1 = sextend ~size:n r1 in
  let r2 = sextend ~size:n r2 in

  List.fold_left2 (fun ct c1 c2 ->
    mux2_2 (c1, c2)
      ~k00:ct
      ~k01:Aig.false_
      ~k10:Aig.false_
      ~k11:ct
  ) Aig.true_ r1 r2

(* -------------------------------------------------------------------- *)
let ugt (r1 : reg) (r2 : reg) : node =
  ugte Aig.false_ r1 r2

(* -------------------------------------------------------------------- *)
let uge (r1 : reg) (r2 : reg) : node =
  ugte Aig.true_ r1 r2

(* -------------------------------------------------------------------- *)
let ult (r1: reg) (r2 : reg) : node =
  ugt r2 r1

(* -------------------------------------------------------------------- *)
let ule (r1 : reg) (r2 : reg) : node =
  uge r2 r1

(* -------------------------------------------------------------------- *)
let sgt (r1 : reg) (r2 : reg) : node =
  sgte Aig.false_ r1 r2

(* -------------------------------------------------------------------- *)
let sge (r1 : reg) (r2 : reg) : node =
  sgte Aig.true_ r1 r2

(* -------------------------------------------------------------------- *)
let slt (r1 : reg) (r2 : reg) : node =
  sgt r2 r1

(* -------------------------------------------------------------------- *)
let sle (r1 : reg) (r2 : reg) : node =
  sge r2 r1

(* -------------------------------------------------------------------- *)
let iszero (r : reg) : node =
  bvueq r (List.map (fun _ -> false_) r)

(* -------------------------------------------------------------------- *)
let abs (a : reg) : reg =
  let msb_a, _ = split_msb a in
  ite (msb_a) (opp a) a

(* -------------------------------------------------------------------- *)
let udiv_ (a : reg) (b : reg) : reg * reg =
  assert (List.length a >= List.length b);

  let n = List.length b in

  let pu (a : node) (b : node) (cin : node) : node * (node -> node) =
    let cout, s = fulladder cin (neg b) a in
    let out (cc : node) = mux2 a s cc in
    (cout, out)
  in

  let create_line (i : int) (d : node) (a : reg) : node * reg =
    let a = d :: (if i = n then a else snd (split_msb a)) in
    let b = if i < n then b else b @ [Aig.false_] in

    let c, pus =
      List.fold_left_map
        (fun c (a, b) -> pu a b c)
        Aig.true_ (List.combine a b)
    in (c, List.map (fun pu -> pu c) pus)
  in

  List.fold_lefti (fun (q, a) i d ->
    let q', a = create_line i d a in (q' :: q, a)
  ) ([], List.make n false_) (List.rev a)

(* -------------------------------------------------------------------- *)
let udiv (a : reg) (b : reg) : reg =
  let m = max (List.length a) (List.length b) in
  let a = uextend ~size:m a in
  let b = uextend ~size:m b in
  ite (iszero b) a (fst (udiv_ a b))

(* -------------------------------------------------------------------- *)
let sdiv (s : reg) (t : reg) : reg =
  let msb_s, _ = split_msb s in
  let msb_t, _ = split_msb t in

  mux2_2reg
    ~k00:(    (udiv (    s) (    t)))
    ~k10:(opp (udiv (opp s) (    t)))
    ~k01:(opp (udiv (    s) (opp t)))
    ~k11:(    (udiv (opp s) (opp t)))
    (msb_s, msb_t)

(* -------------------------------------------------------------------- *)
let umod (a : reg) (b : reg) : reg =
  let m = max (List.length a) (List.length b) in
  let a = uextend ~size:m a in
  let b = uextend ~size:m b in

  ite
    (iszero b)
    (List.map (fun _ -> false_) b)
    (uextend ~size:m (snd (udiv_ a b)))

(* -------------------------------------------------------------------- *)
let srem (s : reg) (t : reg) : reg =
  let msb_s, _ = split_msb s in
  let msb_t, _ = split_msb t in

  mux2_2reg
    ~k00:(    (umod (    s) (    t)))
    ~k10:(opp (umod (opp s) (    t)))
    ~k01:(opp (umod (    s) (opp t)))
    ~k11:(    (umod (opp s) (opp t)))
    (msb_s, msb_t)

(* -------------------------------------------------------------------- *)
let smod (s : reg) (t : reg) : reg =  
  ite (iszero t) s @@
  let msb_s, _ = split_msb s in
  let msb_t, _ = split_msb t in

  let u = umod (abs s) (abs t) in

  ite (iszero u)
  u
  (mux2_2reg
    ~k00:(               u   )
    ~k10:(add_dropc (opp u) t)
    ~k01:(add_dropc (    u) t)
    ~k11:(          (opp u)  )
    (msb_s, msb_t))

(* -------------------------------------------------------------------- *)
let rol (r: reg) (s: reg) : reg =
  let size = List.length r in
  let s = umod s (of_int ~size size) in (* so 0 <= s < size *)
  let s = List.take size s |> uextend ~size in (* by above, ln s < size *)
  lor_ (shift ~side:`L ~sign:`L r s) (shift ~side:`R ~sign:`L r (sub_dropc (of_int ~size size) s)) 

(* -------------------------------------------------------------------- *)
let ror (r: reg) (s: reg) : reg =
  let size = List.length r in
  let s = umod s (of_int ~size size) in (* so 0 <= s < size *)
  let s = List.take size s |> uextend ~size in (* by above, ln s < size *)
  lor_ (shift ~side:`R ~sign:`L r s) (shift ~side:`L ~sign:`L r (sub_dropc (of_int ~size size) s)) 

(* -------------------------------------------------------------------- *)
let popcount ~(size : int) (r : reg) : reg =
  List.fold_left (fun aout node ->
    ite node (incr_dropc aout) aout
  ) (List.make size Aig.false_) r

(* -------------------------------------------------------------------- *)
(* FIXME: redo this *)
let of_bigint_all ~(size : int) (v : Z.t) : reg =
  let mod_ = Z.(lsl) Z.one (size) in
  let v = Z.rem v mod_ in
  let v = if Z.sign v < 0 then Z.add mod_ v else v in
  of_bigint ~size v
