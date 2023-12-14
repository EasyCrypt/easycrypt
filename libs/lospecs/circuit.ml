(* -------------------------------------------------------------------- *)
type name = int

(* -------------------------------------------------------------------- *)
type var = name * int

(* -------------------------------------------------------------------- *)
type node_r =
  | False
  | Input of var
  | And   of node * node

and node = {
  gate : node_r;
  sign : bool;
  neg  : node;
}

(* -------------------------------------------------------------------- *)
type reg = node list

(* -------------------------------------------------------------------- *)
module HCons = Hashtbl.Make(struct
  type t = node_r

  let hash = (Hashtbl.hash : t -> int)

  let equal (n1 : node_r) (n2 : node_r) =
    match n1, n2 with
    | False, False ->
      true

    | Input v1, Input v2 ->
      v1 = v2

    | And (n1, m1), And (n2, m2) ->
      n1 == n2 && m1 == m2

    | _, _ ->
      false
end)

(* -------------------------------------------------------------------- *)
let rec pp_node (fmt : Format.formatter) (n : node) =
  match n with
  | { gate = False; sign = true; } ->
    Format.fprintf fmt "⊥"

  | { gate = False; sign = false; } ->
    Format.fprintf fmt "⊤"

  | { gate = Input (n, i); sign; } ->
    Format.fprintf fmt "%s%d#%0.4x"
      (if sign then "" else "¬") n i

  | { gate = And (n1, n2); sign = true; } ->
    Format.fprintf fmt "(%a) ∧ (%a)" pp_node n1 pp_node n2

  | { gate = And (n1, n2); sign = false; } ->
    Format.fprintf fmt "¬((%a) ∧ (%a))" pp_node n1 pp_node n2

(* -------------------------------------------------------------------- *)
let hcons : node HCons.t = HCons.create 0

(* -------------------------------------------------------------------- *)
let mk (n : node_r) : node =
  match HCons.find_option hcons n with
  | None ->
    let rec pos = { gate = n; sign = true ; neg = neg; }
    and     neg = { gate = n; sign = false; neg = pos; } in

    HCons.add hcons n pos; pos

  | Some pos ->
    pos

(* -------------------------------------------------------------------- *)
let false_ : node =
  mk False

(* -------------------------------------------------------------------- *)
let true_ : node =
  false_.neg

(* -------------------------------------------------------------------- *)
let input (i : var) : node =
  mk (Input i)

(* -------------------------------------------------------------------- *)
let constant (b : bool) : node =
  if b then true_ else false_

(* -------------------------------------------------------------------- *)
let neg (n : node) : node =
  n.neg

(* -------------------------------------------------------------------- *)
let and_ (n1 : node) (n2 : node) : node =
  match () with
  | _ when n1 == n2     -> n1
  | _ when n1 == n2.neg -> false_
  | _ when n1 == false_ -> false_
  | _ when n2 == false_ -> false_
  | _ when n1 == true_  -> n2
  | _ when n2 == true_  -> n1
  | _                   -> mk (And (n1, n2))

(* -------------------------------------------------------------------- *)
let nand (n1 : node) (n2 : node) : node =
  neg (and_ n1 n2)

(* -------------------------------------------------------------------- *)
let or_ (n1 : node) (n2 : node) : node =
  nand (neg n1) (neg n2)

(* -------------------------------------------------------------------- *)
let xor (n1 : node) (n2 : node) : node =
  let n = nand n1 n2 in nand (nand n1 n) (nand n2 n)

(* -------------------------------------------------------------------- *)
module HCache = Hashtbl.Make(struct
  type t = node_r

  let hash = (Hashtbl.hash : t -> int)
  let equal = ((==) : t -> t -> bool)
end)

(* -------------------------------------------------------------------- *)
let eval (env : var -> bool) =
  let cache : bool HCache.t = HCache.create 0 in

  let rec for_node (n : node) =
    if n.sign then for_node_r n.gate else not (for_node_r n.gate)

  and for_node_r (n : node_r) =
    match HCache.find_option cache n with
    | Some value ->
      value
    | None ->
      let value = for_node_force n in
      HCache.add cache n value; value

  and for_node_force (n : node_r) =
    match n with
    | False -> false
    | Input x -> env x
    | And (n1, n2) -> for_node n1 && for_node n2

  in fun (n : node) -> for_node n

(* -------------------------------------------------------------------- *)
let eval0 (n : node) =
  eval (fun (_ : var) -> false) n

(* ==================================================================== *)
module VarRange : sig
  type 'a t

  val empty : 'a t

  val push : 'a t -> ('a * int) -> 'a t

  val contents : 'a t -> ('a * (int * int) list) list

  val pp :
       (Format.formatter -> 'a -> unit)
    -> Format.formatter
    -> 'a t
    -> unit
end = struct
  type range = int * int

  type ranges = range list

  type 'a dep1 = 'a * ranges

  type 'a t = ('a, ranges) Map.t

  let empty : 'a t =
    Map.empty

  let rec add (rg : ranges) (v : int) =
    match rg with
    | [] ->
      [(v, v)]

      (* join two segments *)
    | (lo, hi) :: (lo', hi') :: tl when hi+1 = v && v+1 = lo' ->
      (lo, hi') :: tl

      (* add to the front of a segment *)
    | (lo, hi) :: tl when v+1 = lo ->
      (v, hi) :: tl

      (* add to the back of a segment *)
    | (lo, hi) :: tl when hi+1 = v ->
      (lo, v) :: tl

    | hd :: tl ->
      hd :: add tl v

  let push (r : 'a t) ((n, i) : 'a * int) : 'a t =
    let change (rg : ranges option) =
      Some (add (Option.default [] rg) i)
    in Map.modify_opt n change r

  let contents (r : 'a t) : ('a * ranges) list =
    Map.bindings r

  let pp
      (pp  : Format.formatter -> 'a -> unit)
      (fmt : Format.formatter)
      (r   : 'a t)
  =
    let pp_range (fmt : Format.formatter) ((lo, hi) : range) =
      if lo = hi then
        Format.fprintf fmt "%d" lo
      else
        Format.fprintf fmt "%d-%d" lo hi in

    let pp_ranges (fmt : Format.formatter) (rgs : ranges) =
      Format.fprintf fmt "%a"
        (Format.pp_print_list
           ~pp_sep:(fun fmt () -> Format.fprintf fmt ",")
           pp_range)
        rgs in

    let pp_dep1 (fmt : Format.formatter) ((v, rgs) : 'a dep1) =
      Format.fprintf fmt "%a#%a" pp v pp_ranges rgs in

    Format.fprintf fmt "%a"
      (Format.pp_print_list
         ~pp_sep:(fun fmt () -> Format.fprintf fmt "; ")
         pp_dep1)
      (Map.bindings r)
end

(* ==================================================================== *)
let deps_ () =
  let cache : var Set.t HCache.t = HCache.create 0 in

  let rec doit_force (n : node) =
    match n.gate with
    | False -> Set.empty
    | Input v -> Set.singleton v
    | And (n1, n2) -> Set.union (doit n1) (doit n2)

  and doit (n : node) =
    match HCache.find_option cache n.gate with
    | Some value ->
      value
    | None ->
      let value = doit_force n in
      HCache.add cache n.gate value; value

  in fun (n : node) -> doit n

(* -------------------------------------------------------------------- *)
let deps (r : reg) =
  let out = ref [] in

  let push (hi : int) (dhi : var Set.t) =
    match !out with
    | _ when Set.is_empty dhi ->
      ()
    | ((lo, v), dlo) :: tl when v+1 = hi && not (Set.disjoint dlo dhi) ->
      out := ((lo, hi), Set.union dlo dhi) :: tl
    | _ ->
      out := ((hi, hi), dhi) :: !out in

  List.iteri push (List.map (deps_ ()) r);
  !out
    |> List.rev_map (fun (r, vs) ->
         let vs =
           Set.fold
             (fun v vs -> VarRange.push vs v)
             vs VarRange.empty
         in (r, vs)
       )
    |> List.sort (fun (r1, _) (r2, _) -> compare r1 r2)

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

(* ==================================================================== *)
module Arith : sig
  val of_int : size:int -> int -> reg

  val of_bigint : size:int -> Z.t -> reg

  val of_int32s : int32 list -> reg

  val w8 : int -> reg

  val w16 : int -> reg

  val w32 : int32 -> reg

  val w64 : int64 -> reg

  val w128 : string -> reg

  val w256 : string -> reg

  val mux2 : node -> node -> node -> node

  val mux2_reg : reg -> reg -> node -> reg

  val mux_reg : (node * reg) list -> reg -> reg

  val reg : size:int -> name:int -> reg

  val uextend : size:int -> reg -> reg

  val sextend : size:int -> reg -> reg

  val lnot_ : reg -> reg

  val lor_ : reg -> reg -> reg

  val land_ : reg -> reg -> reg

  val ors : node list -> node

  val ands : node list -> node

  val lsl_ : reg -> reg -> reg

  val lsr_ : reg -> reg -> reg

  val asl_ : reg -> reg -> reg

  val asr_ : reg -> reg -> reg

  val incr : reg -> node * reg

  val incr_dropc : reg -> reg

  val incrc : reg -> reg

  val add : reg -> reg -> node * reg

  val addc : reg -> reg -> reg

  val add_dropc : reg -> reg -> reg

  val opp : reg -> reg

  val sub : reg -> reg -> node * reg

  val sub_dropc : reg -> reg -> reg

  val umul : reg -> reg -> reg

  val umull : reg -> reg -> reg

  val umulh : reg -> reg -> reg

  val smul : reg -> reg -> reg

  val smull : reg -> reg -> reg

  val sat : signed:bool -> size:int -> reg -> reg
end = struct
  let bit ~(position : int) (v : int) : bool =
    (v lsr position) land 0b1 <> 0

  let bit32 ~(position : int) (v : int32) : bool =
    let open Int32 in
    logand (shift_right v position) 0b1l <> 0l

  let bit64 ~(position : int) (v : int64) : bool =
    let open Int64 in
    logand (shift_right v position) 0b1L <> 0L

  let of_int ~(size : int) (v : int) : reg =
    List.init size (fun i -> constant (bit ~position:i v))

  let of_int32 (v : int32) : reg =
    List.init 32 (fun i -> constant (bit32 ~position:i v))

  let of_int64 (v : int64) : reg =
    List.init 64 (fun i -> constant (bit64 ~position:i v))

  let of_int32s (vs : int32 list) : reg =
    List.flatten (List.map of_int32 vs)

  let of_bigint ~(size : int) (v : Z.t) : reg =
    assert (0 <= Z.compare v Z.zero);
    assert (Z.numbits v <= size);
    List.init size (fun i -> constant (Z.testbit v i))

  let of_string ~(size : int) (s : string) : reg =
    of_bigint ~size (Z.of_string s)

  let w8 (i : int) : reg =
    of_int ~size:8 i

  let w16 (i : int) : reg =
    of_int ~size:16 i

  let w32 (i : int32) : reg =
    of_int32 i

  let w64 (i : int64) : reg =
    of_int64 i

  let w128 (s : string) : reg =
    of_string ~size:128 s

  let w256 (s : string) : reg =
    of_string ~size:256 s

  let reg ~(size : int) ~(name : int) : reg =
    List.init size (fun i -> input (name, i))

  let lnot_ (r : reg) : reg =
    List.map neg r

  let lor_ (r1 : reg) (r2 : reg) : reg =
    List.map2 or_ r1 r2

  let land_ (r1 : reg) (r2 : reg) : reg =
    List.map2 and_ r1 r2

  let ors (r : node list) : node =
    List.fold_left or_ false_ r

  let ands (r : node list) : node =
    List.fold_left and_ true_ r

  let lshift ~(offset : int) (r : reg) : reg =
    List.make offset false_ @ r

  let uextend ~(size : int) (r : reg) : reg =
    r @ List.make (max 0 (List.length r - size)) false_

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

  let mux2 (n1 : node) (n2 : node) (c : node) =
    or_ (and_ (neg c) n1) (and_ c n2)

  let mux2_reg (r1 : reg) (r2 : reg) (c : node) =
    assert (List.length r1 = List.length r2);
    List.map2 (fun n1 n2 -> mux2 n1 n2 c) r1 r2

  let mux_reg (cr : (node * reg) list) (r : reg) : reg =
    List.fold_right (fun (c, r) s -> mux2_reg s r c) cr r

  let c_rshift ~(offset : int) ~(sign : node) (c : node) (r : reg) =
    let l = List.length r in
    let s = List.drop offset r @ List.make (min offset l) sign in
    List.map2 (fun r1 s1 -> mux2 r1 s1 c) r s

  let lsr_ (r : reg) (s : reg) : reg =
    let _, r =
      List.fold_left (fun (i, r) c ->
        (i+1, c_rshift ~offset:(1 lsl i) ~sign:false_ c r)
      ) (0, r) s
    in r

  let lsl_ (r : reg) (s : reg) : reg =
    List.rev (lsr_ (List.rev r) s)

  let asr_ (r : reg) (s : reg) : reg =
    lsr_ r s

  let asl_ (r : reg) (s : reg) : reg =
    let sign =
      Option.default false_ (List.Exceptionless.last r) in

    let _, r =
      List.fold_left (fun (i, r) c ->
        (i+1, c_rshift ~offset:(1 lsl i) ~sign c r)
      ) (0, r) s
    in r

  let halfadder (a : node) (b : node) : node * node =
    (and_ a b, xor a b)

  let incr (r : reg) : node * reg =
    List.fold_left_map halfadder true_ r

  let incrc (r : reg) : reg =
    let c, r = incr r in r @ [c]

  let incr_dropc (r : reg) : reg =
    snd (List.fold_left_map halfadder true_ r)

  let opp (r : reg) : reg =
    incr_dropc (lnot_ r)

  let fulladder (c : node) (a : node) (b : node) : node * node =
    let c1, s = halfadder a b in
    let c2, s = halfadder c s in
    (or_ c1 c2, s)

  let addsub (m : node) (r1 : reg) (r2 : reg) : node * reg =
    assert(List.length r1 = List.length r2);

    List.fold_left_map
      (fun carry (a, b) -> fulladder carry a (xor b m))
      m (List.combine r1 r2)

  let add (r1 : reg) (r2 : reg) : node * reg =
    addsub false_ r1 r2

  let addc (r1 : reg) (r2 : reg) : reg =
    let c, r = add r1 r2 in r @ [c]

  let add_dropc (r1 : reg) (r2 : reg) : reg =
    snd (add r1 r2)

  let sub (r1 : reg) (r2 : reg) : node * reg =
    addsub true_ r1 r2

  let sub_dropc (r1 : reg) (r2 : reg) : reg =
    snd (sub r1 r2)

  let bmul (n : node) (r : reg) : reg =
    List.map (fun n' -> and_ n n') r

  let umul_ (r1 : reg) (r2 : reg) : reg * reg =
    let n1 = List.length r1 in
    let n2 = List.length r2 in

    let prods = List.mapi (fun i n -> lshift ~offset:i (bmul n r2)) r1 in

    let out = List.fold_left addc (List.make n2 false_) prods in
    let out = List.take (n1 + n2) out in

    List.split_nth n2 out

  let umul (r1 : reg) (r2 : reg) : reg =
    let o1, o2 = umul_ r1 r2 in o1 @ o2

  let umull (r1 : reg) (r2 : reg) : reg =
    fst (umul_ r1 r2)

  let umulh (r1 : reg) (r2 : reg) : reg =
    snd (umul_ r1 r2)

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

  let smul (r1 : reg) (r2 : reg) : reg =
    let sl, sh = smul_ r1 r2 in sl @ sh

  let smull (r1 : reg) (r2 : reg) : reg =
    fst (smul_ r1 r2)

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

  let sat ~(signed : bool) ~(size : int) (r : reg) : reg =
    match signed with
    | true  -> ssat ~size r
    | false -> usat ~size r
end

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
let pp_reg ~(size : int) (fmt : Format.formatter) (r : bool list) =
  assert (List.length r mod (size * 4) = 0);

  let r = explode ~size:(size * 4) r in
  let r = List.map int32_of_bools r in

  Format.fprintf fmt "%a"
    (Format.pp_print_list
       ~pp_sep:(fun fmt () -> Format.pp_print_string fmt "_")
       (fun fmt -> Format.fprintf fmt "%0.8lx"))
    r

(* -------------------------------------------------------------------- *)
let vpermd (r : reg) (i : reg) =
  assert (List.length r = 256);
  assert (List.length i = 256);

  let perm1 (i : reg) : reg =
    let i = List.take 3 i in
    let i = List.make 5 false_ @ i in
    List.take 32 (Arith.lsr_ r i)
  in

  let o = List.map perm1 (explode ~size:32 i) in

  List.flatten o

(* -------------------------------------------------------------------- *)
let vpadd_16u16 (r1 : reg) (r2 : reg) : reg =
  assert (List.length r1 = 256);
  assert (List.length r2 = 256);
  let r1 = explode ~size:16 r1 in
  let r2 = explode ~size:16 r2 in
  List.flatten (List.map2 Arith.add_dropc r1 r2)

(* -------------------------------------------------------------------- *)
let vpsub_16u16 (r1 : reg) (r2 : reg) : reg =
  assert (List.length r1 = 256);
  assert (List.length r2 = 256);
  let r1 = explode ~size:16 r1 in
  let r2 = explode ~size:16 r2 in
  List.flatten (List.map2 Arith.sub_dropc r1 r2)

(* -------------------------------------------------------------------- *)
let vpsra_16u16 (r1 : reg) (r2 : reg) : reg =
  assert (List.length r1 = 256);
  assert (List.length r2 = 8);
  let r1 = explode ~size:16 r1 in
  List.flatten (List.map (fun r1 -> Arith.asr_ r1 r2) r1)

(* -------------------------------------------------------------------- *)
let vpand_256 (r1 : reg) (r2 : reg) : reg =
  assert (List.length r1 = 256);
  assert (List.length r2 = 256);
  List.map2 and_ r1 r2

(* -------------------------------------------------------------------- *)
let vpbroadcast_16u16 (r : reg) : reg =
  assert (List.length r = 16);
  List.flatten (List.make 16 r)

(* -------------------------------------------------------------------- *)
let vpmulh_16u16 (r1 : reg) (r2 : reg) : reg =
  assert (List.length r1 = 256);
  assert (List.length r2 = 256);
  let r1 = explode ~size:16 r1 in
  let r2 = explode ~size:16 r2 in
  List.flatten (List.map2 Arith.umulh r1 r2)

(* -------------------------------------------------------------------- *)
let vpmulhrs_16u16 (r1 : reg) (r2 : reg) : reg =
  assert (List.length r1 = 256);
  assert (List.length r2 = 256);
  let r1 = explode ~size:16 r1 in
  let r2 = explode ~size:16 r2 in

  let out = List.map2 (fun r1 r2 ->
    let r1 = Arith.sextend ~size:32 r1 in
    let r2 = Arith.sextend ~size:32 r2 in
    let r = Arith.smull r1 r2 in
    let r = Arith.lsl_ r (Arith.w8 14) in
    let r = Arith.incr_dropc r in

    List.take 16 (List.drop 1 r)
  ) r1 r2 in

  List.flatten out

(* -------------------------------------------------------------------- *)
let vpackus_16u16 (r1 : reg) (r2 : reg) : reg =
  let pack (r : reg) : reg =
    let out =
      List.map
        (Arith.sat ~signed:false ~size:8)
        (explode ~size:16 r)
    in List.flatten out in

  let vpackus (r1 : reg) (r2 : reg) : reg =
    assert (List.length r1 = 128);
    assert (List.length r2 = 128);
    pack r1 @ pack r2
  in

  let r1 = explode ~size:128 r1 in
  let r2 = explode ~size:128 r2 in

  List.flatten (List.map2 vpackus r1 r2)

(* -------------------------------------------------------------------- *)
let vpmaddubsw_256 (r1 : reg) (r2 : reg) : reg =
  assert (List.length r1 = 256);
  assert (List.length r2 = 256);

  let r1 = explode ~size:16 r1 in
  let r2 = explode ~size:16 r2 in

  let out = List.map2 (fun r1 r2 ->
    let r1l, r1h = List.split_nth 8 r1 in
    let r2l, r2h = List.split_nth 8 r2 in
    let out =
      Arith.addc
        (Arith.smull (Arith.uextend ~size:16 r1l) (Arith.sextend ~size:16 r2l))
        (Arith.smull (Arith.uextend ~size:16 r1h) (Arith.sextend ~size:16 r2h)) in
    Arith.sat ~signed:true ~size:16 out
  ) r1 r2 in

  List.flatten out

(* -------------------------------------------------------------------- *)
module PolyCompress() = struct
  let pc_permidx_s =
    Arith.w256
      "0x00000000_00000004_00000001_00000005_00000002_00000006_00000003_00000007"

  let pc_shift2_s =
    Arith.w16 0x1001

  let pc_mask_s =
    Arith.w16 0x000f

  let pc_shift1_s =
    Arith.w16 0x0200

  let jvx16 =
    Arith.w256
      "0x4ebf4ebf_4ebf4ebf_4ebf4ebf_4ebf4ebf_4ebf4ebf_4ebf4ebf_4ebf4ebf_4ebf4ebf"

  let jqx16 =
    Arith.w256
      "0xd010d010_d010d010_d010d010_d010d010_d010d010_d010d010_d010d010_d010d01"

  let poly_compress
    (rp_0 : reg)
    (rp_1 : reg)
    (rp_2 : reg)
    (rp_3 : reg)
    (a_0  : reg)
    (a_1  : reg)
    (a_2  : reg)
    (a_3  : reg)
    (a_4  : reg)
    (a_5  : reg)
    (a_6  : reg)
    (a_7  : reg)
    (a_8  : reg)
    (a_9  : reg)
    (a_10 : reg)
    (a_11 : reg)
    (a_12 : reg)
    (a_13 : reg)
    (a_14 : reg)
    (a_15 : reg)
  : reg
  =
    let qx16 = jqx16 in
    let r = a_0 in
    let r_0 = vpsub_16u16 r qx16 in
    let t = vpsra_16u16 r_0 (Arith.w8 0x0f) in
    let t_0 = vpand_256 t qx16 in
    let r_1 = vpadd_16u16 t_0 r_0 in
    let a_0_0 = r_1 in
    let r_2 = a_1 in
    let r_3 = vpsub_16u16 r_2 qx16 in
    let t_1 = vpsra_16u16 r_3 (Arith.w8 0x0f) in
    let t_2 = vpand_256 t_1 qx16 in
    let r_4 = vpadd_16u16 t_2 r_3 in
    let a_1_0 = r_4 in
    let r_5 = a_2 in
    let r_6 = vpsub_16u16 r_5 qx16 in
    let t_3 = vpsra_16u16 r_6 (Arith.w8 0x0f) in
    let t_4 = vpand_256 t_3 qx16 in
    let r_7 = vpadd_16u16 t_4 r_6 in
    let a_2_0 = r_7 in
    let r_8 = a_3 in
    let r_9 = vpsub_16u16 r_8 qx16 in
    let t_5 = vpsra_16u16 r_9 (Arith.w8 0x0f) in
    let t_6 = vpand_256 t_5 qx16 in
    let r_10 = vpadd_16u16 t_6 r_9 in
    let a_3_0 = r_10 in
    let r_11 = a_4 in
    let r_12 = vpsub_16u16 r_11 qx16 in
    let t_7 = vpsra_16u16 r_12 (Arith.w8 0x0f) in
    let t_8 = vpand_256 t_7 qx16 in
    let r_13 = vpadd_16u16 t_8 r_12 in
    let a_4_0 = r_13 in
    let r_14 = a_5 in
    let r_15 = vpsub_16u16 r_14 qx16 in
    let t_9 = vpsra_16u16 r_15 (Arith.w8 0x0f) in
    let t_10 = vpand_256 t_9 qx16 in
    let r_16 = vpadd_16u16 t_10 r_15 in
    let a_5_0 = r_16 in
    let r_17 = a_6 in
    let r_18 = vpsub_16u16 r_17 qx16 in
    let t_11 = vpsra_16u16 r_18 (Arith.w8 0x0f) in
    let t_12 = vpand_256 t_11 qx16 in
    let r_19 = vpadd_16u16 t_12 r_18 in
    let a_6_0 = r_19 in
    let r_20 = a_7 in
    let r_21 = vpsub_16u16 r_20 qx16 in
    let t_13 = vpsra_16u16 r_21 (Arith.w8 0x0f) in
    let t_14 = vpand_256 t_13 qx16 in
    let r_22 = vpadd_16u16 t_14 r_21 in
    let a_7_0 = r_22 in
    let r_23 = a_8 in
    let r_24 = vpsub_16u16 r_23 qx16 in
    let t_15 = vpsra_16u16 r_24 (Arith.w8 0x0f) in
    let t_16 = vpand_256 t_15 qx16 in
    let r_25 = vpadd_16u16 t_16 r_24 in
    let a_8_0 = r_25 in
    let r_26 = a_9 in
    let r_27 = vpsub_16u16 r_26 qx16 in
    let t_17 = vpsra_16u16 r_27 (Arith.w8 0x0f) in
    let t_18 = vpand_256 t_17 qx16 in
    let r_28 = vpadd_16u16 t_18 r_27 in
    let a_9_0 = r_28 in
    let r_29 = a_10 in
    let r_30 = vpsub_16u16 r_29 qx16 in
    let t_19 = vpsra_16u16 r_30 (Arith.w8 0x0f) in
    let t_20 = vpand_256 t_19 qx16 in
    let r_31 = vpadd_16u16 t_20 r_30 in
    let a_10_0 = r_31 in
    let r_32 = a_11 in
    let r_33 = vpsub_16u16 r_32 qx16 in
    let t_21 = vpsra_16u16 r_33 (Arith.w8 0x0f) in
    let t_22 = vpand_256 t_21 qx16 in
    let r_34 = vpadd_16u16 t_22 r_33 in
    let a_11_0 = r_34 in
    let r_35 = a_12 in
    let r_36 = vpsub_16u16 r_35 qx16 in
    let t_23 = vpsra_16u16 r_36 (Arith.w8 0x0f) in
    let t_24 = vpand_256 t_23 qx16 in
    let r_37 = vpadd_16u16 t_24 r_36 in
    let a_12_0 = r_37 in
    let r_38 = a_13 in
    let r_39 = vpsub_16u16 r_38 qx16 in
    let t_25 = vpsra_16u16 r_39 (Arith.w8 0x0f) in
    let t_26 = vpand_256 t_25 qx16 in
    let r_40 = vpadd_16u16 t_26 r_39 in
    let a_13_0 = r_40 in
    let r_41 = a_14 in
    let r_42 = vpsub_16u16 r_41 qx16 in
    let t_27 = vpsra_16u16 r_42 (Arith.w8 0x0f) in
    let t_28 = vpand_256 t_27 qx16 in
    let r_43 = vpadd_16u16 t_28 r_42 in
    let a_14_0 = r_43 in
    let r_44 = a_15 in
    let r_45 = vpsub_16u16 r_44 qx16 in
    let t_29 = vpsra_16u16 r_45 (Arith.w8 0x0f) in
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
let poly_compress () : reg =
  let module M = PolyCompress() in

  let rp_0 = Arith.reg ~size:256 ~name:0x00 in
  let rp_1 = Arith.reg ~size:256 ~name:0x01 in
  let rp_2 = Arith.reg ~size:256 ~name:0x02 in
  let rp_3 = Arith.reg ~size:256 ~name:0x03 in
  let a_0  = Arith.reg ~size:256 ~name:0x04 in
  let a_1  = Arith.reg ~size:256 ~name:0x05 in
  let a_2  = Arith.reg ~size:256 ~name:0x06 in
  let a_3  = Arith.reg ~size:256 ~name:0x07 in
  let a_4  = Arith.reg ~size:256 ~name:0x08 in
  let a_5  = Arith.reg ~size:256 ~name:0x09 in
  let a_6  = Arith.reg ~size:256 ~name:0x0a in
  let a_7  = Arith.reg ~size:256 ~name:0x0b in
  let a_8  = Arith.reg ~size:256 ~name:0x0c in
  let a_9  = Arith.reg ~size:256 ~name:0x0d in
  let a_10 = Arith.reg ~size:256 ~name:0x0e in
  let a_11 = Arith.reg ~size:256 ~name:0x0f in
  let a_12 = Arith.reg ~size:256 ~name:0x10 in
  let a_13 = Arith.reg ~size:256 ~name:0x11 in
  let a_14 = Arith.reg ~size:256 ~name:0x12 in
  let a_15 = Arith.reg ~size:256 ~name:0x13 in

  M.poly_compress
    (rp_0 : reg) (rp_1 : reg) (rp_2 : reg) (rp_3 : reg)
    (a_0  : reg) (a_1  : reg) (a_2  : reg) (a_3  : reg)
    (a_4  : reg) (a_5  : reg) (a_6  : reg) (a_7  : reg)
    (a_8  : reg) (a_9  : reg) (a_10 : reg) (a_11 : reg)
    (a_12 : reg) (a_13 : reg) (a_14 : reg) (a_15 : reg)
