(* -------------------------------------------------------------------- *)
open Batteries
open Aig

(* -------------------------------------------------------------------- *)
exception InvalidWire

(* -------------------------------------------------------------------- *)
(* true -> positive wire *)
let u2si (u : int) : bool * int =
  if u < 0 then raise InvalidWire;
  let s = (u land 0b1) = 0 in
  let i = u lsr 1 in  (* We divide by 2 *)
  (s, i)

(* -------------------------------------------------------------------- *)
let si2u ((b, i) : bool * int) : int =
  assert (0 <= i);
  (i lsl 1) lor (match b with true -> 0 | false -> 1)

(* -------------------------------------------------------------------- *)
exception InvalidAIG of string

(* -------------------------------------------------------------------- *)
(* Load an aig file                                                     *)
let load (input : IO.input) : reg * (Set.String.t * string array) option =
  let parse_asuint =
    let re = Str.regexp "^[0-9]+$" in

    let doit (x : string) =
      if not (Str.string_match re x 0) then
        raise (InvalidAIG ("not a valid uint: " ^ x));
      int_of_string x           (* FIXME: overflow *)
    in fun x -> doit x in 

  let header = String.trim (IO.read_line input) in
  let header = Str.split (Str.regexp "[ \t]+") header in
  let header = Array.of_list header in

  if Array.length header <> 6 || header.(0) <> "aig" then
    raise (InvalidAIG "invalid header");

  let c_m = parse_asuint header.(1) in  (* maximum variable index *)
  let c_i = parse_asuint header.(2) in  (* number of inputs *)
  let c_l = parse_asuint header.(3) in  (* number of latches *)
  let c_o = parse_asuint header.(4) in  (* number of outputs *)
  let c_a = parse_asuint header.(5) in  (* number of AND gates *)

  (* We have c_l = 0 so /\ c_m = c_i + c_l + c_a 
   *
   * Hence: c_m = c_i + c_a
   *)

  if c_m <> c_i + c_l + c_a || c_l <> 0 then
    raise (InvalidAIG "invalid header (sum)");

  let outputs = ref [] in

  (* Reading outputs *)
  for _ = 1 to c_o do
    let output = String.trim (IO.read_line input) in
    let (_, u) as output = u2si (parse_asuint output) in

    if not (0 <= u && u <= c_m) then
      raise (InvalidAIG "invalid output");

    outputs := output :: !outputs
  done;

  let outputs = Array.of_list (List.rev !outputs) in

  (* Reading arguments of AND gate *)
  let read_uint () =
    let exception Done in

    let i, o = ref 0, ref 0 in
    try
      while true do
        assert (!o < 4);
        let d = IO.read_byte input in
        i := !i lor ((d land 0x7f) lsl (7 * !o));
        o := !o + 1;
        if (d land 0x80) = 0 then
          raise Done
      done;
      assert false
    with Done -> !i
  in


  let gates = List.fold_left (fun map -> function
    | 0 ->
       Map.add 0 false_ map

    | i when 0 < i && i <= c_i ->
        Map.add i (Aig.input (0, i-1)) map

    | i when c_i < i && i <= c_i + c_a ->
       let delta0 = read_uint () in
       let delta1 = read_uint () in

       if delta0 = 0 then
         raise (InvalidAIG "invalid delta0");

       (* delta0 = lhs - rhs0, delta1 = rhs0 - rhs1 *)

       let lhs  = 2 * i in
       let rhs0_ = lhs - delta0 in
       let rhs1_ = rhs0_ - delta1 in

       if lhs = c_i*2 + 2 then
         Format.eprintf "Lhs: %d | Rhs0: %d | Rhs1: %d@." lhs rhs0_ rhs1_;

       let (b1, u1) = try 
         u2si rhs0_
       with InvalidWire ->
         Format.eprintf "Invalid wire for rhs0 for params: lhs: %d | rhs0: %d | rhs1: %d@." lhs rhs0_ rhs1_; assert false
       in
       let (b2, u2) = try 
         u2si rhs1_ 
       with InvalidWire ->
         Format.eprintf "Invalid wire for rhs1 for params: lhs: %d | rhs0: %d | rhs1: %d@." lhs rhs0_ rhs1_; assert false
       in

       let n1 = Map.find u1 map in
       let n1 = if b1 then n1 else n1.neg in
       let n2 = Map.find u2 map in
       let n2 = if b2 then n2 else n2.neg in

       if not (u1 <= c_m && u2 <= c_m) then
         raise (InvalidAIG "invalid delta1");

       Map.add i (and_ n1 n2) map

    | _ ->
       assert false
  ) Map.empty (List.init (c_i + c_a + 1) (fun i -> i)) in

  (* Reading annotations *)
  let ainputs = Array.make c_i None in

  begin try
    while true do
      let exception Continue in

      try
        let line = String.trim (IO.read_line input) in

        if line = "" then
          raise Continue;
        if line = "c" then
          raise IO.No_more_input;

        if not (
          Str.string_match
            (Str.regexp "^i\\([0-9]+\\)[ \t]+\\(.*\\)$")
            line 0
        ) then raise (InvalidAIG ("invalid annotation: " ^ line));

        let s = Str.matched_group 2 line in
        let i = parse_asuint (Str.matched_group 1 line) in

        if not (i < c_i) then
          raise (InvalidAIG "invalid annotation (index)");

        if Option.is_some ainputs.(i) then
          raise (InvalidAIG "invalid annotation (dup. index)");

        ainputs.(i) <- Some s

      with Continue -> ()
    done

  with IO.No_more_input -> () end;

  let ainputs =
    if Array.for_all Option.is_none ainputs then
      None
    else if Array.exists Option.is_none ainputs then
      raise (InvalidAIG "invalid annotation (partial)")
    else
      let ainputs = Array.map Option.get ainputs in
      let keys = Set.String.of_array ainputs in

      if Set.String.cardinal keys <> Array.length ainputs then
        raise (InvalidAIG "invalid annotation (dup)");
      Some (keys, ainputs)
  in

  (* Construct network *)
  List.map (fun (b, i) ->
    if b then (Map.find i gates).neg else Map.find i gates
  ) (Array.to_list outputs), ainputs
