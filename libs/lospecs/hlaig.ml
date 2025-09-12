type node = Aig.node
type reg = Aig.reg

(* tdeps : int -> int set ; dependency for a single output bit 
           i |->  {j | output depends on bit j of var i }*)
type tdeps = (int, int Set.t) Map.t
(* tdblock (n, d) = merged dependencies as above for n bits 
  aka, the tdep represents dependencies for n bits rather than 1
*)
type tdblock = (int * tdeps)

module Hashtbl = Batteries.Hashtbl

module type SMTInstance = sig
  type bvterm

  exception SMTError
 
  (* Expected params: sort, value *)
  val bvterm_of_int : int -> int -> bvterm

  (* Expected params: sort, name *)
  val bvterm_of_name : int -> string -> bvterm

  (* argument must be of size 1, assert it true *)
  (* Should affect internal state of SMT *)
  val assert' : bvterm -> unit

  (* Check satisfiability of current asserts *)
  val check_sat : unit -> bool 

  (* equality over bitvectors, res is a size 1 bitvector *)
  val bvterm_equal : bvterm -> bvterm -> bvterm

  (* bvterm concat, res sort is sum of sorts *)
  val bvterm_concat : bvterm -> bvterm -> bvterm

  (* bvand *)
  val lognot : bvterm -> bvterm

  (* bvnot *)
  val logand : bvterm -> bvterm -> bvterm

  val get_value : bvterm -> bvterm

  val pp_term : Format.formatter -> bvterm -> unit
end

module type SMTInterface = sig
  val circ_equiv : ?inps:(int * int) list -> reg -> reg -> node ->  bool

  val circ_sat : ?inps:(int * int) list -> node -> bool

  val circ_taut : ?inps:(int * int) list -> node -> bool
end

(* TODO Add model printing for circ_sat and circ_taut *)
(* Assumes circuit inputs have already been appropriately renamed *)
module MakeSMTInterface(SMT: SMTInstance) : SMTInterface = struct
  let circ_equiv ?(inps: (int * int) list option) (r1 : Aig.reg) (r2 : Aig.reg) (pcond : Aig.node) : bool =
    if not ((Array.length r1 > 0) && (Array.length r2 > 0)) then
      (Format.eprintf "Sizes differ in circ_equiv"; false)
    else
    let bvvars : SMT.bvterm Map.String.t ref = ref Map.String.empty in

    let rec bvterm_of_node : Aig.node -> SMT.bvterm =
      let cache = Hashtbl.create 0 in
  
      let rec doit (n : Aig.node) =
        let mn = 
          match Hashtbl.find_option cache (Int.abs n.id) with
          | None ->
            let mn = doit_r n.gate in
            Hashtbl.add cache (Int.abs n.id) mn;
            mn
          | Some mn -> 
            mn
        in 
          if 0 < n.id then mn else SMT.lognot mn

      and doit_r (n : Aig.node_r) = 
        match n with
        | False -> SMT.bvterm_of_int 1 0 
        | Input v -> let name = ("BV_" ^ (fst v |> string_of_int) ^ "_" ^ (Printf.sprintf "%X" (snd v))) in
        begin 
          match Map.String.find_opt name !bvvars with
          | None ->
            bvvars := Map.String.add name (SMT.bvterm_of_name 1 name) !bvvars;
            Map.String.find name !bvvars 
          | Some t -> t
        end
        | And (n1, n2) -> SMT.logand (doit n1) (doit n2)

      in fun n -> doit n
    in 
  
    let bvterm_of_reg (r: Aig.reg) : _ =
      Array.map bvterm_of_node r |> Array.reduce (fun acc b -> SMT.bvterm_concat b acc)
    in 

    let bvinpt1 = (bvterm_of_reg r1) in
    let bvinpt2 = (bvterm_of_reg r2) in
    let formula = SMT.bvterm_equal bvinpt1 bvinpt2 in
    let pcond = (bvterm_of_node pcond) in
    let inps = Option.bind inps (fun l -> 
      if List.is_empty l then None
      else Some l
    ) in

    let inps = Option.map (fun inps ->
      List.map (fun (id,sz) -> 
      List.init sz (fun i -> ("BV_" ^ (id |> string_of_int) ^ "_" ^ (Printf.sprintf "%X" (i))))) inps 
    ) inps in
    let inps = Option.map (fun inps ->
    List.map (List.map (fun name -> match Map.String.find_opt name !bvvars with
    | Some bv -> bv
    | None -> SMT.bvterm_of_name 1 name)) inps) inps
    in
    let bvinp = Option.map (fun inps -> 
      List.map (fun i -> List.reduce (SMT.bvterm_concat) i) inps) inps 
    in

    begin
      SMT.assert' @@ SMT.logand pcond (SMT.lognot formula);
      if SMT.check_sat () = false then true 
      else begin
        Format.eprintf "bvout1: %a@."  SMT.pp_term (SMT.get_value bvinpt1);
        Format.eprintf "bvout2: %a@."  SMT.pp_term (SMT.get_value bvinpt2);
        Format.eprintf "Terms in formula: ";
        List.iter (Format.eprintf "%s ") (List.of_enum @@ Map.String.keys !bvvars);
        Format.eprintf "@\n";
        Option.may (fun bvinp ->
        List.iteri (fun i bv -> 
        Format.eprintf "input[%d]: %a@." i SMT.pp_term (SMT.get_value bv)        
        ) bvinp) bvinp;
        false
      end
    end


  let circ_sat ?(inps: (int * int) list option) (n : Aig.node) : bool =
    let bvvars : SMT.bvterm Map.String.t ref = ref Map.String.empty in

    let rec bvterm_of_node : Aig.node -> SMT.bvterm =
      let cache = Hashtbl.create 0 in
  
      let rec doit (n : Aig.node) =
        let mn = 
          match Hashtbl.find_option cache (Int.abs n.id) with
          | None ->
            let mn = doit_r n.gate in
            Hashtbl.add cache (Int.abs n.id) mn;
            mn
          | Some mn -> 
            mn
        in 
          if 0 < n.id then mn else SMT.lognot mn

      and doit_r (n : Aig.node_r) = 
        match n with
        | False -> SMT.bvterm_of_int 1 0 
        | Input v -> let name = ("BV_" ^ (fst v |> string_of_int) ^ "_" ^ (Printf.sprintf "%05X" (snd v))) in
        begin 
          match Map.String.find_opt name !bvvars with
          | None ->
            bvvars := Map.String.add name (SMT.bvterm_of_name 1 name) !bvvars;
            Map.String.find name !bvvars 
          | Some t -> t
        end
        | And (n1, n2) -> SMT.logand (doit n1) (doit n2)

      in fun n -> doit n
    in 
  
    let form = bvterm_of_node n in 

    let inps = Option.bind inps (fun l -> 
      if List.is_empty l then None
      else Some l
    ) in

    let inps = Option.map (fun inps ->
      List.map (fun (id,sz) -> 
      List.init sz (fun i -> ("BV_" ^ (id |> string_of_int) ^ "_" ^ (Printf.sprintf "%05X" (i))))) inps 
    ) inps in
    let inps = Option.map (fun inps ->
    List.map (List.map (fun name -> match Map.String.find_opt name !bvvars with
    | Some bv -> bv
    | None -> SMT.bvterm_of_name 1 name)) inps) inps
    in
    let bvinp = Option.map (fun inps -> 
      List.map (fun i -> List.reduce (SMT.bvterm_concat) i) inps) inps 
    in

    begin
      SMT.assert' @@ form;
      if SMT.check_sat () = true then 
      begin
        Format.eprintf "Input BVVars: ";
        let () = Enum.iter (Format.eprintf "%s, ") (Map.String.keys !bvvars) in
        Format.eprintf "@.";
        Option.may (fun bvinp -> List.iteri (fun i bv -> 
            Format.eprintf "input[%d]: %a@." i SMT.pp_term (SMT.get_value bv)        
        ) bvinp) bvinp;
        true 
      end
      else false
    end
  
  let circ_taut ?inps (n: Aig.node) : bool =
    not @@ circ_sat ?inps (Aig.neg n)

end


let makeBWZinstance () : (module SMTInstance) = 
  let module B = Bitwuzla.Once () in
  let open B in
  
  (module struct
  type bvterm = Term.Bv.t 

  exception SMTError
  
  let bvterm_of_int (sort: int) (v: int) : bvterm =
    Term.Bv.of_int (Sort.bv sort) v
  

  let bvterm_of_name (sort: int) (name: string) : bvterm =
    Term.const (Sort.bv sort) name
  

  let assert' (f: bvterm) : unit =
    assert' f
  

  let check_sat () : bool =
    match check_sat () with
    | Sat -> true
    | Unsat -> false
    | Unknown -> raise SMTError
   

  let bvterm_equal (bv1: bvterm) (bv2: bvterm) : bvterm =
    Term.equal bv1 bv2
  

  let bvterm_concat (bv1: bvterm) (bv2: bvterm) : bvterm =
    Term.Bv.concat [|bv1; bv2|]
  

  let lognot (bv: bvterm) : bvterm =
    Term.Bv.lognot bv
  

  let logand (bv1: bvterm) (bv2: bvterm) : bvterm =
    Term.Bv.logand bv1 bv2
  

  let get_value (bv: bvterm) : bvterm =
    (get_value bv :> bvterm)
  

  let pp_term (fmt: Format.formatter) (bv: bvterm) : unit =
    Term.pp fmt bv

  end : SMTInstance)


let makeBWZinterface () : (module SMTInterface) =
  (module MakeSMTInterface ((val makeBWZinstance () : SMTInstance)))


let of_int (i:int) : reg = 
  (* Number of bits the integer occupies *)
  let rec log2up (i: int) : int = 
  match i with
  | 0 | 1 -> 1
  | _ -> 1 + log2up (i/2) 
  in
  Circuit.of_int ~size:(log2up i) i

(* ------------------------------------------------------------------------------- *)
(* FIXME: CHECK THIS *)
let rec inputs_of_node : _ -> Aig.var Set.t =
  let cache : (int, Aig.var Set.t) Hashtbl.t = Hashtbl.create 0 in
  
  let rec doit (n : Aig.node) : Aig.var Set.t =
    match Hashtbl.find_option cache (Int.abs n.id) with
    | None ->
      let mn = doit_r n.gate in
      Hashtbl.add cache (Int.abs n.id) mn;
      mn
    | Some mn -> 
      mn

  and doit_r (n : Aig.node_r) = 
    match n with
    | False -> Set.empty
    | Input v -> Set.singleton v
    | And (n1, n2) -> Set.union (doit n1) (doit n2)

  in fun n -> doit n

(* ------------------------------------------------------------------------------- *)
let inputs_of_reg (r : Aig.reg) : Aig.var Set.t =
  Array.fold_left (fun acc x -> Set.union acc (inputs_of_node x)) Set.empty r

(* ==================================================================== *)
let rec dep : _ -> tdeps = 
  let cache : (int, tdeps) Hashtbl.t = Hashtbl.create 0 in

  let rec doit (n: Aig.node) : tdeps = 
    match Hashtbl.find_option cache (Int.abs n.id) with
    | None -> let mn = doit_r n.gate in
      Hashtbl.add cache (Int.abs n.id) mn;
      mn 
    | Some mn -> 
      mn

  and doit_r (n: Aig.node_r) =
    match n with
    | False -> Map.empty
    | Input (v, i) -> Map.add v (Set.add i (Set.empty)) Map.empty
    | And (n1, n2) -> Map.union_stdlib (fun k s1 s2 -> Some (Set.union s1 s2)) (doit n1) (doit n2)

  in fun n -> doit n

let deps (n: reg) : tdeps array = 
  Array.map dep n 

let block_deps (d: tdeps array) : tdblock list =
  let drop_while_count (f: 'a -> bool) (l: 'a list) : int * ('a list) =
    let rec doit (n: int) (l: 'a list) = 
      match l with
      | [] -> (n, [])
      | a::l' -> if f a then doit (n+1) l' else (n, l)
    in
    let n, tl = doit 0 l in
    (n, tl)
  in
  let rec decompose (l: tdeps list) : tdblock list =
    match l with
    | [] -> []
    | h::_ -> let n, l' = 
      (drop_while_count (fun a -> Map.equal (Set.equal) h a) l) in
      (n, h)::(decompose l')
  in
  decompose (Array.to_list d)

let blocks_indep ((_,b):tdblock) ((_,d):tdblock) : bool =
  let keys = Set.intersect (Set.of_enum @@ Map.keys b) (Set.of_enum @@ Map.keys d) in
  let intersects = Set.map (fun k -> 
    let b1 = Map.find k b in
    let d1 = Map.find k d in
    (Set.cardinal @@ Set.intersect b1 d1) = 0
  ) keys in
  Set.fold (&&) intersects true

let block_list_indep (bs: tdblock list) : bool =
  let rec doit (bs: tdblock list) (acc: tdblock list) : bool =
   match bs with
   | [] -> true
   | b::bs -> List.for_all (blocks_indep b) acc && doit bs (b::acc)
  in
  doit bs []

let merge_deps (d1: tdeps) (d2: tdeps) : tdeps = 
    Map.union_stdlib (fun _ a b -> Option.some (Set.union a b)) d1 d2

let split_deps (n: int) (d: tdeps array) : tdblock list =
  assert (Array.length d mod n = 0);
  let combine (d: tdeps list) : tdeps =
    List.reduce merge_deps d
  in
  let rec aggregate (acc: tdblock list) (d: tdeps array) : tdblock list =
    match d with
    | [| |] -> acc
    | _ -> (aggregate ((n, combine (Array.head d n |> Array.to_list))::acc) (Array.tail d n))
  in
  List.rev @@ aggregate [] d

let check_dep_width ?(eq=false) (n: int) (d: tdeps) : bool =
  Map.fold (fun s acc -> let m = (Set.cardinal s) in
    if eq then
      acc && (n = m)
    else
      acc && (m <= n)
    ) d true

(* maybe optimize this? *)
let tdblock_of_tdeps (d: tdeps list) : tdblock =
  (List.length d, List.reduce merge_deps d)

(* 
  Take a list of blocks and drop all but the first block if the 
  sizes are the same and the dependecy amounts are the same
*)
let compare_dep_size (a: tdeps) (b: tdeps) : bool =
  (Map.fold (fun s acc -> acc + (Set.cardinal s)) a 0) =
  (Map.fold (fun s acc -> acc + (Set.cardinal s)) b 0)   

let compare_tdblocks ((na, da): tdblock) ((nb, db): tdblock) : bool =
  (na = nb) && compare_dep_size da db

let collapse_blocks (d: tdblock list) : tdblock option = 
  match d with
  | [] -> None
  | h::t -> 
    List.fold_left 
    (fun a b -> 
      match a with
      | None -> None
      | Some a -> if compare_tdblocks a b 
                  then Some a else None) 
    (Some h) t

(* -------------------------------------------------------------------- *)
let rec pp_node ?(namer=string_of_int) (fmt : Format.formatter) (n : node) =
  let pp_node = pp_node ~namer in
  match n with
  | { gate = False; id } when 0 < id ->
    Format.fprintf fmt "⊥"

  | { gate = False; } ->
    Format.fprintf fmt "⊤"

  | { gate = Input (v, i); id; } ->
    let s = namer v in
    Format.fprintf fmt "%s%s#%0.4x"
      (if 0 < id then "" else "¬") s i

  | { gate = And (n1, n2); id; } when 0 < id ->
    Format.fprintf fmt "(%a) ∧ (%a)" pp_node n1 pp_node n2

  | { gate = And (n1, n2); } ->
    Format.fprintf fmt "¬((%a) ∧ (%a))" pp_node n1 pp_node n2

let pp_dep ?(namer = string_of_int) (fmt : Format.formatter) (d: tdeps) : unit =
  let print_set fmt s = Set.iter (Format.fprintf fmt "%d ") s in
  Map.iter (fun id ints -> Format.fprintf fmt "%s: %a@." (namer id) print_set ints) d

let pp_deps ?(namer = string_of_int) (fmt: Format.formatter) (ds: tdeps list) : unit = 
  List.iteri (fun i d -> Format.fprintf fmt "Output #%d:@.%a@." i (pp_dep ~namer) d) ds

let pp_bdep ?(start_index = 0) ?(oname="") ?(namer=string_of_int) (fmt: Format.formatter) ((n, d): tdblock) : unit =
  Format.fprintf fmt "[%d-%d]%s:@." start_index (start_index+n-1) oname;
  pp_dep ~namer fmt d

let pp_bdeps ?(oname="") ?(namer=string_of_int) (fmt: Format.formatter) (bs: tdblock list) : unit =
  List.fold_left (fun acc (n,d) -> (pp_bdep ~start_index:acc ~oname ~namer fmt (n,d)); acc + n) 0 bs |> ignore

(* -------------------------------------------------------------------- *)
let zpad (n: int) (r: Aig.reg)  = 
  if Array.length r < n then
    Array.append r (Array.init (n - (Array.length r)) (fun _ -> Aig.false_))
  else r
