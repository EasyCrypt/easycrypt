(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2017 - Inria
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcUtils
open EcMaps
open EcPath
open EcTypes
open EcFol
open EcDecl
open EcEnv
open EcRing
open EcField

module BI = EcBigInt

open EcBigInt.Notations

(* -------------------------------------------------------------------- *)
module RState : sig
  type rstate

  val empty   : rstate
  val add     : LDecl.hyps -> form -> rstate -> int * rstate
  val get     : int -> rstate -> form option
  val update  : rstate -> int list -> form list -> rstate

end = struct
  type rstate = {
    rst_map : int Mf.t;
    rst_inv : form Mint.t;
    rst_idx : int;
  }

  let empty = { rst_map = Mf.empty; rst_inv = Mint.empty; rst_idx = 0; }

  exception Found of int

  let find_alpha hyps form map =
    match Mf.find_opt form map with
    | Some i -> Some i
    | None ->
      try
        Mf.iter (fun f i ->
          if EcReduction.is_alpha_eq hyps f form then raise (Found i)) map;
        None
      with Found i -> Some i

  let add hyps (form : form) (rmap : rstate) =
    let res =
      match find_alpha hyps form rmap.rst_map with
      | Some i -> (i, rmap)
      | None ->
        let i = rmap.rst_idx+1 in
        let m = Mf  .add form i rmap.rst_map in
        let v = Mint.add i form rmap.rst_inv in
        (i, { rst_map = m; rst_inv = v; rst_idx = i; }) in
    res

  let get (i : int) (rmap : rstate) =
    Mint.find_opt i rmap.rst_inv

  let update1 rmap i f' =
    match get i rmap with
    | Some f ->
      {rmap with
        rst_map = Mf.add f' i (Mf.remove f rmap.rst_map);
        rst_inv = Mint.add i f' rmap.rst_inv}
    | None -> rmap

  let update rmap li lf = List.fold_left2 update1 rmap li lf

end

(* -------------------------------------------------------------------- *)
type eq = form * form

(* -------------------------------------------------------------------- *)
let rapp r op args =
  let opty = toarrow (List.map f_ty args) r.r_type in
    f_app (f_op op [] opty) args r.r_type

let rzero r = rapp r r.r_zero []
let rone  r = rapp r r.r_one  []

let radd r e1 e2 = rapp r r.r_add [e1; e2]
let ropp r e     =
  match r.r_opp with
  | Some opp -> rapp r opp [e]
  | None -> assert (r.r_kind = `Boolean); e

let rmul r e1 e2 = rapp r r.r_mul [e1; e2]

let rexp r e i  =
  match r.r_exp with
  | Some r_exp ->
      rapp r r_exp [e; f_int i]

  | None ->
      let rec aux exp i =
        if BI.equal i BI.one then exp else
          let x = aux exp (BI.rshift i 1) in
          match BI.parity i with
          | `Even -> rmul r x x
          | `Odd  -> rmul r exp (rmul r x x)
      in assert (BI.one <=^ i); aux e i

let rsub r e1 e2 =
  match r.r_sub with
  | None   -> radd r e1 (ropp r e2)
  | Some p -> rapp r p [e1; e2]

let rofint r i =
  match r.r_embed with
  | `Direct  -> f_int i
  | `Embed p -> rapp r p [f_int i]
  | `Default ->
      let rec aux i =
        if BI.equal i BI.one then rone r else
          let x = aux (BI.rshift i 1) in
          match BI.parity i with
          | `Even -> radd r x x
          | `Odd  -> radd r (rone r) (radd r x x)
      in
        match BI.sign i with
        | n when n > 0 -> aux i
        | n when n < 0 -> ropp r (aux (~^ i))
        | _ -> rzero r

(* -------------------------------------------------------------------- *)
let fzero  f = rzero  f.f_ring
let fone   f = rone   f.f_ring
let fadd   f = radd   f.f_ring
let fopp   f = ropp   f.f_ring
let fmul   f = rmul   f.f_ring
let fexp   f = rexp   f.f_ring
let fsub   f = rsub   f.f_ring
let fofint f = rofint f.f_ring

let finv f e = rapp f.f_ring f.f_inv [e]

let fdiv f e1 e2 =
  match f.f_div with
  | None   -> fmul f e1 (finv f e2)
  | Some p -> rapp f.f_ring p [e1; e2]

(* -------------------------------------------------------------------- *)
let emb_rzero r = rofint r BI.zero
let emb_rone  r = rofint r BI.one

let emb_fzero r = emb_rzero r.f_ring
let emb_fone  r = emb_rone  r.f_ring

(* -------------------------------------------------------------------- *)
type cringop = [`Zero | `One | `Add | `Opp | `Sub | `Mul | `Exp | `OfInt]
type cring   = ring * (cringop Mp.t)

(* -------------------------------------------------------------------- *)
type cfieldop = [cringop | `Inv | `Div]
type cfield   = field * (cfieldop Mp.t)

(* -------------------------------------------------------------------- *)
let cring_of_ring (r : ring) : cring =
  let cr = [(r.r_zero, `Zero);
            (r.r_one , `One );
            (r.r_add , `Add );
            (r.r_mul , `Mul );]
  in

  let cr = List.fold_left (fun m (p, op) -> Mp.add p op m) Mp.empty cr in
  let cr = odfl cr (r.r_opp |> omap (fun p -> Mp.add p `Opp cr)) in
  let cr = odfl cr (r.r_sub |> omap (fun p -> Mp.add p `Sub cr)) in
  let cr = odfl cr (r.r_exp |> omap (fun p -> Mp.add p `Exp cr)) in
  let cr = r.r_embed |>
      (function (`Direct | `Default) -> cr | `Embed p -> Mp.add p `OfInt cr) in
    (r, cr)

let ring_of_cring (cr:cring) = fst cr

(* -------------------------------------------------------------------- *)
let cfield_of_field (r : field) : cfield =
  let cr = (snd (cring_of_ring r.f_ring) :> cfieldop Mp.t) in
  let cr = Mp.add r.f_inv `Inv cr in
  let cr = odfl cr (r.f_div |> omap (fun p -> Mp.add p `Div cr)) in
    (r, cr)

let field_of_cfield (cr:cfield) : field = fst cr

(* -------------------------------------------------------------------- *)
let toring hyps ((r, cr) : cring) (rmap : RState.rstate) (form : form) =
  let rmap = ref rmap in

  let int_of_form form = reffold (RState.add hyps form) rmap in

  let rec doit form =
    let o, args = destr_app form in
    match o.f_node with
    | Fop (op, _) -> begin
        match Mp.find_opt op cr with
        | None -> abstract form
        | Some op -> begin
          match op,args with
          | `Zero, []           -> PEc c0
          | `One , []           -> PEc c1
          | `Add , [arg1; arg2] -> PEadd (doit arg1, doit arg2)
          | `Opp , [arg1]       -> PEopp (doit arg1)
          | `Sub , [arg1; arg2] -> PEsub (doit arg1, doit arg2)
          | `Mul , [arg1; arg2] -> PEmul (doit arg1, doit arg2)
          | `Exp , [arg1; arg2] -> begin
            match arg2.f_node with
            | Fint n -> PEpow (doit arg1, n)
            | _ -> abstract form
          end
          | `OfInt, [arg1] -> of_int arg1

          | _, _ -> abstract form
        end
    end
    | Fint i when r.r_embed = `Direct -> PEc i
    | _ -> abstract form

  and of_int f =
    let abstract () =
      match r.r_embed with
      | `Direct | `Default -> abstract f
      | `Embed p -> abstract (rapp r p [f])
    in
      match f.f_node with
      | Fint n -> PEc n
      | Fapp ({f_node = Fop (p,_)}, [a1; a2]) -> begin
          match op_kind p with
          | Some `Int_add -> PEadd (of_int a1, of_int a2)
          | Some `Int_mul -> PEmul (of_int a1, of_int a2)
          | Some `Int_pow -> begin
              match a2.f_node with
              | Fint n when 0 <= BI.sign n -> PEpow (of_int a1, n)
              | _ -> abstract ()
          end
          | _ -> abstract ()
        end
      | Fapp ({f_node = Fop (p,_)}, [a]) -> begin
          match op_kind p with
          | Some `Int_opp -> PEsub (PEc c0, of_int a)
          | _ -> abstract ()
        end
      | _ -> abstract ()

  and abstract form = PEX (int_of_form form) in

  let form = doit form in (form, !rmap)

(* -------------------------------------------------------------------- *)
let tofield hyps ((r, cr) : cfield) (rmap : RState.rstate) (form : form) =
  let rmap = ref rmap in

  let int_of_form form = reffold (RState.add hyps form) rmap in

  let rec doit form =
    let o, args = destr_app form in
    match o.f_node with
    | Fop(op, _) -> begin
        match Mp.find_opt op cr with
        | None -> abstract form
        | Some op -> begin
          match op,args with
          | `Zero, []           -> FEc c0
          | `One , []           -> FEc c1
          | `Add , [arg1; arg2] -> FEadd (doit arg1, doit arg2)
          | `Opp , [arg1]       -> FEopp (doit arg1)
          | `Sub , [arg1; arg2] -> FEsub (doit arg1, doit arg2)
          | `Mul , [arg1; arg2] -> FEmul (doit arg1, doit arg2)
          | `Inv , [arg1]       -> FEinv (doit arg1)
          | `Div , [arg1; arg2] -> FEdiv (doit arg1, doit arg2)
          | `Exp , [arg1; arg2] -> begin
            match arg2.f_node with
              (* TODO: missing case for n < 0 *)
            | Fint n -> FEpow (doit arg1, n)
            | _ -> abstract form
          end
          | `OfInt, [arg1] -> of_int arg1
          | _, _ -> abstract form
        end
    end
    | Fint i when r.f_ring.r_embed = `Direct -> FEc i
    | _ -> abstract form

  and of_int f =
    let abstract () =
      match r.f_ring.r_embed with
      | `Direct | `Default -> abstract f
      | `Embed p -> abstract (rapp r.f_ring p [f])
    in

    match f.f_node with
    | Fint n -> FEc n
    | Fapp ({f_node = Fop (p,_)}, [a1; a2]) -> begin
        match op_kind p with
        | Some `Int_add -> FEadd (of_int a1, of_int a2)
        | Some `Int_mul -> FEmul (of_int a1, of_int a2)
        | Some `Int_pow -> begin
          match a2.f_node with
          | Fint n when 0 <= BI.sign n -> FEpow (of_int a1, n)
          | _ -> abstract ()
          end
        | _ -> abstract ()
      end
    | Fapp({f_node = Fop (p,_)}, [a]) -> begin
        match op_kind p with
        | Some `Int_opp -> FEsub (FEc c0, of_int a)
        | _ -> abstract ()
      end
    | _ -> abstract ()

  and abstract form = FEX (int_of_form form) in

  let form = doit form in (form, !rmap)

(* -------------------------------------------------------------------- *)
let rec ofring (r:ring) (rmap:RState.rstate) (e:pexpr) : form =
  match e with
  | PEc c -> rofint r c
  | PEX idx -> oget (RState.get idx rmap)
  | PEadd(p1,p2) -> radd r (ofring r rmap p1) (ofring r rmap p2)
  | PEsub(p1,p2) -> rsub r (ofring r rmap p1) (ofring r rmap p2)
  | PEmul(p1,p2) -> rmul r (ofring r rmap p1) (ofring r rmap p2)
  | PEopp p1     -> ropp r (ofring r rmap p1)
  | PEpow(p1,i)  -> rexp r (ofring r rmap p1) i

(* -------------------------------------------------------------------- *)
let norm_pe_of_ring (cr : EcDecl.ring) =
  match cr.r_kind with
  | `Boolean -> Bring.norm_pe
  | `Integer -> Iring.norm_pe

  | `Modulus (c, p) ->
      let module M = struct let c = c let p = p end in
      let module C = EcRing.Cmod(M) in
      let module R = EcRing.Make(C) in
      R.norm_pe

(* -------------------------------------------------------------------- *)
let ring_simplify_pe (cr:cring) peqs pe =
  norm_pe_of_ring (fst cr) pe peqs

let ring_simplify todo (cr : cring) (eqs : eq list) (form : form) =
  let map = ref RState.empty in
  let toring form = reffold (fun map -> toring todo cr map form) map in
  let form = toring form in
  let eqs  = List.map (fun (f1, f2) -> (toring f1, toring f2)) eqs in
  ofring (fst cr) !map (ring_simplify_pe cr eqs form)

(* -------------------------------------------------------------------- *)
let ring_eq todo (cr : cring) (eqs : eq list) (f1 : form) (f2 : form) =
  ring_simplify todo cr eqs (rsub (fst cr) f1 f2)

(* -------------------------------------------------------------------- *)
let get_field_equation (f1, f2) =
  match fnorm f1, fnorm f2 with
  | (n, PEc l, []), (m, PEc r, []) when (ceq l c1 && ceq r c1) -> Some (n, m)
  | _ -> None

(* -------------------------------------------------------------------- *)
let field_eq hyps (cr : cfield) (eqs : eq list) (f1 : form) (f2 : form) =
  let map = ref RState.empty in

  let tofield form = reffold (fun map -> tofield hyps cr map form) map in
  let ofring  form = ofring (fst cr).f_ring !map form in

  let (f1, f2) = (tofield f1, tofield f2) in

  let (num1, denum1, cond1) = fnorm f1 in
  let (num2, denum2, cond2) = fnorm f2 in

  let eqs = List.map (fun (f1, f2) -> (tofield f1, tofield f2)) eqs in
  let eqs = List.pmap get_field_equation eqs in

  let norm = norm_pe_of_ring (fst cr).f_ring in
  let norm form = ofring (norm form eqs) in

  let num1   = norm num1   in
  let num2   = norm num2   in
  let denum1 = norm denum1 in
  let denum2 = norm denum2 in
  let cond1  = List.map norm cond1 in
  let cond2  = List.map norm cond2 in

    (cond1 @ cond2, ((num1, num2), (denum1, denum2)))

(* -------------------------------------------------------------------- *)
let rec offield (r:field) (rmap:RState.rstate) (e:fexpr) : form =
  match e with
  | FEc c        -> fofint r c
  | FEX idx      -> oget (RState.get idx rmap)
  | FEadd(p1,p2) -> fadd r (offield r rmap p1) (offield r rmap p2)
  | FEsub(p1,p2) -> fsub r (offield r rmap p1) (offield r rmap p2)
  | FEmul(p1,p2) -> fmul r (offield r rmap p1) (offield r rmap p2)
  | FEopp p1     -> fopp r (offield r rmap p1)
  | FEpow(p1,i)  -> fexp r (offield r rmap p1) i
  | FEinv p1     -> finv r (offield r rmap p1)
  | FEdiv(p1,p2) -> fdiv r (offield r rmap p1) (offield r rmap p2)

let field_simplify_pe (cr:cfield) peqs pe =
  let (num,denum,cond) = fnorm pe in
  let norm = norm_pe_of_ring (fst cr).f_ring in
  let norm f = norm f peqs in
  (List.map norm cond, (norm num, norm denum))

let field_simplify hyps (cr : cfield) (eqs : eq list) (f : form) =
  let map = ref RState.empty in

  let tofield form = reffold (fun map -> tofield hyps cr map form) map in
  let ofring  form = ofring (fst cr).f_ring !map form in

  let (num, denum, cond) = fnorm (tofield f) in
  let eqs = List.map (fun (f1, f2) -> (tofield f1, tofield f2)) eqs in
  let eqs = List.pmap get_field_equation eqs in

  let norm = norm_pe_of_ring (fst cr).f_ring in
  let norm form = ofring (norm form eqs) in
  (List.map norm cond, (norm num, norm denum))


