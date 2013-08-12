(* -------------------------------------------------------------------- *)
open EcUtils
open EcMaps
open EcPath
open EcTypes
open EcFol
open EcRing

(* -------------------------------------------------------------------- *)
module RState : sig
  type rstate

  val empty   : rstate
  val add     : form -> rstate -> int * rstate
  val get     : int -> rstate -> form option
  val current : rstate -> int
end = struct
  type rstate = {
    rst_map : int Mf.t;
    rst_inv : form Mint.t;
    rst_idx : int;
  }

  let empty = { rst_map = Mf.empty; rst_inv = Mint.empty; rst_idx = 0; }

  let add (form : form) (rmap : rstate) =
    match Mf.find_opt form rmap.rst_map with
    | Some i -> (i, rmap)
    | None ->
       let i = rmap.rst_idx+1 in
       let m = Mf  .add form i rmap.rst_map in
       let v = Mint.add i form rmap.rst_inv in
         (i, { rst_map = m; rst_inv = v; rst_idx = i; })

  let current (rmap : rstate) =
    rmap.rst_idx

  let get (i : int) (rmap : rstate) =
    Mint.find_opt i rmap.rst_inv
end

(* -------------------------------------------------------------------- *)
type ring = {
  r_type   : EcTypes.ty;
  r_zero   : path;
  r_one    : path;
  r_add    : path;
  r_opp    : path;
  r_mul    : path;
  r_exp    : path;
  r_sub    : path option;
  r_intmul : [`Embed | `NatMul of path];
}

(* -------------------------------------------------------------------- *)
let rapp r op args =
  let opty = toarrow (List.map f_ty args) r.r_type in
    f_app (f_op op [] opty) args r.r_type

let rzero r = rapp r r.r_zero []
let rone  r = rapp r r.r_one  []

let radd r e1 e2 = rapp r r.r_add [e1; e2]
let ropp r e     = rapp r r.r_opp [e]
let rmul r e1 e2 = rapp r r.r_mul [e1; e2]
let rexp r e  i  = rapp r r.r_exp [e; f_int i]

let rsub r e1 e2 =
  match r.r_sub with
  | None   -> radd r e1 (ropp r e2)
  | Some p -> rapp r p [e1; e2]

(* -------------------------------------------------------------------- *)
type cringop = Zero | One | Add | Opp | Sub | Mul | Exp | NatMul
type cring   = ring * (cringop Mp.t)

(* -------------------------------------------------------------------- *)
let cring_of_ring (r : ring) =
  let cr = [(r.r_zero, Zero);
            (r.r_one , One );
            (r.r_add , Add );
            (r.r_opp , Opp );
            (r.r_mul , Mul );
            (r.r_exp , Exp )]
  in

  let cr = List.fold_left (fun m (p, op) -> Mp.add p op m) Mp.empty cr in
  let cr = odfl cr (r.r_sub |> omap (fun p -> Mp.add p Sub cr)) in
  let cr = r.r_intmul |> (function `Embed -> cr | `NatMul p -> Mp.add p NatMul cr) in
    (r, cr)

(* -------------------------------------------------------------------- *)
let toring ((r, cr) : cring) (rmap : RState.rstate) (form : form) =
  let rmap = ref rmap in

  let int_of_form form = reffold (RState.add form) rmap in

  let rec doit form =
    match sform_of_form form with
    | SFop ((op, _), args) -> begin
        match Mp.find_opt op cr with
        | None -> abstract form
        | Some op -> begin
            match op,args with
            | Zero, []           -> PEc c0
            | One , []           -> PEc c1
            | Add , [arg1; arg2] -> PEadd (doit arg1, doit arg2)
            | Opp , [arg1]       -> PEsub (PEc c0, doit arg1)
            | Sub , [arg1; arg2] -> PEsub (doit arg1, doit arg2)
            | Mul , [arg1; arg2] -> PEmul (doit arg1, doit arg2)
            | Exp , [arg1; arg2] -> begin
                match arg2.f_node with
                | Fint n -> PEpow (doit arg1, n)
                | _ -> abstract form
            end
            | _, _ -> abstract form
        end
    end
    | SFint i when r.r_intmul = `Embed -> PEc (Big_int.big_int_of_int i)
    | _ -> abstract form

  and abstract form = PEX (int_of_form form) in

  let form = doit form in (form, !rmap)

(* -------------------------------------------------------------------- *)
let ofring ((r, _) : cring) (rmap : RState.rstate) (e : pol) : form =
  let rec doit idx e =
    match e with
    | Pc c -> begin
      let c = f_int (Big_int.int_of_big_int c) in (* FIXME: possible overflow *)
        match r.r_intmul with
        | `Embed    -> c
        | `NatMul p -> rapp r p [c]
    end

    | Pinj (j, e) -> doit (idx-j) e

    | PX (p, i, q) ->
        let f = oget (RState.get i rmap) in
        let f = match i with 1 -> f | _ -> rexp r f i in
        let f = if peq p (Pc c1) then f else rmul r (doit idx p) f in
        let f = if peq q (Pc c0) then f else radd r f (doit (idx-1) q) in
          f
  in
    doit (RState.current rmap) e

(* -------------------------------------------------------------------- *)
let ring_simplify (cr : cring) (eqs : (form * form) list) (form : form) =
  let map = ref RState.empty in
  let toring form = reffold (fun map -> toring cr map form) map in

  let form = toring form in
  let eqs  = List.map (fun (f1, f2) -> (toring f1, toring f2)) eqs in
    ofring cr !map (norm form eqs)

(* -------------------------------------------------------------------- *)
let ring_eq (cr : cring) (eqs : (form * form) list) (f1 : form) (f2 : form) =
  ring_simplify cr eqs (rsub (fst cr) f1 f2)
