(* Based on the PArray librairy of Jean Christophe Filiatre *)

(* Persistent arrays implemented using Backer's trick.

   A persistent array is a usual array (node Array) or a change into 
   another persistent array (node Diff). Invariant: any persistent array is a
   (possibly empty) linked list of Diff nodes ending on an Array node.

   As soon as we try to access a Diff, we reverse the linked list to move
   the Array node to the position we are accessing; this is achieved with
   the reroot function.
*)

type 'a t = 'a data ref
and 'a data =
  | Array of 'a array 
  | Diff of int * 'a * 'a t
  | DiffO of int * int * 'a array * 'a t

type 'a zip1 = 
  | Zdiff of int * 'a * 'a t
  | ZdiffO of int * int * 'a array * 'a t 

let rec unzip t' z = 
  match z with
  | [] -> ()
  | Zdiff(i,v,t) :: z ->
    begin match !t' with
    | Array a as n ->
      let v' = a.(i) in
      a.(i) <- v;
      t := n;
      t' := Diff (i, v', t)
    | _ -> assert false 
    end; 
    unzip t z
  | ZdiffO(s,len,c,t) :: z ->
    begin match !t' with
    | Array a as n ->
      for i = 0 to len - 1 do
        let j = s + i in
        let v' = a.(j) in
        a.(j) <- c.(i);
        c.(i) <- v'
      done;
      t := n;
      t' := DiffO (s,len, c, t)
    | _ -> assert false
    end;
    unzip t z
      

let rec rerootk t z = match !t with
  | Array _ -> unzip t z 
  | Diff (i, v, t') -> rerootk t' (Zdiff(i,v,t)::z)
  | DiffO(s,l,c,t') -> rerootk t' (ZdiffO(s,l,c,t)::z)

let reroot t = 
  match !t with
  | Array _ -> ()
  | _ -> rerootk t []
      
(* Array.array *)
type 'x array = 'x t

(* Array.empty *)
(*  let empty : 'x array = assert false (* TO FILL *) *)

(* Array.create *)
let create n v = ref (Array (Array.create n v))

(* Array.init *)
let init n f = ref (Array (Array.init n f))

(* Array._.[_] *)
let get t i = 
  match !t with
  | Array a -> a.(i)
  | _ -> 
    reroot t; 
    match !t with 
    | Array a -> a.(i) 
    | _ -> assert false 

let _dtlb_rb = get 

(* Array._.[_<-_] *)
let rec set t i v = 
  match !t with
  | Array a as n ->
    let old = a.(i) in
    if old == v then
      t
    else begin
      a.(i) <- v;
      let res = ref n in
      t := Diff (i, old, res);
      res
    end
  | _ -> reroot t; set t i v

let _dtlb_lsmn_rb = set

(* Array.write *)
let write dst dOff src sOff len = 
  reroot dst; 
  reroot src;
  match !dst, !src with
  | Array a as n, Array b ->
    begin
      let s = Array.sub a dOff len in
      Array.blit b sOff a dOff len;
      let res = ref n in
      dst := DiffO (dOff, len, s, res);
      res
    end
  | _, _ -> assert false

(* wrappers to apply an impure function from Array to a persistent array *)
let impure f t =
  match !t with 
  | Array a -> f a 
  | _ -> 
    rerootk t []; 
    match !t with 
    | Array a -> f a 
    | _ -> assert false 

 (* Array.length *)
let length t = impure Array.length t

(* Array.fold_left *)
let fold_left f t s = impure (Array.fold_left (fun s x -> f x s) s) t

(* Array.fold_right *)
let fold_right f s t = 
  impure (fun a -> Array.fold_right (fun x s -> f s x) a s) t

(* Array.sub *)
let sub t x y = 
 ref (Array (impure (fun a -> Array.sub a x y) t))
  
(* Array.|| *)
let brbr t1 t2 = 
 ref (Array (impure (fun a1 -> impure (Array.append a1) t2) t1))

(* Array.map2 *)
let map2 f t1 t2 = 
  let map2 f a1 a2 = 
    let len = min (Array.length a1) (Array.length a2) in
    Array.init len (fun i -> f a1.(i) a2.(i)) in
  ref (Array (impure (fun a1 -> impure (map2 f a1) t2) t1))
  
(* Array.map *)
let map f t = 
  ref (Array (impure (Array.map f) t))
  
(* Array.::: *)
let clclcl t x =
  ref (Array (impure (fun a -> Array.append a [|x|]) t))
  
(* Array._::_ *)
let _clcl_ x t = 
  ref (Array (impure (fun a -> Array.append [|x|] a) t))

  
  
 
  
 

