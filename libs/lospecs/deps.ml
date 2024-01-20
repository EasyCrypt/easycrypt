(* -------------------------------------------------------------------- *)
type symbol = string

(* -------------------------------------------------------------------- *)
type dep1 = Set.Int.t Map.String.t
type deps = dep1 Map.Int.t

(* -------------------------------------------------------------------- *)
let eq_dep1 (d1 : dep1) (d2 : dep1) : bool =
  Map.String.equal Set.Int.equal d1 d2

(* -------------------------------------------------------------------- *)
let eq_deps (d1 : deps) (d2 : deps) : bool = Map.Int.equal eq_dep1 d1 d2

(* -------------------------------------------------------------------- *)
let empty ~(size : int) : deps =
  0 --^ size |> Enum.map (fun i -> (i, Map.String.empty)) |> Map.Int.of_enum

(* -------------------------------------------------------------------- *)
let enlarge ~(min : int) ~(max : int) (d : deps) : deps =
  let change = function None -> Some Map.String.empty | Some _ as v -> v in

  min --^ max |> Enum.fold (fun d i -> Map.Int.modify_opt i change d) d

(* -------------------------------------------------------------------- *)
let clearout ~(min : int) ~(max : int) (d : deps) : deps =
  Map.Int.filter_map
    (fun i d1 -> Some (if min <= i && i < max then d1 else Map.String.empty))
    d

(* -------------------------------------------------------------------- *)
let restrict ~(min : int) ~(max : int) (d : deps) : deps =
  Map.Int.filter (fun i _ -> min <= i && i < max) d

(* -------------------------------------------------------------------- *)
let recast ~(min : int) ~(max : int) (d : deps) : deps =
  d |> restrict ~min ~max |> enlarge ~min ~max

(* -------------------------------------------------------------------- *)
let merge1 (d1 : dep1) (d2 : dep1) : dep1 =
  Map.String.merge
    (fun _ i1 i2 ->
      Some (Set.Int.union (i1 |? Set.Int.empty) (i2 |? Set.Int.empty)))
    d1 d2

(* -------------------------------------------------------------------- *)
let merge (d1 : deps) (d2 : deps) : deps =
  Map.Int.merge
    (fun _ m1 m2 ->
      Some (merge1 (m1 |? Map.String.empty) (m2 |? Map.String.empty)))
    d1 d2

(* -------------------------------------------------------------------- *)
let merge1_all (ds : dep1 Enum.t) : dep1 = Enum.reduce merge1 ds

(* -------------------------------------------------------------------- *)
let merge_all (ds : deps Enum.t) : deps = Enum.reduce merge ds

(* -------------------------------------------------------------------- *)
let copy ~(offset : int) ~(size : int) (x : symbol) : deps =
  0 --^ size
  |> Enum.map (fun i ->
         let di = Map.String.singleton x (Set.Int.singleton (i + offset)) in
         (i, di))
  |> Map.Int.of_enum

(* -------------------------------------------------------------------- *)
let chunk ~(csize : int) ~(count : int) (d : deps) : deps =
  0 --^ count
  |> Enum.map (fun ci ->
         let d1 =
           0 --^ csize
           |> Enum.map (fun i -> i + (ci * csize))
           |> Enum.map (fun i -> Map.Int.find_opt i d |> Option.default Map.String.empty)
           |> merge1_all
         in
         0 --^ csize |> Enum.map (fun i -> (i + (ci * csize), d1)))
  |> Enum.flatten |> Map.Int.of_enum

(* -------------------------------------------------------------------- *)
let perm ~(csize : int) ~(perm : int list) (d : deps) : deps =
  List.enum perm
  |> Enum.mapi (fun ci x ->
         Enum.map
           (fun i -> (i + (ci * csize), Map.Int.find_opt (i + (x * csize)) d |> Option.default Map.String.empty))
           (0 --^ csize))
  |> Enum.flatten |> Map.Int.of_enum

(* -------------------------------------------------------------------- *)
let collapse ~(csize : int) ~(count : int) (d : deps) : deps =
  0 --^ count
  |> Enum.map (fun ci ->
         let d1 =
           0 --^ csize
           |> Enum.map (fun i -> i + (ci * csize))
           |> Enum.map (fun i -> Map.Int.find_opt i d |> Option.default Map.String.empty)
           |> merge1_all
         in
         (ci, d1))
  |> Map.Int.of_enum

(* -------------------------------------------------------------------- *)
let merge_all_deps (d : deps) : dep1 =
  Map.Int.enum d |> Enum.map snd |> merge1_all

(* -------------------------------------------------------------------- *)
let constant ~(size : int) (d : dep1) : deps =
  0 --^ size |> Enum.map (fun i -> (i, d)) |> Map.Int.of_enum

(* -------------------------------------------------------------------- *)
let offset ~(offset : int) (d : deps) : deps =
  Map.Int.enum d |> Enum.map (fun (i, x) -> (i + offset, x)) |> Map.Int.of_enum

(* -------------------------------------------------------------------- *)
let split ~(csize : int) ~(count : int) (d : deps) : deps Enum.t =
  0 --^ count
  |> Enum.map (fun i ->
         Map.Int.filter (fun x _ -> csize * i <= x && x < csize * (i + 1)) d
         |> offset ~offset:(-i * csize))

(* -------------------------------------------------------------------- *)
let aggregate ~(csize : int) (ds : deps Enum.t) =
  Enum.foldi
    (fun i d1 d -> merge (offset ~offset:(i * csize) d1) d)
    (empty ~size:0) ds

(* ==================================================================== *)
type 'a pp = Format.formatter -> 'a -> unit

(* -------------------------------------------------------------------- *)
let pp_bitset (fmt : Format.formatter) (d : Set.Int.t) =
  Format.fprintf fmt "{%a}"
    (Format.pp_print_list
       ~pp_sep:(fun fmt () -> Format.fprintf fmt ", ")
       Format.pp_print_int)
    (Set.Int.elements d)

(* -------------------------------------------------------------------- *)
let pp_bitintv (fmt : Format.formatter) (d : (int * int) list) =
  Format.fprintf fmt "%a"
    (Format.pp_print_list
       ~pp_sep:(fun fmt () -> Format.fprintf fmt ", ")
       (fun fmt (i, j) -> Format.fprintf fmt "[%d..%d](%d)" i j (j - i + 1)))
    d

(* -------------------------------------------------------------------- *)
let bitintv_of_bitset (d : Set.Int.t) =
  let aout = ref [] in
  let current = ref None in

  d
  |> Set.Int.iter (fun i ->
         match !current with
         | None -> current := Some (i, i)
         | Some (v1, v2) ->
             if i = v2 + 1 then current := Some (v1, i)
             else (
               aout := (v1, v2) :: !aout;
               current := Some (i, i)));

  Option.may (fun (v1, v2) -> aout := (v1, v2) :: !aout) !current;

  List.rev !aout

(* -------------------------------------------------------------------- *)
let pp_dep1 (fmt : Format.formatter) (d : dep1) =
  Map.String.iter
    (fun x bits ->
      Format.fprintf fmt "%s -> %a@\n" x pp_bitintv (bitintv_of_bitset bits))
    d

(* -------------------------------------------------------------------- *)
let pp_deps (fmt : Format.formatter) (d : deps) =
  let display (v1, v2, d) =
    Format.fprintf fmt "[%d..%d](%d) -> @[@\n%a@]@\n" v1 v2
      (v2 - v1 + 1)
      pp_dep1 d
  in

  let current = ref None in

  Map.Int.iter
    (fun i d ->
      match !current with
      | None -> current := Some (i, i, d)
      | Some (v1, v2, d') ->
          if i = v2 + 1 && eq_dep1 d d' then current := Some (v1, i, d')
          else (
            display (v1, v2, d');
            current := Some (i, i, d)))
    d;

  Option.may display !current
