(* -------------------------------------------------------------------- *)
open Lospecs

(* -------------------------------------------------------------------- *)
let _ =
  let dont_type = false in
  let prog = Io.parse IO.stdin in
  if dont_type then Format.eprintf "%a@." Ptree.pp_pprogram prog
  else Typing.tt_program Typing.Env.empty prog |> (fun _ -> ())
  (*
    let vars = Typing.tt_program Typing.Env.empty prog in
    Format.eprintf "%a@.%a@." Ptree.pp_pprogram prog
      (fun fmt a (* print vars *) ->
        Format.pp_print_list
          ~pp_sep:(fun fmt () -> Format.fprintf fmt "@.")
          (fun fmt (a, b) -> Format.fprintf fmt "%s: %a" a Typing.pp_atype b)
          fmt a)
      vars
*)
(* -------------------------------------------------------------------- *)
module List : sig
  include module type of List

  val as_seq2 : 'a list -> 'a * 'a
  val paired : 'a list -> ('a * 'a) list
end = struct
  include List

  let as_seq2 (xs : 'a list) : 'a * 'a =
    match xs with [ x; y ] -> (x, y) | _ -> assert false

  let rec paired (xs : 'a list) : ('a * 'a) list =
    match xs with
    | [] -> []
    | v1 :: v2 :: xs -> (v1, v2) :: paired xs
    | _ -> assert false
end

(* -------------------------------------------------------------------- *)
module Enum : sig
  include module type of Enum

  val paired : 'a t -> ('a * 'a) t
end = struct
  include Enum

  let paired (e : 'a t) : ('a * 'a) t =
    let next () =
      try
        let v1 = Enum.get_exn e in
        let v2 = Enum.get_exn e in
        (v1, v2)
      with Not_found -> raise Enum.No_more_elements
    in
    Enum.from next
end

(* -------------------------------------------------------------------- *)
let main () =
  let open Deps in
  let f0 = copy ~offset:(0 * 256) ~size:256 "a" in
  (* f0 = a[u256 4*i    ]; *)
  let f1 = copy ~offset:(1 * 256) ~size:256 "a" in
  (* f1 = a[u256 4*i + 1]; *)
  let f2 = copy ~offset:(2 * 256) ~size:256 "a" in
  (* f2 = a[u256 4*i + 2]; *)
  let f3 = copy ~offset:(3 * 256) ~size:256 "a" in

  (* f3 = a[u256 4*i + 3]; *)

  (* v = 2^16 inv mod q *)
  let f0 = chunk ~csize:16 ~count:16 f0 in
  (* f0 = #VPMULH_16u16(f0, v); // v indep from inputs *)
  let f1 = chunk ~csize:16 ~count:16 f1 in
  (* f1 = #VPMULH_16u16(f1, v); // v indep from inputs *)
  let f2 = chunk ~csize:16 ~count:16 f2 in
  (* f2 = #VPMULH_16u16(f2, v); // v indep from inputs *)
  let f3 = chunk ~csize:16 ~count:16 f3 in

  (* f3 = #VPMULH_16u16(f3, v); // v indep from inputs *)

  (* shift1 is statically known and equal to (1 << 9) *)
  let shift1 (d : deps) =
    let do1 (d : deps) (* 16 -> 16 *) =
      d |> offset ~offset:(9 - 15) |> recast ~min:0 ~max:16
    in

    split ~csize:16 ~count:16 d |> Enum.map do1 |> aggregate ~csize:16
  in

  (* Parallel right-shift of 6 bits *)
  let f0 = shift1 f0 in
  (* f0 = #VPMULHRS_16u16(f0, shift1); // shift1 indep from inputs *)
  let f1 = shift1 f1 in
  (* f1 = #VPMULHRS_16u16(f1, shift1); // shift1 indep from inputs *)
  let f2 = shift1 f2 in
  (* f2 = #VPMULHRS_16u16(f2, shift1); // shift1 indep from inputs *)
  let f3 = shift1 f3 in

  (* f3 = #VPMULHRS_16u16(f3, shift1); // shift1 indep from inputs *)

  (* mask is statically known. We remove the clear bits *)
  (* mask if 0x000F repeated 16 times *)
  let and_mask (d : deps) =
    split ~csize:16 ~count:16 d
    |> Enum.map (clearout ~min:0 ~max:4)
    |> aggregate ~csize:16
  in

  let f0 = and_mask f0 in
  (* f0 = #VPAND_256(f0, mask); // mask indep from inputs *)
  let f1 = and_mask f1 in
  (* f0 = #VPAND_256(f0, mask); // mask indep from inputs *)
  let f2 = and_mask f2 in
  (* f0 = #VPAND_256(f0, mask); // mask indep from inputs *)
  let f3 = and_mask f3 in

  (* f0 = #VPAND_256(f0, mask); // mask indep from inputs *)
  let packus_8u16 (d : deps) =
    (* 128 -> 64 *)
    split ~csize:16 ~count:8 d |> Enum.map merge_all_deps
    |> Enum.map (constant ~size:8)
    |> aggregate ~csize:8
  in

  let vpackus_8u16 (d1 : deps) (d2 : deps) : deps =
    merge (packus_8u16 d1) (offset ~offset:64 (packus_8u16 d2))
  in

  let vpackus_16u16 (d1 : deps) (d2 : deps) : deps =
    let d1 = List.of_enum (split ~csize:128 ~count:2 d1) in
    let d2 = List.of_enum (split ~csize:128 ~count:2 d2) in

    let d1, d2 = List.as_seq2 (List.map2 vpackus_8u16 d1 d2) in

    merge d1 (offset ~offset:128 d2)
  in

  let f0 = vpackus_16u16 f0 f1 in
  (* f0 = #VPACKUS_16u16(f0, f1); *)
  let f2 = vpackus_16u16 f2 f3 in

  (* f2 = #VPACKUS_16u16(f2, f3); *)
  let vpmaddubsw_256 (d1 : deps) (d2 : deps) : deps =
    let d1 = split ~csize:8 ~count:32 d1 in
    let d2 = split ~csize:8 ~count:32 d2 in

    Enum.combine d1 d2
    |> Enum.map (fun (x1, x2) -> merge1 (merge_all_deps x1) (merge_all_deps x2))
    |> Enum.paired
    |> Enum.map (fun (d1, d2) -> merge1 d1 d2)
    |> Enum.map (fun d -> constant ~size:16 d)
    |> Enum.foldi
         (fun i d1 d -> merge d (offset ~offset:(i * 16) d1))
         (empty ~size:256)
  in

  (*
  let vpmaddubsw_256_shift2 (d : deps) : deps =
       split ~csize:8 ~count:32 d
    |> List.enum
    |> Enum.paired
    |> Enum.map (fun (d1, d2) -> merge d1 (offset ~offset:4 d2))
    |> Enum.map (enlarge ~min:0 ~max:16)
    |> Enum.mapi (fun i d -> offset ~offset:(i * 16) d)
    |> merge_all
  in
*)
  let f0 = vpmaddubsw_256 f0 (empty ~size:256) in
  (* f0 = #VPMADDUBSW_256(f0, shift2); *)
  let f2 = vpmaddubsw_256 f2 (empty ~size:256) in

  (* f2 = #VPMADDUBSW_256(f2, shift2); *)
  let f0 = vpackus_16u16 f0 f2 in

  (* f0 = #VPACKUS_16u16(f0, f2); *)

  (* The permutation is statically known *)
  let f0 = perm ~csize:32 ~perm:[ 0; 4; 1; 5; 2; 6; 3; 7 ] f0 in

  (* f0 = #VPERMD(permidx, f0); *)
  Format.eprintf "%a@." pp_deps f0
