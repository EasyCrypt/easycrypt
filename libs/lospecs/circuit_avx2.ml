(* ==================================================================== *)
open Aig
open Circuit

(* ==================================================================== *)
module type S = sig
  val vpermd : reg -> reg -> reg
  val vpbroadcast_16u16 : reg -> reg
  val vpadd_16u16 : reg -> reg -> reg
  val vpsub_16u16 : reg -> reg -> reg
  val vpand_256 : reg -> reg -> reg
  val vpmaddubsw_256 : reg -> reg -> reg
  val vpmulh_16u16 : reg -> reg -> reg
  val vpmulhrs_16u16 : reg -> reg -> reg
  val vpsra_16u16 : reg -> int -> reg
  val vpackus_16u16 : reg -> reg -> reg
end

(* ==================================================================== *)
module HandMade : S = struct
  let vpermd (i : reg) (r : reg) =
    assert (List.length r = 256);
    assert (List.length i = 256);

    let perm1 (i : reg) : reg =
      let i = List.take 3 i in
      let i = List.make 5 false_ @ i in
      List.take 32 (lsr_ r i)
    in

    let o = List.map perm1 (explode ~size:32 i) in

    List.flatten o

  (* ------------------------------------------------------------------ *)
  let vpadd_16u16 (r1 : reg) (r2 : reg) : reg =
    assert (List.length r1 = 256);
    assert (List.length r2 = 256);
    let r1 = explode ~size:16 r1 in
    let r2 = explode ~size:16 r2 in
    List.flatten (List.map2 add_dropc r1 r2)

  (* ------------------------------------------------------------------ *)
  let vpsub_16u16 (r1 : reg) (r2 : reg) : reg =
    assert (List.length r1 = 256);
    assert (List.length r2 = 256);
    let r1 = explode ~size:16 r1 in
    let r2 = explode ~size:16 r2 in
    List.flatten (List.map2 sub_dropc r1 r2)

  (* ------------------------------------------------------------------ *)
  let vpsra_16u16 (r : reg) (i : int) : reg =
    assert (List.length r = 256);
    let r = explode ~size:16 r in
    List.flatten (List.map (fun r -> arshift ~offset:i r) r)

  (* ------------------------------------------------------------------ *)
  let vpand_256 (r1 : reg) (r2 : reg) : reg =
    assert (List.length r1 = 256);
    assert (List.length r2 = 256);
    List.map2 and_ r1 r2

  (* ------------------------------------------------------------------ *)
  let vpbroadcast_16u16 (r : reg) : reg =
    assert (List.length r = 16);
    List.flatten (List.make 16 r)

  (* ------------------------------------------------------------------ *)
  let vpmulh_16u16 (r1 : reg) (r2 : reg) : reg =
    assert (List.length r1 = 256);
    assert (List.length r2 = 256);
    let r1 = explode ~size:16 r1 in
    let r2 = explode ~size:16 r2 in
    List.flatten (List.map2 umulh r1 r2)

  (* ------------------------------------------------------------------ *)
  let vpmulhrs_16u16 (r1 : reg) (r2 : reg) : reg =
    assert (List.length r1 = 256);
    assert (List.length r2 = 256);
    let r1 = explode ~size:16 r1 in
    let r2 = explode ~size:16 r2 in

    let out = List.map2 (fun r1 r2 ->
      let r1 = sextend ~size:32 r1 in
      let r2 = sextend ~size:32 r2 in
      let r = smull r1 r2 in
      let r = lsr_ r (w8 14) in
      let r = incr_dropc r in

      List.take 16 (List.drop 1 r)
    ) r1 r2 in

    List.flatten out

  (* ------------------------------------------------------------------ *)
  let vpackus_16u16 (r1 : reg) (r2 : reg) : reg =
    let pack (r : reg) : reg =
      let out =
        List.map
          (sat ~signed:false ~size:8)
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

  (* ------------------------------------------------------------------ *)
  let vpmaddubsw_256 (r1 : reg) (r2 : reg) : reg =
    assert (List.length r1 = 256);
    assert (List.length r2 = 256);

    let r1 = explode ~size:16 r1 in
    let r2 = explode ~size:16 r2 in

    let out = List.map2 (fun r1 r2 ->
      let r1l, r1h = List.split_nth 8 r1 in
      let r2l, r2h = List.split_nth 8 r2 in
      let x1 = smull (uextend ~size:16 r1l) (sextend ~size:16 r2l) in
      let x2 = smull (uextend ~size:16 r1h) (sextend ~size:16 r2h) in
      let out = add_dropc (sextend ~size:17 x1) (sextend ~size:17 x2) in
      sat ~signed:true ~size:16 out
    ) r1 r2 in

    List.flatten out
end

(* ==================================================================== *)
module FromSpec () = struct
  (* ------------------------------------------------------------------ *)
  let specs =
    let spec = Filename.concat (List.hd Config.Sites.specs) "avx2.spec" in
    let spec = File.with_file_in spec (Io.parse spec) in
    let spec = Typing.tt_program Typing.Env.empty spec in

    (*
    List.iter
      (fun (_, spec) ->
        Format.eprintf "%a@."
          (Yojson.Safe.pretty_print ~std:true)
          (Typing.adef_to_yojson spec))
      spec;
    *)
    spec
 
  (* ------------------------------------------------------------------ *)
  let vpermd = List.assoc "VPERMD" specs

  let vpermd (r1 : reg) (r2 : reg) : reg =
    Circuit_spec.circuit_of_spec [r1; r2] vpermd

  (* ------------------------------------------------------------------ *)
  let vpbroadcast_16u16 = List.assoc "VPBROADCAST_16u16" specs

  let vpbroadcast_16u16 (r : reg) : reg =
    Circuit_spec.circuit_of_spec [r] vpbroadcast_16u16

  (* ------------------------------------------------------------------ *)
  let vpadd_16u16 = List.assoc "VPADD_16u16" specs

  let vpadd_16u16 (r1 : reg) (r2 : reg) : reg =
    Circuit_spec.circuit_of_spec [r1; r2] vpadd_16u16

  (* ------------------------------------------------------------------ *)
  let vpsub_16u16 = List.assoc "VPSUB_16u16" specs

  let vpsub_16u16 (r1 : reg) (r2 : reg) : reg =
    Circuit_spec.circuit_of_spec [r1; r2] vpsub_16u16

  (* ------------------------------------------------------------------ *)
  let vpand_256 = List.assoc "VPAND_256" specs

  let vpand_256 (r1 : reg) (r2 : reg) : reg =
    Circuit_spec.circuit_of_spec [r1; r2] vpand_256

  (* ------------------------------------------------------------------ *)
  let vpmaddubsw_256 = List.assoc "VPMADDUBSW_256" specs

  let vpmaddubsw_256 (r1 : reg) (r2 : reg) : reg =
    Circuit_spec.circuit_of_spec [r1; r2] vpmaddubsw_256

  (* ------------------------------------------------------------------ *)
  let vpmulh_16u16 = List.assoc "VPMULH_16u16" specs

  let vpmulh_16u16 (r1 : reg) (r2 : reg) : reg =
    Circuit_spec.circuit_of_spec [r1; r2] vpmulh_16u16

  (* ------------------------------------------------------------------ *)
  let vpmulhrs_16u16 = List.assoc "VPMULHRS_16u16" specs

  let vpmulhrs_16u16 (r1 : reg) (r2 : reg) : reg =
    Circuit_spec.circuit_of_spec [r1; r2] vpmulhrs_16u16

  (* ------------------------------------------------------------------ *)
  let vpsra_16u16 = List.assoc "VPSRA_16u16" specs

  let vpsra_16u16 (r : reg) (n : int) : reg =
    Circuit_spec.circuit_of_spec [r; Circuit.w8 n] vpsra_16u16

  (* ------------------------------------------------------------------ *)
  let vpackus_16u16 = List.assoc "PACKUS_16u16" specs

  let vpackus_16u16 (r1 : reg) (r2 : reg) : reg =
    Circuit_spec.circuit_of_spec [r1; r2] vpackus_16u16  
end
