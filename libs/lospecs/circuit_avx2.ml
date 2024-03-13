(* ==================================================================== *)
open Aig

type symbol = string

(* ==================================================================== *)
module type S = sig
  val func_from_spec : symbol -> (reg list -> reg)
  val vpermd : reg -> reg -> reg
  val vpermq : reg -> int -> reg
  val vpbroadcast_16u16 : reg -> reg
  val vpadd_16u16 : reg -> reg -> reg
  val vpadd_32u8 : reg -> reg -> reg
  val vpsub_16u16 : reg -> reg -> reg
  val vpsub_32u8 : reg -> reg -> reg
  val vpand_256 : reg -> reg -> reg
  val vpmaddubsw_256 : reg -> reg -> reg
  val vpmulh_16u16 : reg -> reg -> reg
  val vpmulhrs_16u16 : reg -> reg -> reg
  val vpsra_16u16 : reg -> int -> reg
  val vpsrl_16u16 : reg -> int -> reg
  val vpsrl_4u64 : reg -> int -> reg
  val vpsll_4u64 : reg -> int -> reg
  val vpackus_16u16 : reg -> reg -> reg
  val vpackss_16u16 : reg -> reg -> reg
  val vpshufb_256 : reg -> reg -> reg
  val vpcmpgt_16u16 : reg -> reg -> reg
  val vpmovmskb_u256u64 : reg -> reg
  val vpunpckl_32u8 : reg -> reg -> reg
  val vpextracti128 : reg -> int -> reg
  val vpinserti128 : reg -> reg -> int -> reg
  val vpblend_16u16 : reg -> reg -> int -> reg
  val vpslldq_256 : reg -> int -> reg
  val vpsrldq_256 : reg -> int -> reg
  val vpslldq_128 : reg -> int -> reg
  val vpsrldq_128 : reg -> int -> reg
end

(* ==================================================================== *)
module FromSpec () : S = struct
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

  let func_from_spec (f: symbol) : (reg list) -> reg =
    (fun regs -> Circuit_spec.circuit_of_spec regs (List.assoc f specs))
 
  (* ------------------------------------------------------------------ *)
  let vpermd = List.assoc "VPERMD" specs

  let vpermd (r1 : reg) (r2 : reg) : reg =
    Circuit_spec.circuit_of_spec [r1; r2] vpermd

  (* ------------------------------------------------------------------ *)
  let vpermq = List.assoc "VPERMQ" specs

  let vpermq (r : reg) (i : int) : reg =
    Circuit_spec.circuit_of_spec [r; Circuit.w8 i] vpermq

  (* ------------------------------------------------------------------ *)
  let vpbroadcast_16u16 = List.assoc "VPBROADCAST_16u16" specs

  let vpbroadcast_16u16 (r : reg) : reg =
    Circuit_spec.circuit_of_spec [r] vpbroadcast_16u16

  (* ------------------------------------------------------------------ *)
  let vpadd_16u16 = List.assoc "VPADD_16u16" specs

  let vpadd_16u16 (r1 : reg) (r2 : reg) : reg =
    Circuit_spec.circuit_of_spec [r1; r2] vpadd_16u16

  (* ------------------------------------------------------------------ *)
  let vpadd_32u8 = List.assoc "VPADD_32u8" specs

  let vpadd_32u8 (r1 : reg) (r2 : reg) : reg =
    Circuit_spec.circuit_of_spec [r1; r2] vpadd_32u8

  (* ----------------------------------------------------------------- *)
  let vpsub_16u16 = List.assoc "VPSUB_16u16" specs

  let vpsub_16u16 (r1 : reg) (r2 : reg) : reg =
    Circuit_spec.circuit_of_spec [r1; r2] vpsub_16u16

  (* ------------------------------------------------------------------ *)
  let vpsub_32u8 = List.assoc "VPSUB_32u8" specs

  let vpsub_32u8 (r1 : reg) (r2 : reg) : reg =
    Circuit_spec.circuit_of_spec [r1; r2] vpsub_32u8

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
  let vpsrl_16u16 = List.assoc "VPSRL_16u16" specs

  let vpsrl_16u16 (r : reg) (n : int) : reg =
    Circuit_spec.circuit_of_spec [r; Circuit.w8 n] vpsrl_16u16

  (* ------------------------------------------------------------------ *)
  let vpsrl_4u64 = List.assoc "VPSRL_4u64" specs

  let vpsrl_4u64 (r : reg) (n : int) : reg =
    Circuit_spec.circuit_of_spec [r; Circuit.w8 n] vpsrl_4u64

  (* ------------------------------------------------------------------ *)
  let vpsll_4u64 = List.assoc "VPSLL_4u64" specs

  let vpsll_4u64 (r : reg) (n : int) : reg =
    Circuit_spec.circuit_of_spec [r; Circuit.w8 n] vpsll_4u64

  (* ------------------------------------------------------------------ *)
  let vpslldq_256 = List.assoc "VPSLLDQ_256" specs

  let vpslldq_256 (r : reg) (n : int) : reg =
    Circuit_spec.circuit_of_spec [r; Circuit.w8 (8 * n)] vpslldq_256

  (* ------------------------------------------------------------------ *)
  let vpsrldq_256 = List.assoc "VPSRLDQ_256" specs

  let vpsrldq_256 (r : reg) (n : int) : reg =
    Circuit_spec.circuit_of_spec [r; Circuit.w8 (8 * n)] vpsrldq_256

  (* ------------------------------------------------------------------ *)
  let vpslldq_128 = List.assoc "VPSLLDQ_128" specs

  let vpslldq_128 (r : reg) (n : int) : reg =
    Circuit_spec.circuit_of_spec [r; Circuit.w8 (8 * n)] vpslldq_128

  (* ------------------------------------------------------------------ *)
  let vpsrldq_128 = List.assoc "VPSRLDQ_128" specs

  let vpsrldq_128 (r : reg) (n : int) : reg =
    Circuit_spec.circuit_of_spec [r; Circuit.w8 (8 * n)] vpsrldq_128

  (* ------------------------------------------------------------------ *)
  let vpackus_16u16 = List.assoc "VPACKUS_16u16" specs

  let vpackus_16u16 (r1 : reg) (r2 : reg) : reg =
    Circuit_spec.circuit_of_spec [r1; r2] vpackus_16u16  

  (* ------------------------------------------------------------------ *)
  let vpackss_16u16 = List.assoc "VPACKSS_16u16" specs

  let vpackss_16u16 (r1 : reg) (r2 : reg) : reg =
    Circuit_spec.circuit_of_spec [r1; r2] vpackss_16u16
    
  (* ------------------------------------------------------------------ *)
  let vpshufb_256 = List.assoc "VPSHUFB_256" specs

  let vpshufb_256 (r1 : reg) (r2 : reg) : reg =
    Circuit_spec.circuit_of_spec [r1; r2] vpshufb_256

  (* ------------------------------------------------------------------ *)
  let vpcmpgt_16u16 = List.assoc "VPCMPGT_16u16" specs

  let vpcmpgt_16u16 (r1 : reg) (r2 : reg) : reg =
    Circuit_spec.circuit_of_spec [r1; r2] vpcmpgt_16u16

  (* ------------------------------------------------------------------ *)
  let vpmovmskb_u256u64 = List.assoc "VPMOVMSKB_u256u64" specs

  let vpmovmskb_u256u64 (r : reg) : reg =
    Circuit_spec.circuit_of_spec [r] vpmovmskb_u256u64

  (* ------------------------------------------------------------------ *)
  let vpunpckl_32u8 = List.assoc "VPUNPCKL_32u8" specs

  let vpunpckl_32u8 (r1 : reg) (r2 : reg): reg =
    Circuit_spec.circuit_of_spec [r1; r2] vpunpckl_32u8

  (* ------------------------------------------------------------------ *)
  let vpextracti128 = List.assoc "VPEXTRACTI128" specs

  let vpextracti128 (r : reg) (i : int): reg =
    Circuit_spec.circuit_of_spec [r; Circuit.w8 i] vpextracti128

  (* ------------------------------------------------------------------ *)
  let vpinserti128 = List.assoc "VPINSERTI128" specs

  let vpinserti128 (r1 : reg) (r2 : reg) (i : int): reg =
    Circuit_spec.circuit_of_spec [r1; r2; Circuit.w8 i] vpinserti128

  (* ------------------------------------------------------------------ *)
  let vpblend_16u16 = List.assoc "VPBLEND_16u16" specs

  let vpblend_16u16 (r1 : reg) (r2 : reg) (i : int): reg =
    Circuit_spec.circuit_of_spec [r1; r2; Circuit.w8 i] vpblend_16u16
end
