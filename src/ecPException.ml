(* --------------------------------------------------------------------
 * Copyright (c) - 2012-2015 - IMDEA Software Institute and INRIA
 * Distributed under the terms of the CeCILL-C license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
type exn_printer = Format.formatter -> exn -> unit

(* -------------------------------------------------------------------- *)
let exn_printers = (Stack.create () : exn_printer Stack.t)

(* -------------------------------------------------------------------- *)
let core_printer fmt exn =
  Format.fprintf fmt "anomaly: %s, please report to: @\n@." (Printexc.to_string exn);
  Format.fprintf fmt "anomaly: \t%s@\n@." EcVersion.url

(* -------------------------------------------------------------------- *)
let () = Stack.push core_printer exn_printers

(* -------------------------------------------------------------------- *)
let register ppexn = Stack.push ppexn exn_printers

let () = register Why3.Exn_printer.exn_printer

(* -------------------------------------------------------------------- *)
exception Exit_loop

let exn_printer fmt exn =
  let do1 (f : exn_printer) =
    try
      Format.fprintf fmt "@[%a@]@." f exn;
      raise Exit_loop
    with e when e <> Exit_loop -> ()
  in
  try  Stack.iter do1 exn_printers
  with Exit_loop -> ()

(* -------------------------------------------------------------------- *)
let tostring (e : exn) =
  let buf = Buffer.create 128 in
  let fmt = Format.formatter_of_buffer buf in
    exn_printer fmt e; Buffer.contents buf
