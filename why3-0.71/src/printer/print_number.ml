(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-2011                                               *)
(*    François Bobot                                                      *)
(*    Jean-Christophe Filliâtre                                           *)
(*    Claude Marché                                                       *)
(*    Guillaume Melquiond                                                 *)
(*    Andrei Paskevich                                                    *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Library General Public           *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)

open Format
open Big_int
open Term

let any_to_dec radix s =
  let n = String.length s in
  let rec compute acc i =
    if i = n then
      acc
    else begin
      let v = match s.[i] with
        | '0'..'9' as c -> Char.code c - Char.code '0'
        | 'A'..'Z' as c -> 10 + Char.code c - Char.code 'A'
        | 'a'..'z' as c -> 10 + Char.code c - Char.code 'a'
        | _ -> assert false in
      assert (v < radix);
      compute (add_int_big_int v (mult_int_big_int radix acc)) (i + 1)
    end in
  string_of_big_int (compute zero_big_int 0)

let power2 n =
  string_of_big_int (power_int_positive_int 2 n)

type integer_format = (string -> unit, Format.formatter, unit) format
type real_format = (string -> string -> string -> unit, Format.formatter, unit) format
type part_real_format = (string -> string -> unit, Format.formatter, unit) format
type dec_real_format =
  | PrintDecReal of part_real_format * real_format
type frac_real_format =
  | PrintFracReal of integer_format * part_real_format * part_real_format

type 'a number_support_kind =
  | Number_unsupported
  | Number_default
  | Number_custom of 'a

type integer_support_kind = integer_format number_support_kind

type number_support = {
  long_int_support : bool;
  dec_int_support : integer_support_kind;
  hex_int_support : integer_support_kind;
  oct_int_support : integer_support_kind;
  bin_int_support : integer_support_kind;
  def_int_support : integer_support_kind;
  dec_real_support : dec_real_format number_support_kind;
  hex_real_support : real_format number_support_kind;
  frac_real_support : frac_real_format number_support_kind;
  def_real_support : integer_support_kind;
}

let check_support support default do_it try_next v =
  match support with
  | Number_unsupported -> try_next v
  | Number_default -> do_it (match default with Some d -> d | None -> assert false) v
  | Number_custom f -> do_it f v

let force_support support do_it v =
  match support with
  | Number_unsupported -> assert false
  | Number_default -> assert false
  | Number_custom f -> do_it f v

let simplify_max_int = big_int_of_string "2147483646"

let remove_minus e =
  if e.[0] = '-' then
    (let e' = String.copy e in e'.[0] <- 'm'; e')
  else e

let print_dec_int support fmt i =
  let fallback i =
    force_support support.def_int_support (fprintf fmt) i in
  if not support.long_int_support &&
     (compare_big_int (big_int_of_string i) simplify_max_int > 0) then
    fallback i
  else
    check_support support.dec_int_support (Some "%s") (fprintf fmt)
    fallback i

let print_hex_int support fmt =
  check_support support.hex_int_support (Some "0x%s")
    (fun s i -> assert support.long_int_support; fprintf fmt s i)
  (fun i -> print_dec_int support fmt (any_to_dec 16 i))

let print_oct_int support fmt =
  check_support support.oct_int_support (Some "0o%s")
    (fun s i -> assert support.long_int_support; fprintf fmt s i)
  (fun i -> print_dec_int support fmt (any_to_dec 8 i))

let print_bin_int support fmt =
  check_support support.bin_int_support (Some "0b%s")
    (fun s i -> assert support.long_int_support; fprintf fmt s i)
  (fun i -> print_dec_int support fmt (any_to_dec 2 i))

let print_dec_real support fmt =
  check_support support.dec_real_support
    (Some (PrintDecReal ("%s.%s", "%s.%se%s")))
    (fun (PrintDecReal (noexp,full)) i f e ->
      match e with
      | None -> fprintf fmt noexp i f
      | Some e -> fprintf fmt full i f e)
  (check_support support.frac_real_support None
    (fun (PrintFracReal (exp_zero, exp_pos, exp_neg)) i f e ->
      let f = if f = "0" then "" else f in
      let e =
        (match e with None -> 0 | Some e -> int_of_string e) - String.length f in
      if e = 0 then
        fprintf fmt exp_zero (i ^ f)
      else if e > 0 then
        fprintf fmt exp_pos (i ^ f) ("1" ^ String.make e '0')
      else
        fprintf fmt exp_neg (i ^ f) ("1" ^ String.make (-e) '0'))
  (force_support support.def_real_support
    (fun def i f e -> fprintf fmt def (sprintf "%s_%s_e%s" i f
      (match e with None -> "0" | Some e -> remove_minus e)))
  ))

let print_hex_real support fmt =
  check_support support.hex_real_support
    (Some "0x%s.%sp%s")
    (fun s i f e -> fprintf fmt s i f e)
  (* TODO: add support for decay to decimal floats *)
  (check_support support.frac_real_support None
    (fun (PrintFracReal (exp_zero, exp_pos, exp_neg)) i f e ->
      let f = if f = "0" then "" else f in
      let dec = any_to_dec 16 (i ^ f) in
      let e = int_of_string e - 4 * String.length f in
      if e = 0 then
        fprintf fmt exp_zero dec
      else if e > 0 then
        fprintf fmt exp_pos dec (power2 e)
      else
        fprintf fmt exp_neg dec (power2 (-e)))
  (force_support support.def_real_support
    (fun def i f e -> fprintf fmt def (sprintf "0x%s_%s_p%s" i f (remove_minus e)))
  ))

let print support fmt = function
  | ConstInt (IConstDecimal i) -> print_dec_int support fmt i
  | ConstInt (IConstHexa i)    -> print_hex_int support fmt i
  | ConstInt (IConstOctal i)   -> print_oct_int support fmt i
  | ConstInt (IConstBinary i)  -> print_bin_int support fmt i
  | ConstReal (RConstDecimal (i, f, e)) -> print_dec_real support fmt i f e
  | ConstReal (RConstHexa (i, f, e))    -> print_hex_real support fmt i f e

(*
Local Variables:
compile-command: "unset LANG; make -C ../.. byte"
End:
*)
