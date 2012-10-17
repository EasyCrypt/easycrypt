(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-2011                                               *)
(*    François Bobot                                                      *)
(*    Jean-Christophe Filliâtre                                           *)
(*    Claude Marché                                                       *)
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

let channel_contents_fmt cin fmt =
  let buff = String.make 1024 ' ' in
  let n = ref 0 in
  while n := input cin buff 0 1024; !n <> 0 do
    Format.pp_print_string fmt
      (if !n = 1024 then
         buff
       else
         String.sub buff 0 !n)
  done

let channel_contents_buf cin =
  let buf = Buffer.create 1024
  and buff = String.make 1024 ' ' in
  let n = ref 0 in
  while n := input cin buff 0 1024; !n <> 0 do
    Buffer.add_substring buf buff 0 !n
  done;
  buf

let channel_contents cin = Buffer.contents (channel_contents_buf cin)

let rec fold_channel f acc cin =
  try
    fold_channel f (f acc (input_line cin)) cin
  with End_of_file -> acc

let file_contents_fmt f fmt =
  try
    let cin = open_in f in
    channel_contents_fmt cin fmt;
    close_in cin
  with _ ->
    invalid_arg (Printf.sprintf "(cannot open %s)" f)

let file_contents_buf f =
  try
    let cin = open_in f in
    let buf = channel_contents_buf cin in
    close_in cin;
    buf
  with _ ->
    invalid_arg (Printf.sprintf "(cannot open %s)" f)

let file_contents f = Buffer.contents (file_contents_buf f)

let open_temp_file ?(debug=false) filesuffix usefile =
  let file,cout = Filename.open_temp_file "why" filesuffix in
  try
    let res = usefile file cout in
    if not debug then Sys.remove file;
    close_out cout;
    res
  with
    | e ->
        if not debug then Sys.remove file;
        close_out cout;
        raise e

type 'a result =
  | Result of 'a
  | Exception of exn

open Unix

exception Bad_execution of process_status

let call_asynchronous (f : unit -> 'a) =
  let cin,cout = pipe () in
  let cin = in_channel_of_descr cin in
  let cout = out_channel_of_descr cout in
  match fork () with
    | 0 ->
        let result =
          try
            Result (f ())
          with exn -> Exception exn in
        Marshal.to_channel cout (result : 'a result) [];
        close_out cout;
        exit 0
    | pid ->
        let f () =
          let result = (Marshal.from_channel cin: 'a result) in
          close_in cin;
          let _, ps = waitpid [] pid in
          match ps with
            | WEXITED 0 ->
                begin match result with
                  | Result res -> res
                  | Exception exn -> raise exn
                end
            | _ -> raise (Bad_execution ps) in
        f

let copy_file from to_ =
  let cin = open_in from in
  let cout = open_out to_ in
  let buff = String.make 1024 ' ' in
  let n = ref 0 in
  while n := input cin buff 0 1024; !n <> 0 do
    output cout buff 0 !n
  done

(* return the absolute path of a given file name.
   this code has been designed to be architecture-independant so
   be very careful if you modify this *)
let path_of_file f =
  let rec aux acc f =
(*
    Format.printf "aux %s@." f;
    let _ = read_line () in
*)
    let d = Filename.dirname f in
    if d = Filename.current_dir_name then
      (* f is relative to the current dir *)
      aux (f::acc) (Sys.getcwd ())
    else
      let b = Filename.basename f in
      if b=Filename.current_dir_name then acc else
        if f=b then b::acc else
          aux (b::acc) d
  in
  aux [] f

(*
let test x = (Filename.dirname x, Filename.basename x)

let _ = test "file"
let _ = test "/file"
let _ = test "/"
let _ = test "f1/f2"
let _ = test "/f1/f2"

let p1 = path_of_file "/bin/bash"

let p1 = path_of_file "../src/f.why"
  *)

let relativize_filename base f =
  let rec aux ab af =
    match ab,af with
      | x::rb, y::rf when x=y -> aux rb rf
      | _ ->
          let rec aux2 acc p =
            match p with
              | [] -> acc
              | _::rb -> aux2 (Filename.parent_dir_name::acc) rb
          in aux2 af ab
  in
  let rec rebuild l =
    match l with
      | [] -> ""
      | [x] -> x
      | x::l -> Filename.concat x (rebuild l)
  in
  rebuild (aux (path_of_file base) (path_of_file f))

let absolutize_filename dirname f =
  if Filename.is_relative f then
    Filename.concat dirname f
  else
    f

(*
let p1 = relativize_filename "/bin/bash" "src/f.why"

let p1 = relativize_filename "test" "/home/cmarche/recherche/why3/src/ide/f.why"
*)
