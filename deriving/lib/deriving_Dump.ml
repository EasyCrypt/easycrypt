(** Dump **)

(* Copyright Jeremy Yallop 2007.
   This file is free software, distributed under the MIT license.
   See the file COPYING for details.
*)

(* TODO: we could have an additional debugging deserialisation method. *)
module type Dump = sig
  type a
    val to_buffer : Buffer.t -> a -> unit
    val to_string : a -> string
    val to_channel : out_channel -> a -> unit
    val from_stream : char Stream.t -> a
    val from_string : string -> a
    val from_channel : in_channel -> a
end

module type SimpleDump = sig
  type a
  val to_buffer : Buffer.t -> a -> unit
  val from_stream : char Stream.t -> a
end

exception Dump_error of string

let bad_tag tag stream typename =
  raise (Dump_error
           (Printf.sprintf 
              "Dump: failure during %s deserialisation at character %d; unexpected tag %d" 
              typename (Stream.count stream) tag))

module Defaults (P : sig   
			  type a
			  val to_buffer : Buffer.t -> a -> unit
			  val from_stream : char Stream.t -> a
			end) : Dump with type a = P.a = 
struct
  include P

 (* is there a reasonable value to use here? *)
  let buffer_size = 128

  let to_string obj = 
    let buffer = Buffer.create buffer_size in
      P.to_buffer buffer obj;
      Buffer.contents buffer
      (* should we explicitly deallocate the buffer? *)
  and from_string string = P.from_stream (Stream.of_string string)
  and from_channel in_channel = 
    from_stream (Stream.of_channel in_channel)
  and to_channel out_channel obj = 
    let buffer = Buffer.create buffer_size in
      P.to_buffer buffer obj;
      Buffer.output_buffer out_channel buffer
end


(* Generic int dumper.  This should work for any (fixed-size) integer
   type with suitable operations. *)
module Dump_intN (P : sig
                      type t
                      val zero : t
                      val logand : t -> t -> t
                      val logor : t -> t -> t
                      val lognot : t -> t
                      val shift_right_logical : t -> int -> t
                      val shift_left : t -> int -> t
                      val of_int : int -> t
                      val to_int : t -> int
                    end) = Defaults (
  struct
    type a = P.t
	(* Format an integer using the following scheme:
	   
	   The lower 7 bits of each byte are used to store successive 7-bit
	   chunks of the integer.
	   
	   The highest bit of each byte is used as a flag to indicate
	   whether the next byte is present.
	*)
    open Buffer
    open Char
    open P

    let to_buffer buffer =
      let rec aux int =
        (* are there more than 7 bits? *)
        if logand int (lognot (of_int 0x7f)) <> zero
        (* if there are, write the lowest 7 bite plus a high bit (to
           indicate that there's more).  Then recurse, shifting the value
           7 bits right *)
        then begin
          add_char buffer (chr (to_int (logor (of_int 0x80) (logand int (of_int 0x7f)))));
	  aux (shift_right_logical int 7)
        end
          (* otherwise, write the bottom 7 bits only *)
        else add_char buffer (chr (to_int int))
      in aux

    and from_stream stream = 
      let rec aux (int : t) shift = 
        let c = of_int (code (Stream.next stream)) in
        let int = logor int (shift_left (logand c (of_int 0x7f)) shift) in
          if logand c (of_int 0x80) <> zero then aux int (shift + 7)
          else int 
      in aux zero 0
  end
)

module Dump_int32 = Dump_intN (Int32)
module Dump_int64 = Dump_intN (Int64)
module Dump_nativeint = Dump_intN (Nativeint)
module Dump_int = Defaults (
  struct
    type a = int
    let to_buffer buffer int = Dump_nativeint.to_buffer buffer (Nativeint.of_int int)
    and from_stream stream = Nativeint.to_int (Dump_nativeint.from_stream stream)
  end
)

module Dump_char = Defaults (
  struct
    type a = char
    let to_buffer = Buffer.add_char
    and from_stream = Stream.next
  end
)

(* This is questionable; it doesn't preserve sharing *)
module Dump_string = Defaults (
  struct
    type a = string
    let to_buffer buffer string = 
      begin
        Dump_int.to_buffer buffer (String.length string);
        Buffer.add_string buffer string
      end
    and from_stream stream = 
      let len = Dump_int.from_stream stream in
      let s = String.create len in
        for i = 0 to len - 1 do
          String.set s i (Stream.next stream) (* could use String.unsafe_set here *)
        done;
        s
  end
)

module Dump_float = Defaults (
  struct
    type a = float
    let to_buffer buffer f = Dump_int64.to_buffer buffer (Int64.bits_of_float f)
    and from_stream stream = Int64.float_of_bits (Dump_int64.from_stream stream)
  end
)

(* This should end up a bit more compact than the derived version *)
module Dump_list (P : SimpleDump) = Defaults (
  (* This could perhaps be more efficient by serialising the list in
     reverse: this would result in only one traversal being needed
     during serialisation, and no "reverse" being needed during
     deserialisation.  (However, dumping would no longer be
     tail-recursive) *)
  struct
    type a = P.a list
    let to_buffer buffer items = 
      begin
        Dump_int.to_buffer buffer (List.length items);
        List.iter (P.to_buffer buffer) items
      end
    and from_stream stream = 
      let rec aux items = function
        | 0 -> items
        | n -> aux (P.from_stream stream :: items) (n-1)
      in List.rev (aux [] (Dump_int.from_stream stream))
  end
)

(* Dump_ref and Dump_array cannot preserve sharing, so we don't
   provide implementations *)

module Dump_option (P : SimpleDump) = Defaults (
  struct
    type a = P.a option
    let to_buffer buffer = function
      | None   -> Dump_int.to_buffer buffer 0
      | Some s -> 
          begin
            Dump_int.to_buffer buffer 1;
            P.to_buffer buffer s
          end
    and from_stream stream = 
      match Dump_int.from_stream stream with
        | 0 -> None
        | 1 -> Some (P.from_stream stream)
        | i      -> bad_tag i stream "option"
  end
)


module Dump_bool = Defaults (
  struct
    type a = bool
    let to_buffer buffer = function
      | false -> Buffer.add_char buffer '\000'
      | true  -> Buffer.add_char buffer '\001'
    and from_stream stream =
      match Stream.next stream with
        | '\000' -> false
        | '\001' -> true
        | c      -> bad_tag (Char.code c) stream "bool"
  end
)

module Dump_unit = Defaults (
  struct
    type a = unit
    let to_buffer _ () = ()
    and from_stream _ = ()
  end
)

module Dump_alpha(P: sig type a end) = Defaults(struct
  type a = P.a
  let to_buffer _ _ = assert false
  let from_stream _ = assert false
end)

module Dump_undumpable (P : sig type a val tname : string end) = Defaults ( 
  struct 
    type a = P.a
    let to_buffer _ _ = failwith ("Dump: attempt to serialise a value of unserialisable type : " ^ P.tname)
    let from_stream _ = failwith ("Dump: attempt to deserialise a value of unserialisable type : " ^ P.tname)
  end
)

(* Uses Marshal to serialise the values that the parse-the-declarations
   technique can't reach. *)
module Dump_via_marshal (P : sig type a end) = Defaults (
(* Rather inefficient. *)
  struct
    include P
    let to_buffer buffer obj = Buffer.add_string buffer (Marshal.to_string obj [Marshal.Closures])
    let from_stream stream = 
      let readn n = 
        let s = String.create n in
          for i = 0 to n - 1 do
            String.set s i (Stream.next stream)
          done;
          s
      in
      let header = readn Marshal.header_size in
      let datasize = Marshal.data_size header 0 in
      let datapart = readn datasize in
        Marshal.from_string (header ^ datapart) 0
  end)
