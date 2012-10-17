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

(** Create and manage one main worker which wait for the remaining
    works *)
module MainWorker :
sig
  type 'a t
  val create : unit -> 'a t
  val treat :
    maxlevel2:int -> maxlevel3:int -> 'a t -> ('b -> 'a -> 'b) -> 'b -> 'b
  type level
  val level1 :level val level2 : level val level3 : level
  val start_work : level -> 'a t -> unit
  val stop_work : level -> 'a t -> unit
  val add_work : level -> 'a t -> 'a -> unit
  val add_works : level -> 'a t -> 'a Queue.t -> unit
end
  =
struct
  type level = int
  let level1 = 1 and level2 = 2 and level3 = 3
  type 'a levels = {level1 : 'a; level2 : 'a; level3 : 'a}
  let map_level level f x =
    match level with
      | 1 -> {x with level1 = f x.level1}
      | 2 -> {x with level2 = f x.level2}
      | 3 -> {x with level3 = f x.level3}
      | _ -> assert false
  let iter_level level f x =
    match level with
      | 1 -> f x.level1
      | 2 -> f x.level2
      | 3 -> f x.level3
      | _ -> assert false

  type 'a t = { queue : 'a Queue.t levels;
                mutex : Mutex.t;
                condition : Condition.t;
                mutable remaining : int levels;
              }

  let create () =
    { queue = {level1 = Queue.create ();
               level2 = Queue.create ();
               level3 = Queue.create ()};
      mutex = Mutex.create ();
      condition = Condition.create ();
      remaining = {level1 = 0; level2 = 0; level3 = 0}
    }

  let treat ~maxlevel2 ~maxlevel3 t f acc =
    let rec main acc =
      Mutex.lock t.mutex;
      while
        Queue.is_empty t.queue.level3
        && (Queue.is_empty t.queue.level2
            || t.remaining.level3 > maxlevel3)
        && (Queue.is_empty t.queue.level1
            || t.remaining.level2 > maxlevel2)
        && t.remaining.level1 + t.remaining.level2 + t.remaining.level3 > 0
      do
        Condition.wait t.condition t.mutex
      done;
      let for_one queue =
        let v = Queue.pop queue in
        Mutex.unlock t.mutex;
        let acc = f acc v in
        Thread.yield ();
        main acc
      in
      try
        (* Format.printf "level3 : l1=%i;l2=%i;l3=%i@." *)
        (*   t.remaining.level1 *)
        (*   t.remaining.level2 *)
        (*   t.remaining.level3 ; *)
        for_one t.queue.level3
      with Queue.Empty ->
      try
        (* Format.printf "level2 : l1=%i;l2=%i;l3=%i@." *)
        (*   t.remaining.level1 *)
        (*   t.remaining.level2 *)
        (*   t.remaining.level3 ; *)
        for_one t.queue.level2
      with Queue.Empty ->
      try
        (* Format.printf "level1 : l1=%i;l2=%i;l3=%i@." *)
        (*   t.remaining.level1 *)
        (*   t.remaining.level2 *)
        (*   t.remaining.level3 ; *)
        for_one t.queue.level1
      with Queue.Empty ->
        (* t.remaining.level1 + t.remaining.level2 + t.remaining.level3 = 0 *)
        Mutex.unlock t.mutex;
        acc in
    main acc

  let start_work level t =
    Mutex.lock t.mutex;
    t.remaining <- map_level level succ t.remaining;
    Mutex.unlock t.mutex

  let stop_work level t =
    Mutex.lock t.mutex;
    t.remaining <- map_level level pred t.remaining;
    Condition.signal t.condition;
    Mutex.unlock t.mutex

  let add_work level t x =
    Mutex.lock t.mutex;
    iter_level level (Queue.push x) t.queue;
    Condition.signal t.condition;
    Mutex.unlock t.mutex

  let add_works level t q =
    Mutex.lock t.mutex;
    iter_level level (Queue.transfer q) t.queue;
    Condition.signal t.condition;
    Mutex.unlock t.mutex


end

(** Manage a pool of worker *)
module ManyWorkers :
sig
  type 'a t
  val create : int ref -> ('a -> unit) -> 'a t
    (** [create n f] create a pool of [n] worker doing [f] *)
  val add_work : 'a t -> 'a -> unit
  val add_works : 'a t -> 'a Queue.t -> unit
end
  =
struct
  type 'a t = { queue : 'a Queue.t;
                mutex : Mutex.t;
                f : 'a -> unit;
                max : int ref;
                mutable current : int;
              }

  let create n f =
    { queue = Queue.create ();
      mutex = Mutex.create ();
      f = f;
      max = n;
      current = 0;
    }

  let rec run t x =
    t.f x;
    Mutex.lock t.mutex;
    if not (Queue.is_empty t.queue) then
      let x = Queue.pop t.queue in
      Mutex.unlock t.mutex;
      run t x
    else begin
      t.current <- t.current - 1;
      Mutex.unlock t.mutex
    end

  (** In the next functions, we never call [start] inside the
      mutex in order to release it as soon as possible *)
  let start t x = ignore (Thread.create (run t) x)

  let add_work t x =
    Mutex.lock t.mutex;
    if t.current < !(t.max)
    then begin
      t.current <- t.current + 1;
      Mutex.unlock t.mutex;
      start t x
    end
    else begin
      Queue.push x t.queue;
      Mutex.unlock t.mutex
    end


  let add_works t q =
    let rec extract acc =
      if t.current < !(t.max) && not (Queue.is_empty q)
      then
        let x = Queue.pop q in
        t.current <- t.current + 1;
        extract (x::acc)
      else acc in
    Mutex.lock t.mutex;
    let now = extract [] in
    Queue.transfer q t.queue;
    Mutex.unlock t.mutex;
    List.iter (start t) now


end
