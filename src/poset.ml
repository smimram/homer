(** Partially ordered sets. *)

open Standard

type t = bool array array

type poset = t

let create n = Array.init n (fun i -> (Array.init n (fun j -> i = j)))

let card (p:t) =
  Array.length p

let copy p =
  Array.init (card p) (fun i -> Array.copy p.(i))

let le p x y =
  p.(x).(y)

 (** Raised when adding a relation when the poset becomes cyclic. *)
 exception Cyclic

(** Add a dependency relation. *)
let rec add p x y =
  if x <> y && le p y x then raise Cyclic;
  if not (le p x y) then
    (
      p.(x).(y) <- true;
      for i = 0 to card p - 1 do
        if le p i x then add p i y;
        if le p y i then add p x i
      done
    )  

(** Labeled variant of posets. *)
module Labeled = struct
  exception Cyclic = Cyclic

  type t = string array * poset

  let create l : t =
    let l = Array.of_list l in
    let n = Array.length l in
    let p = create n in
    l, p

  let copy ((l,p):t) : t =
    l, copy p

  let le ((l,p):t) x y =
    let x = Array.index l x in
    let y = Array.index l y in
    le p x y

  let add ((l,p):t) x y =
    let x = Array.index l x in
    let y = Array.index l y in
    add p x y

  (** Sort a list according to the poset. *)
  let sort_list p l =
    (* We will dynamically extend p as a total order. *)
    let p = copy p in
    (*
    List.iter (fun x ->
      List.iter (fun y ->
        if not (le p x y) && not (le p y x) then
          add p x y
      ) l
    ) l;
    let compare x y = if x = y then 0 else if le p x y then -1 else 1 in
    *)
    let compare x y =
      if x = y then 0
      else
        if le p x y then -1
        else if le p y x then 1
        else (add p x y; -1)
    in
    List.fast_sort compare l

  let to_string (l,p) =
    let l = String.concat " , " (Array.to_list l) in
    let ans = ref (l ^ "\n") in
    for i = 0 to card p - 1 do
      for j = 0 to card p - 1 do
        ans := !ans ^ (if p.(i).(j) then "1" else "0")
      done;
      ans := !ans ^ "\n"
    done;
    !ans
end
