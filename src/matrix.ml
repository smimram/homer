(** Operations on matrices with integer coefficients. *)
open Stdlib

type t = int array array

type matrix = t

let create r c = Array.init r (fun _ -> Array.make c 0)
    
let rows m = Array.length m

let cols m = Array.length m.(0)

let to_string m =
  let ans = ref "" in
  for i = 0 to rows m - 1 do
    for j = 0 to cols m - 1 do
      if j <> 0 then ans := !ans ^ "\t";
      ans := !ans ^ string_of_int m.(i).(j)
    done;
    ans := !ans ^ "\n"
  done;
  !ans

(** Operations on rows. *)
module Row = struct
  let replace m i mi =
    Array.init (rows m) (fun k -> if k = i then mi else m.(k))

  let exchange m i j =
    Array.init (rows m) (fun k -> if k = i then m.(j) else if k = j then m.(i) else m.(k))

  let mult m q i =
    assert (q <> 0);
    let mi = Array.init (cols m) (fun k -> q * m.(i).(k)) in
    replace m i mi

  let madd m i q j =
    assert (i <> j);
    let mi = Array.init (cols m) (fun k -> m.(i).(k) + q * m.(j).(k)) in
    replace m i mi
end

let row_echelon m =
  let m = ref m in
  let ip = ref 0 in
  let cols = if rows !m = 0 then 0 else cols !m in
  for j = 0 to cols - 1 do
    if !m.(!ip).(j) = 0 then
      (
        try
          for i = !ip + 1 to rows !m - 1 do
            if !m.(i).(j) <> 0 then (m := Row.exchange !m !ip i; raise Exit)
          done
        with
        | Exit -> ()
      );
    let a = !m.(!ip).(j) in
    if a <> 0 then
      (
        for i = !ip + 1 to rows !m - 1 do
          let b = !m.(i).(j) in
          if b <> 0 then
            (
              m := Row.mult !m (-a) i;
              m := Row.madd !m i b !ip
            )
        done;
        incr ip
      )
  done;
  !m

(** Dimension of the image. *)
let rank m =
  let m = row_echelon m in
  let n = ref 0 in
  try
    if rows m = 0 then raise Exit; (* Avoid a problem with undefined cols below. *)
    for i = 0 to min (rows m) (cols m) - 1 do
      if m.(i).(i) = 0 then raise Exit else incr n
    done;
    raise Exit
  with
  | Exit -> !n

(** Dimension of the kernel. *)
let nullity m =
  rows m - rank m

(** Matrices with labeled basis elements. *)
module Labeled = struct
  type 'a map = 'a array

  type 'a t = 'a map * 'a map * matrix

  let matrix ((_,_,m):'a t) = m

  let create rows cols : 'a t =
    let m = create (Array.length rows) (Array.length cols) in
    rows, cols, m

  let set ((r,c,m):'a t) i j x =
    let i = Array.index r i in
    let j = Array.index c j in
    m.(i).(j) <- x

  let get ((r,c,m):'a t) i j =
    let i = Array.index r i in
    let j = Array.index c j in
    m.(i).(j)

  let rank ((r,c,m):'a t) = rank m

  let nullity ((r,c,m):'a t) = nullity m
end
