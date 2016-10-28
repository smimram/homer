(** Enhancements over standard library. *)

let id x = x

let get_some = function
  | Some x -> x
  | None -> raise Not_found

let maybe x = function
  | Some x -> x
  | None -> x

let fixpoint f x =
  let first = ref true in
  let xold = ref x in
  let x = ref x in
  while !xold <> !x || !first do
    first := false;
    xold := !x;
    x := f !x;
  done;
  !x

let iff a b =
  a && b || (not a && not b)

(** Iter a function a given number of times. *)
let rec iter k f x =
  if k = 0 then x else iter (k-1) f (f x)

let sort_pair (x,y) =
  if x <= y then x,y else y,x

(* Inefficient implementation for js_of_ocaml. *)
let input_char ic =
  let c = Bytes.create 1 in
  if input ic c 0 1 = 0 then raise End_of_file;
  c.[0]

(* Inefficient implementation for js_of_ocaml. *)
(* TODO: correctly handle last line *)
let input_line ic =
  let ans = ref "" in
  let c = ref (input_char ic) in
  try
    while !c <> '\n' do
      let s = Bytes.create (Bytes.length !ans + 1) in
      Bytes.blit !ans 0 s 0 (Bytes.length !ans);
      ans := s;
      Bytes.set !ans (Bytes.length !ans - 1) !c;
      c := input_char ic
    done;
    !ans
  with
  | End_of_file ->
    if !ans <> "" then !ans else raise End_of_file

(** Koszul sign rule *)
let koszul n =
  if n mod 2 = 0 then 1 else -1

module Array = struct
  include Array

  let for_all p a =
    try
      Array.iter (fun x -> if not (p x) then raise Exit) a;
      true
    with
    | Exit -> false

  let for_alli p a =
    try
      Array.iteri (fun i x -> if not (p i x) then raise Exit) a;
      true
    with
    | Exit -> false

  let for_all2 p a b =
    try
      assert (length a = length b);
      for i = 0 to length a - 1 do
        if not (p a.(i) b.(i)) then raise Exit
      done;
      true
    with
    | Exit -> false

  let exists p a =
    try
      for i = 0 to length a - 1 do
        if p a.(i) then raise Exit
      done;
      false
    with
    | Exit -> true

  (** Is [a] included in [b] at offset [off]? *)
  let included off a b =
    try
      if (off + Array.length a > Array.length b) then raise Exit;
      for i = 0 to Array.length a - 1 do
        if a.(i) <> b.(i+off) then raise Exit
      done;
      true
    with
    | Exit -> false

  let sub_right a off len =
    let l = Array.length a in
    Array.sub a (l-len-off) len

  let index a x =
    let ans = ref (-1) in
    try
      for i = 0 to Array.length a - 1 do
        if a.(i) = x then (ans := i; raise Exit)
      done;
      raise Not_found
    with
    | Exit -> !ans

  let mem x a =
    try
      for i = 0 to Array.length a - 1 do
        if a.(i) = x then raise Exit
      done;
      false
    with
    | Exit -> true

  let contains a x =
    try
      ignore (index a x); true
    with
    | Not_found -> false

  let is_prefix a b =
    assert (Array.length a <= Array.length b);
    let ans = ref true in
    for i = 0 to Array.length a - 1 do
      if a.(i) <> b.(i) then ans := false
    done;
    !ans

  let is_suffix a b =
    let la = Array.length a in
    let lb = Array.length b in
    assert (la <= lb);
    let ans = ref true in
    for i = la - 1 downto 0 do
      let j = lb - 1 - (la - 1 - i) in
      if a.(i) <> b.(j) then ans := false
    done;
    !ans

  let incr a i = a.(i) <- a.(i) + 1

  let iter2 f a b =
    assert (length a = length b);
    for i = 0 to Array.length a - 1 do
      f a.(i) b.(i)
    done

  let count f a =
    let ans = ref 0 in
    for i = 0 to Array.length a - 1 do
      ans := !ans + f a.(i)
    done;
    !ans
end

module List = struct
  include List

  let iteri f l =
    let rec aux n = function
      | x::t -> f n x; aux (n+1) t
      | [] -> ()
    in
    aux 0 l

  let rec may_map f = function
    | h::t ->
       (
         match f h with
         | Some h' -> h'::(may_map f t)
         | None -> may_map f t
       )
    | [] -> []

  let iter_pairs f l1 l2 =
    iter (fun x -> iter (fun y -> f x y) l2) l1

  (** Iterate over strictly ordered pairs. *)
  let rec iter_ordered_pairs f = function
    | x::l -> iter (fun y -> f x y) l; iter_ordered_pairs f l
    | [] -> ()

  let rec remove_duplicates = function
    | [] -> []
    | x::l ->  x::(remove_duplicates (filter (fun y -> y <> x) l))

  let rec last = function
    | [] -> raise Not_found
    | [x] -> x
    | _::l -> last l
       
  let rec first_n_elts n l = 
    if n < 0 
    then []
    else match n, l with 
    | 0, l -> []
    | n, [] -> []
    | n, x::xx -> x:: (first_n_elts (n-1) xx)

  let map_ctx f =
    let rec aux h = function
      | x::t -> (f h x t)::(aux (x::h) t)
      | [] -> []
    in
    aux []

  let iter_ctx f l =
    let rec aux h = function
      | x::t -> f h x t; aux (x::h) t
      | [] -> ()
    in
    aux [] l

  let init n f =
    let rec aux k =
      if k < n then (f k)::(aux (k+1)) else []
    in
    aux 0

  let rec bind f = function
    | x::l ->  (f x)@(bind f l)
    | [] -> []

  let bind_ctx f l =
    concat (map_ctx f l)

  let count f l =
    fold_left (fun n x -> n + f x) 0 l

  (** Remove duplicates. *)
  let rec unique = function
    | x::l -> if mem x l then unique l else x::(unique l)
    | [] -> []

  (** Concatenation without duplicates. *)
  let union l1 l2 =
    unique (l1@l2)

  (** Difference. *)
  let diff l1 l2 =
    filter (fun x -> not (mem x l2)) l1

  let assoc_all x l =
    may_map (fun (x',y) -> if x' = x then Some y else None) l
end

module String = struct
  include String

  let of_char c = String.make 1 c

  let split_char s c =
    if s = "" then [] else
      let b = ref 0 in
      let ans = ref [] in
      try
        while true do
          let e = index_from s !b c in
          ans := sub s !b (e - !b) :: !ans;
          b := e+1
        done;
        assert false
      with
      | Not_found -> List.rev (sub s !b (length s - !b) :: !ans)

  let substrings s =
    let ans = ref [""] in
    for l = 1 to String.length s do
      for i = 0 to String.length s - l do
        ans := String.sub s i l :: !ans
      done;
    done;
    !ans

  let concat_map s f l =
    String.concat s (List.map f l)

end

module Char = struct
  let is_digit c =
    let c = int_of_char c in
    int_of_char '0' <= c && c <= int_of_char '9'

  let to_int c =
    int_of_char c - int_of_char '0'
end

(** Operations initial segments of integers. *)
module Int = struct
  let for_all f n =
    try
      for i = 0 to n - 1 do
        if not (f i) then raise Exit
      done;
      true
    with
    | Exit -> false

  let iter f n =
    for i = 0 to n - 1 do
      f i
    done

  let fold_left f x n =
    let x = ref x in
    iter (fun i -> x := f !x i) n;
    !x

  let list n =
    List.init n id
end

module Option = struct
  let default x = function
    | Some x -> x
    | None -> x

  let get = function
    | Some x -> x
    | None -> raise Not_found

  let map f = function
    | Some x -> Some (f x)
    | None -> None
end

module UTF8 = struct
  let subscript n =
    let digit = function
      | 0 -> "₀"
      | 1 -> "₁"
      | 2 -> "₂"
      | 3 -> "₃"
      | 4 -> "₄"
      | 5 -> "₅"
      | 6 -> "₆"
      | 7 -> "₇"
      | 8 -> "₈"
      | 9 -> "₉"
      | _ -> assert false
    in
    if n = 0 then digit 0 else
      let ans = ref "" in
      let n = ref n in
      while !n <> 0 do
        ans := digit (!n mod 10) ^ !ans;
        n := !n / 10
      done;
      !ans
end

(** Enumerations. *)
module Enum = struct
  type 'a t = unit -> 'a

  exception End

  let get (e : 'a t) = e ()

  let make (f : unit -> 'a) : 'a t = f

  let empty = make (fun () -> raise End)

  let of_list l =
    let l = ref l in
    make (fun () ->
      match !l with
      | x::t -> l := t; x
      | [] -> raise End)

  let singleton x =
    of_list [x]

  let append e e' =
    fun () -> try get e with End -> get e'

  (** Interval from [p] (included) to [q] (excluded). *)
  let interval p q =
    let k = ref (p-1) in
    make (fun () -> incr k; if !k = q then raise End else !k)

  let int n =
    interval 0 n

  let iter f e =
    try
      while true do f (get e) done
    with
    | End -> ()

  let map f e =
    fun () -> f (get e)

  let rec bind f e =
    fun () -> get (append (f (get e)) (bind f e))

  let rec bind (f : 'a -> 'b t) (e : 'a t) : 'b t =
    let ee = ref (f (get e)) in
    fun () ->
      try
        get !ee
      with
      | End -> get (bind f e)

  let length e =
    let n = ref 0 in
    iter (fun _ -> incr n) e;
    !n
end
