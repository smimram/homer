(** Free groups. *)

open Standard

(** Free group on a given list of generators. *)
type 'a group = 'a list

(** An element of a free group. *)
type 'a t = ('a * int) list

type 'a element = 'a t

(** Create a free group. *)
let make : 'a list -> 'a group = fun l -> l

(** Canonize the internal representation of an element. This does not change the
    element. *)
let reduce x =
  List.filter (fun (g,n) -> n <> 0) x

let to_string_simple gen x =
  String.concat_map "+" (fun (g,n) -> Printf.sprintf "%d%s" n (gen g)) x

let to_string ?(mul="") gen x =
  let x = reduce x in
  let ans = ref "" in
  let s s = ans := !ans ^ s in
  List.iter
    (fun (g,n) ->
      if n >= 0 then (if !ans <> "" then s "+") else s "-";
      if n <> 1 && n <> -1 then s (string_of_int (abs n) ^ mul);
      s (gen g)
    ) x;
  !ans
(* let to_string = to_string_simple *)

let zero : 'a t = []

let cgen n (x:'a) : 'a t = [x,n]

let generator x = cgen 1 x

let gen = generator

(** Coefficient of a generator. *)
let coeff g x =
  try List.assoc g x with Not_found -> 0

let dom (x : 'a t) : 'a list =
  List.may_map (fun (g,n) -> if n <> 0 then Some g else None) x

(** Multiply by a coefficient. *)
let cmul k x : 'a t =
  List.map (fun (g,n) -> g,k*n) x

let add x y : 'a t =
  List.map (fun g -> g, coeff g x + coeff g y) (List.union (dom x) (dom y))

let sub x y : 'a t =
  List.map (fun g -> g, coeff g x - coeff g y) (List.union (dom x) (dom y))

let neg x =
  List.map (fun (g,n) -> g,-n) x

let eq x y =
  List.for_all (fun g -> coeff g x = coeff g y) (List.union (dom x) (dom y))

let neq x y = not (eq x y)

let is_zero x =
  eq x zero

(* Put in internal representation by removing duplicates. *)
let canonize l : 'a t =
  List.map (fun g ->
    let nn = List.may_map (fun (g', n) -> if g' = g then Some n else None) l in
    g, List.fold_left (+) 0 nn
  ) (dom l)

let map f (x:'a t) =
  canonize (List.map (fun (g,n) -> f g,n) x)

let iter f (x:'a t) =
  List.iter (fun (g,n) -> if n <> 0 then f n g) x

(** Linear extension of a function on generators. *)
let bind (f : 'a -> 'b t) (x : 'a t) =
  let x = List.map (fun (g,n) -> cmul n (f g)) x in
  List.fold_left add zero x

let rec dist_list : 'a t list -> 'a list t = function
  | x::l ->
     bind (fun x ->
       let l = dist_list l in
       map (fun l -> x::l) l
     ) x
  | [] -> gen []

let dist_array a =
  map Array.of_list (dist_list (Array.to_list a))

(** Leading monomial. *)
let leading ?(compare=compare) x =
  assert (not (is_zero x));
  let x = reduce x in
  let g,n = List.hd x in
  let g,n = List.fold_left (fun (g,n) (g',n') -> if compare g g' = -1 then g',n' else g,n) (g,n) x in
  assert (n <> 0);
  n,g

(** {2 Operations on sums with positive coefficients (multisets). } *)

let target x =
  List.filter (fun (g,n) -> n > 0) x

let source x =
  List.may_map (fun (g,n) -> if n < 0 then Some (g, -n) else None) x

let is_set x =
  List.for_all (fun (_,n) -> n = 0 || n = 1) x

let list_of_set x =
  assert (is_set x);
  List.may_map (fun (g,n) -> if n <> 0 then Some g else None) x

(*

let positive x =
  List.for_all (fun (_,n) -> n >= 0) x

let is_multiset = positive

(** Inclusion of multisets. *)
let included x y =
  assert (positive x);
  assert (positive y);
  List.for_all (fun (g,n) -> n <= coeff g y) x

(** Intersection of multisets. *)
let inter x y =
  assert (positive x);
  assert (positive y);
  List.map (fun (g,n) -> g, min n (coeff g y)) x
*)

(** Linear functions between groups. *)
module Map = struct
  module Map = SimpleMap

  type ('a,'b) t = ('a,'b element) Map.t

  let set (f:('a,'b) t) x y : ('a,'b) t =
    Map.add f x y

  let app (f:('a,'b) t) (x:'a) : 'b element =
    try
      Map.app f x
    with
    | Not_found -> zero

  let zero : ('a,'b) t =
    Map.empty
end
