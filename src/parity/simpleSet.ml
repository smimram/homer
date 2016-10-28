(** Sets. *)

open Stdlib

(** A set. *)
type 'a t = 'a list

let make (s : 'a list) : 'a t = s

let to_list s = s

let to_string sep gen s =
  String.concat_map sep gen s

let empty = []

let singleton x = [x]

(** Cardinal of a set. *)
let card s = List.length s

let mem s x =
  List.mem x s

let add s x =
  (* We append in order to have printing in the order of insertion. *)
  if mem s x then s else s@[x]

let union s t =
  List.fold_left add s t

let filter = List.filter

let inter s t =
  filter (mem t) s

let remove s x =
  assert (mem s x);
  filter (fun y -> y <> x) s

let diff s t =
  filter (fun x -> not (mem t x)) s

let minus s t =
  List.fold_left remove s t

let is_empty = function
  | [] -> true
  | _ -> false

let is_singleton = function
  | [_] -> true
  | _ -> false

let element s =
  assert (not (is_empty s));
  List.hd s

let the_element s =
  assert (is_singleton s);
  element s

let for_all = List.for_all

let included s t =
  for_all (mem t) s

let eq s t =
  included s t && included t s

let iter f s =
  List.iter f s

let map f s =
  List.map f s

let bind f s =
  List.flatten (List.map f s)

let bind_pairs f s t =
  bind (fun x -> bind (fun y -> f x y) t) s

let iter_ordered_pairs f s =
  List.iter_ordered_pairs f s

let exists p s = List.exists p s

let fold = List.fold_left
