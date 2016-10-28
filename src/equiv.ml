(** Equivalence relations. *)

module Map = SimpleMap

type 'a t = ('a,'a) Map.t

let empty : 'a t = Map.empty

(** Create a discrete equivalence relation. *)
let make l : 'a t =
  List.fold_left (fun f x -> Map.add f x x) empty l

(** Normal form of an element. *)
let nf (r : 'a t) x =
  Map.app r x

(** Comparison modulo an equivalence relation. *)
let eq r x y =
  nf r x = nf r y

(** Add a relation. *)
let add r x y : 'a t =
  let x = nf r x in
  let y = nf r y in
  let z = min x y in
  if x = y then r else
    Map.map r (fun z' -> if z' = x || z' = y then z else z')

(** Is an equivalence relation the full one? *)
let is_full (r : 'a t) =
  if r = [] then true else
    let _,x = List.hd r in
    List.for_all (fun (_,y) -> y = x) r
