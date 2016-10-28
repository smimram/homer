(** Functions. *)

type ('a,'b) t = ('a * 'b) list

let empty : ('a,'b) t = []

let app (f : ('a,'b) t) x =
  List.assoc x f

let may_app d f x =
  try
    app f x
  with
  | Not_found -> d

let remove (f : ('a,'b) t) x : ('a,'b) t =
  List.remove_assoc x f

let add f x y : ('a,'b) t =
  let f = remove f x in
  (x,y)::f

let replace f x y =
  add (remove f x) x y

let map f g : ('a,'b) t =
  List.map (fun (x,y) -> x, g y) f
