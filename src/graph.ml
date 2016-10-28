(** Operations on graphs with labeled edges. *)

type ('vertex,'edge) t =
  {
    vertices : 'vertex list;
    edges : ('vertex * 'edge * 'vertex) list;
  }

let empty = { vertices = []; edges = [] }

let make vertices edges = { vertices; edges }

module Vertex = struct
  let is_source g x =
    List.exists (fun (x',_,_) -> x' = x) g.edges

  let is_target g x =
    List.exists (fun (_,_,x') -> x' = x) g.edges

  let initial g =
    List.filter (fun x -> not (is_target g x)) g.vertices

  let terminal g =
    List.filter (fun x -> not (is_source g x)) g.vertices
end

module Edge = struct
  let border g a =
    let rec aux = function
      | (x,a',y)::_ when a' = a -> x,y
      | _::edges -> aux edges
      | [] -> raise Not_found
    in
    aux g.edges

  let source g a =
    fst (border g a)

  let target g a =
    snd (border g a)
end

module Path = struct
  type ('vertex,'edge) t =
    | Empty of 'vertex
    | Edge of 'edge * ('vertex,'edge) t

  let source g = function
    | Empty x -> x
    | Edge (a,_) -> Edge.source g a

  let rec target g = function
    | Empty x -> x
    | Edge (_,p) -> target g p

  let append g p q =
    assert (target g p = source g q);
    let rec aux = function
      | Empty _ -> q
      | Edge (a,q) -> Edge (a, aux q)
    in
    aux p

  let empty x = Empty x

  let is_empty = function
    | Empty _ -> true
    | _ -> false

  let edge g a =
    let x = Edge.target g a in
    Edge (a, Empty x)

(*
  let rec to_string = function
    | Empty x -> "id("^x^")"
    | Edge (a,Empty _) -> a
    | Edge (a,p) -> a^"."^to_string p
*)

  let rec to_string = function
    | Empty x -> ""
    | Edge (a,Empty _) -> a
    | Edge (a,p) -> a^"."^to_string p
end

module Poset = Poset.Labeled

(** Ensure that a graph is acyclic. *)
let acyclic g =
  let le = Poset.create g.vertices in
  try
    List.iter (fun (x,_,y) -> Poset.add le x y) g.edges;
    true
  with
  | Poset.Cyclic -> false
     
(** Paths in an acyclic graph. *)
(* TODO: this function has horrible complexity, improve it *)
let paths g =
  assert (acyclic g);
  let ans = ref (List.map (fun x -> Path.empty x) g.vertices) in
  let add p =
    if not (List.mem p !ans) then ans := p :: !ans
  in
  List.iter (fun (x,a,y) ->
    List.iter (fun p ->
      if Path.source g p = y then add (Path.append g (Path.edge g a) p);
      if Path.target g p = x then add (Path.append g p (Path.edge g a))
    ) !ans
  ) g.edges;
  !ans

(*
let () =
  let g =
    {
      vertices = ["x";"y";"z";"t"]; edges =
      [
        "x","a","y";
        "y","b","z";
        "x","c","z";
        "z","d","t"
      ]
    }
  in
  let pp = paths g in
  List.iter (fun p -> print_endline (Path.to_string p)) (List.rev pp);
  assert false
*)
