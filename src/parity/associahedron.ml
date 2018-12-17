(** The associahedron. *)

open Standard

module G = FreeGroup

(** Trees with node of arity at least two. *)
module Tree = struct
  type t =
    | Node of t array
    | Leaf

  let rec to_string = function
    | Node tt ->
       "(" ^ String.concat_map "" to_string (Array.to_list tt) ^ ")"
    | Leaf -> "."

  let node tt =
    assert (Array.length tt >= 2);
    Node tt

  let leaf = Leaf

  let corolla n =
    node (Array.make n leaf)

  (** Dimension of a tree: the number of nodes that can be split. *)
  let rec dim = function
    | Leaf -> 0
    | Node a -> (Array.length a - 2) + (Array.fold_left (+) 0 (Array.map dim a))

  (** Boundary of a tree: splits a node in two and extend as a derivation. *)
  let rec diff = function
    | Node a ->
       let ans = ref G.zero in
       let add k t = ans := G.add !ans (G.cmul (if k mod 2 = 0 then 1 else - 1) t) in
       let n = Array.length a in
       (* We split the node. *)
       for i = 2 to n - 1 do (* arity of node below *)
         let i' = n + 1 - i in (* arity of node above *)
         for j = 0 to i - 1 do (* position of node above *)
           let a' = Array.init i
             (fun k ->
               if k < j then
                 a.(k)
               else if k = j then
                 let a'' = Array.init i' (fun k -> a.(k+j)) in
                 Node a''
               else
                 a.(k+i'-1)
             )
           in
           (* Printf.printf "%d o (%d * %d * %d) => %d\n" i j i' (n-(j+i')) (j+i'*(n-(j+i'))); *)
           add (j+i'*(n-(j+i'))) (G.gen (Node a'))
         done
       done;
       (* We recurse at position i. *)
       for i = 0 to n - 1 do
         let t =
           G.bind (fun t ->
             let a = Array.init n (fun j -> if j = i then t else a.(j)) in
             G.gen (node a)
           ) (diff a.(i))
         in
         let p = ref n in
         for j = 0 to i - 1 do
           p := !p + dim a.(j)
         done;
         add !p t
       done;
       !ans
    | Leaf -> G.zero

  (* let () = *)
    (* let t = corolla 5 in *)
    (* Printf.printf "%s\n%!" (to_string t); *)
    (* let d = diff t in *)
    (* Printf.printf "diff:\n%s\n%!" (G.to_string to_string d) *)
end

open Parity

let parity n =
  let s = ref Sig.empty in
  (* Add a given tree to the signature. *)
  let rec aux t =
    let ts = Tree.to_string t in
    if not (Sig.mem !s ts) then
      let d = Tree.diff t in
      assert (G.eq (G.bind Tree.diff d) G.zero);
      List.iter aux (G.dom d);
      let src = G.source d in
      let tgt = G.target d in
      let src = G.list_of_set src in
      let tgt = G.list_of_set tgt in
      let src = List.map Tree.to_string src in
      let tgt = List.map Tree.to_string tgt in
      let src = Set.make src in
      let tgt = Set.make tgt in
      s := Sig.add !s ts (Tree.dim t) (src,tgt)
  in
  aux (Tree.corolla (n+2));
  !s

(*
let () =
  let s = parity 2 in
  let c = Cell.full s in
  Cell.check s c
*)

let () =
  let f s c a =
    let n = int_of_string a.(0) in
    let s = parity n in
    s, Cell.full s
  in
  LangParity.register "associahedron" "Generate an associahedron." 1 f;
  LangParity.register "ass" "Generate an associahedron." 1 f
