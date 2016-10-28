open Stdlib

module G = FreeGroup

(** Operations on sujections. *)
module Surj = struct
  (** A surjection coded as the indices of the images. *)
  type t = int array

  let corolla n =
    Array.make n 0

  (** Number of elements in the source. *)
  let source f = Array.length f

  (** Number of elements in the target. *)
  let target f =
    (Array.fold_left max (-1) f) + 1

  let app f i =
    assert (i < source f);
    f.(i)

  (** Pre-image of an element. *)
  let preimage f k =
    assert (k < target f);
    let ans = ref [] in
    for i = source f - 1 downto 0 do
      if app f i = k then ans := i :: !ans
    done;
    assert (!ans <> []);
    !ans

  let to_string ?(repr=`Images) f =
    match repr with
    | `Images ->
       (* TODO: find a representation for those *)
       assert (source f < 10);
       let f = Array.to_list f in
       String.concat_map "" string_of_int f
    | `Ordered_partition ->
       assert (source f < 10);
       let ans = ref "" in
       for i = 0 to target f - 1 do
         if !ans <> "" then ans := !ans ^ "|";
         ans := !ans ^ String.concat_map "" string_of_int (preimage f i)
       done;
       !ans

  (** Shuffle corresponding to a surjection. *)
  let shuffle f =
    let ans = ref [] in
    for i = 0 to target f - 1 do
      ans := !ans@(preimage f i)
    done;
    Array.of_list !ans

  (** Unshuffle (inverse of the shuffle). *)
  let unshuffle f =
    let f = shuffle f in
    let n = source f in
    assert (target f = n);
    Array.init n (fun i ->
      let l = preimage f i in
      assert (List.length l = 1);
      List.hd l)

  (** Degree of a surjection. *)
  let dim ?k f =
    let k = Option.default (target f) k in
    let ans = ref 0 in
    for i = 0 to k - 1 do
      ans := !ans + List.length (preimage f i) - 1
    done;
    !ans

  (** Shift image by one starting from [k] (included). *)
  let shift f k =
    Array.map (fun i -> if i >= k then i + 1 else i) f

  let unshift f k =
    assert (k > 0);
    Array.map (fun i -> if i >= k then i - 1 else i) f

  (** Given two increasing lists, compute the sign of their exterior product. *)
  let exterior_sign l1 l2 =
    let sign =
      List.count (fun i ->
        List.count (fun j -> if j < i then 1 else 0) l2
      ) l1
    in
    koszul sign

  (** Differential. *)
  let diff f =
    (* Non-empty partitions of a list. *)
    let partitions l =
      (* Take or not each element. *)
      let rec aux = function
        | x::l ->
           let l = aux l in
           (List.map (fun l -> x::l) l)@l
        | [] -> [[]]
      in
      let ans = aux l in
      let ans = List.map (fun l1 -> l1, List.diff l l1) ans in
      List.filter (fun (l1,l2) -> l1 <> [] && l2 <> []) ans
    in
(*
    let partitions l =
      let ll = partitions l in
      let s = String.concat_map "" string_of_int in
      Printf.printf "partitions %s = %s\n" (s l) (String.concat_map " " (fun (l1,l2) -> s l1 ^ "," ^ s l2) ll);
      ll
    in
*)
    let ans = ref G.zero in
    for j = 0 to target f - 1 do
      let l = preimage f j in
      let len = List.length l in
      if len > 1 then
        List.iter (fun (l1,l2) ->
          (* Put l1 before. *)
          let f' = shift f j in
          List.iter (fun i -> f'.(i) <- j) l1;
          let sign = koszul (dim ~k:(j+1) f') * exterior_sign l1 l2 in
          ans := G.add !ans (G.cgen sign f');
        ) (partitions l)
    done;
    !ans

(*
  let () =
    let f = corolla 3 in
    (* let f = [|0;0;1|] in *)
    Printf.printf "%s\n%!" (to_string f);
    (* Printf.printf "%d\n" (dim f); *)
    let f' = diff f in
    Printf.printf "%s\n%!" (G.to_string to_string f');
    let f'' = G.bind diff f' in
    Printf.printf "%s\n%!" (G.to_string ~mul:"*" to_string f'');
    assert false
*)

  (** Generate all bijections on n elements. *)
  let bijections n =
    let rec aux k =
      if k = 0 then [[]] else
        List.bind (fun l ->
          let ans = ref [] in
          for i = 0 to n - 1 do
            if not (List.mem i l) then ans := (i::l) :: !ans
          done;
          !ans
        ) (aux (k-1))
    in
    List.map Array.of_list (aux n)

(*
  let () =
    let l = bijections 5 in
    Printf.printf "%s\n" (String.concat_map "\n" to_string l);
    assert false
*)

  (** Codifferential. *)
  (* From Chapoton's Opérades différentielles graduées sur les simplexes et les
     permutoèdres. *)
  let codiff f =
    let ans = ref G.zero in
    for i = 0 to target f - 2 do
      let sign = koszul (dim ~k:(i+1) f) in
      let sign = sign * exterior_sign (preimage f i) (preimage f (i+1)) in
      let f' = unshift f (i+1) in
      ans := G.add !ans (G.cgen sign f')
    done;
    !ans

(*
  let () =
    let l = bijections 4 in
    List.iter (fun f ->
      let f' = codiff f in
      let f'' = G.bind codiff f' in
      Printf.printf "d(%s) = %s / %s\n" (to_string f) (G.to_string ~mul:"*" to_string f') (G.to_string ~mul:"*" to_string f'')
    ) l;
    assert false
*)
end

open Parity

let parity ?repr n =
  let s = ref Sig.empty in
  (* Add a given surjection to the signature. *)
  let rec aux f =
    let fs = Surj.to_string ?repr f in
    if not (Sig.mem !s fs) then
      let d = Surj.diff f in
      (* Check that we do have a chain complex. *)
      assert (G.eq (G.bind Surj.diff d) G.zero);
      List.iter aux (G.dom d);
      let src = G.source d in
      let tgt = G.target d in
      let src = G.list_of_set src in
      let tgt = G.list_of_set tgt in
      let src = List.map (Surj.to_string ?repr) src in
      let tgt = List.map (Surj.to_string ?repr) tgt in
      let src = Set.make src in
      let tgt = Set.make tgt in
      (* Printf.printf "%d %s : %s -> %s\n%!" (Surj.dim f) fs (Set.to_string src) (Set.to_string tgt); *)
      s := Sig.add !s fs (Surj.dim f) (src,tgt)
  in
  aux (Surj.corolla (n+1));
  !s

let () =
  let f ?repr s c a =
    let n = int_of_string a.(0) in
    let s = parity ?repr n in
    s, Cell.full s
  in
  LangParity.register "permutohedron" "Generate a permutohedron." 1 f;
  LangParity.register "perm" "Generate a permutohedron." 1 f;
  LangParity.register "perm'" "Generate a permutohedron (ordered partition notation)." 1 (f ~repr:`Ordered_partition);
  LangParity.register "dperm" "Debug permutohedron construction: generate reoriented permutohedra." 1
    (fun s c a ->
      let n = int_of_string a.(0) in
      let s = parity n in
      let s =
        if n = 3 then
          List.fold_left Sig.bireorient s
            ["1100";"1010"]
        else if n = 4 then
          List.fold_left Sig.bireorient s
            ["21100";"21010";"12100";"12010";"11200";"10210";"11020";"10120";"11002";"10102"]
        else
          s
      in
      s, Cell.full s
    )
