module S = Parity.Signature
module C = Parity.Cell
module Cat = Parity.Cat
module Sig = GenerateParity

(*
let () =
  let globe = Sig.globe 4 in
  Printf.printf "%s\n%!" (S.to_string globe);
  Printf.printf "***************\n\n%!"

let () =
  let a = "a" in
  let b = "b" in
  let c = "c" in
  let d = "d" in
  let f = "f" in
  let g1 = "g1" in
  let g2 = "g2" in
  let g3 = "g3" in
  let h = "h" in
  let p = "p" in
  let q = "q" in
  let s = S.empty in
  let s = S.add s a 0 (Set.empty, Set.empty) in
  let s = S.add s b 0 (Set.empty, Set.empty) in
  let s = S.add s c 0 (Set.empty, Set.empty) in
  let s = S.add s d 0 (Set.empty, Set.empty) in
  let s = S.add s f 1 (Set.make [a], Set.make [c]) in
  let s = S.add s g1 1 (Set.make [a], Set.make [b]) in
  let s = S.add s g2 1 (Set.make [b], Set.make [c]) in
  let s = S.add s g3 1 (Set.make [c], Set.make [d]) in
  let s = S.add s h 1 (Set.make [b], Set.make [d]) in
  let s = S.add s p 2 (Set.make [f], Set.make [g1;g2]) in
  let s = S.add s q 2 (Set.make [g2;g3], Set.make [h]) in
  Printf.printf "signature:\n%s\n\n%!" (S.to_string s);
  let c = C.generators s 2 (Set.make [p;q]) in
  (* let c = C.union s c (C.id s (C.generator s g3)) in *)
  Printf.printf "cell: %s\n\n%!" (C.to_string c);
  Printf.printf "cell source: %s\n\n%!" (C.to_string (C.source s c));
  let c = Cat.of_cell s c in
  Printf.printf "composition: %s\n\n%!" (Cat.to_string c);
  (* Printf.printf "composition: %s\n\n%!" (Cat.to_string (Cat.simpl c)); *)
  Printf.printf "***************\n\n%!"
*)

(*
let () =
  (* Parity.composition := `Categorical; *)
  Parity.show_identities := false;
  let n1, n2 =
    if Array.length Sys.argv > 2 then
      int_of_string Sys.argv.(1), int_of_string Sys.argv.(2)
    else
      2, 2
  in
  let globe x n = Sig.globe ~src:(fun i -> x^string_of_int i^"⁻") ~tgt:(fun i -> x^string_of_int i^"⁺") ~top:x n in
  let s1 = globe "x" n1 in
  let s2 = globe "y" n2 in
  Printf.printf "sig 1:\n%s\n\n%!" (S.to_string s1);
  Printf.printf "sig 2:\n%s\n\n%!" (S.to_string s2);
  let c1 = C.full s1 in
  let c2 = C.full s2 in
  Printf.printf "cell 1: %s\n\n%!" (C.to_string c1);
  Printf.printf "cell 2: %s\n\n%!" (C.to_string c2);
  let s3 = S.tensor s1 s2 in
  let c3 = C.full s3 in
  Printf.printf "sig 3:\n%s\n\n%!" (S.to_string s3);
  Printf.printf "cell 3:   %s\n\n%!" (C.to_string c3);
  let c3s = C.source s3 c3 in
  let c3t = C.target s3 c3 in
  Printf.printf "source 3: %s\n\n%!" (C.to_string c3s);
  let c3s = Cat.of_cell s3 c3s in
  Printf.printf "    comp: %s\n\n%!" (Cat.to_string c3s);
  Printf.printf "   simpl: %s\n\n%!" (Cat.to_string (Cat.simpl s3 c3s));
  Printf.printf "target 3: %s\n\n%!" (C.to_string c3t);
  let c3t = Cat.of_cell s3 c3t in
  Printf.printf "    comp: %s\n\n%!" (Cat.to_string c3t);
  Printf.printf "   simpl: %s\n\n%!" (Cat.to_string (Cat.simpl s3 c3t))
*)

(*
let () =
  (* Parity.composition := `Categorical; *)
  Parity.show_identities := false;
  Parity.use_utf8 := false;
  for n1 = 1 to 4 do
    for n2 = 1 to 4 do
      let globe x n = Sig.globe ~src:(fun i -> x^string_of_int i^"⁻") ~tgt:(fun i -> x^string_of_int i^"⁺") ~top:x n in
      let s1 = globe "x" n1 in
      let s2 = globe "y" n2 in
      let c1 = C.full s1 in
      let c2 = C.full s2 in
      let s3 = S.tensor s1 s2 in
      let c3 = C.full s3 in
      let c3s = C.source s3 c3 in
      let c3t = C.target s3 c3 in
      let c3s = Cat.of_cell s3 c3s in
      (* Printf.printf "   simpl: %s\n\n%!" (Cat.to_string (Cat.simpl s3 c3s)); *)
      let c3t = Cat.of_cell s3 c3t in
      Printf.printf "%d %d: %s\n\n%!" n1 n2 (Cat.to_string (Cat.simpl s3 c3t))
    done
  done
*)

let () =
  let s = Sig.cube 5 in
  let c = C.full s in
  let c = C.source s c in
  let c = C.source s c in
  let c = Cat.of_cell s c in
  let c = Cat.simpl s c in
  Printf.printf "%s\n%!" (Cat.to_string c)
