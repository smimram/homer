(** Generate signatures for common complexes. *)

open Standard
open Parity

(** Generate the signature corresponding to the [n]-globe. *)
let globe ?(src=fun i -> "x"^string_of_int i) ?(tgt=fun i -> "y"^string_of_int i) ?(top="z") n =
  let x = Array.init n src in
  let y = Array.init n tgt in
  let z = top in
  let d n =
    if n = 0 then
      Set.empty, Set.empty
    else
      Set.singleton x.(n-1), Set.singleton y.(n-1)
  in
  let s = ref Sig.empty in
  for i = 0 to n-1 do
    s := Sig.add !s x.(i) i (d i);
    s := Sig.add !s y.(i) i (d i)
  done;
  Sig.add !s z n (d n)

(** n-cube. *)
let cube n =
  (* Point *)
  let p = Sig.empty in
  let p = Sig.add p "0" 0 (Set.empty, Set.empty) in
  (* Interval *)
  let i = Sig.empty in
  let i = Sig.add i "-" 0 (Set.empty, Set.empty) in
  let i = Sig.add i "+" 0 (Set.empty, Set.empty) in
  let i = Sig.add i "0" 1 (Set.singleton "-", Set.singleton "+") in
  if n = 0 then p else Int.fold_left (fun s _ -> Sig.tensor ~sep:"" s i) i (n-1)

(** n-simplex (or oriental). *)
let simplex n =
  (* Strictly increasing subsets of integers from 0 (included) to (n+1)
     (excluded) of size len starting at postition pos. *)
  let rec subsets pos len =
    if len = 0 then
      [[]]
    else if pos >= n + 1 || n+1 - pos < len then
      []
    else
      (* Interval from pos to n+1 *)
      let posint = List.init (n+1-pos) (fun i -> pos + i) in
      List.bind (fun pos ->
        let x = pos in
        let s = (subsets (pos+1) (len-1)) in
        List.map (fun l -> x::l) s
      ) posint
  in
  let subsets = subsets 0 in
  let sep = if n <= 9 then "" else "|" in
  let gen l = String.concat_map sep string_of_int l in
  let s = ref Sig.empty in
  for i = 0 to n do
    List.iter
      (fun l ->
        let src = ref Set.empty in
        let tgt = ref Set.empty in
        let is_src = ref false in
        List.iter_ctx
          (fun h x t ->
            let l' = (List.rev h)@t in
            let d = if !is_src then src else tgt in
            is_src := not !is_src;
            (* Printf.printf "adding %s\n%!" (gen l'); *)
            d := Set.add !d (gen l')
          ) l;
        if i = 0 then (src := Set.empty; tgt := Set.empty);
        s := Sig.add !s (gen l) i (!src,!tgt)
      ) (subsets (i+1))
  done;
  !s
