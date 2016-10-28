(** Some tests with parity complexes. *)

open Parity

let () =
  LangParity.register "street_gs" "Tensor of globe times simplex (as in Street's example)." 1 (fun s c a ->
    let n = int_of_string a.(0) in
    let s1 = GenerateParity.globe n in
    let s2 = GenerateParity.simplex n in
    let s = Sig.tensor s1 s2 in
    s, Cell.full s
  )

