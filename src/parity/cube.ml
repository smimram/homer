(** Operations on basic cubes. *)
module Cube = struct
  type t = string

  let inj_source c : t = c ^ "-"

  let inj_target c : t = c ^ "+"

  let extrude c : t = c ^ "0"

  let standard n : t = String.make n '0'

  let length = String.length

  let dim c =
    let ans = ref 0 in
    for i = 0 to length c - 1 do
      if c.[i] = '0' then incr ans
    done;
    !ans

  let is_standard c =
    dim c = length c

  (** Operations on contexts, which are embeddings into higher-dimensional
      cubes. *)
  module Context = struct
    (** A context. *)
    (* Positions are strictly increasing and chars are '-' or '+'. *)
    type t = (int * char) list

    (** The context of the standard cube in a cube. *)
    let standard c =
      let ans = ref [] in
      for i = length c - 1 downto 0 do
        if c.[i] <> '0' then ans := (i,c.[i]) :: !ans
      done;
      !ans

    (** Apply a context. *)
    let app k c =
      let ci = ref (-1) in
      let k = ref k in
      String.init
        (List.length !k + length c)
        (fun i ->
          match !k with
          | (j,x)::k' when j = i -> k := k'; x
          | _ -> incr ci; c.[!ci]
        )
  end
end

module Cat = struct
  include Parity.Cat

(*
  let rec source = function
    | Seq (n,l) -> failwith "TODO"
    | Id f -> failwith "TODO"
    | Gen c ->
       let n = Cube.dim c in
       if Cube.is_standard c then
         let f = ... in
         let g = ... in
         Seq (n-2,[f;g])
*)
end
