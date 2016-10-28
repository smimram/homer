(** Higher-dimensional precategories. *)

(** The free precategory on a globular set. *)
module Free (G : Globular.T) = struct
  (** A cell. *)
  type t =
    | C of whisker * t (** a composite *)
    | I of t (** an identity *)
  (** A whiskered generator. *)
  and whisker =
    | G of G.t (** a generator *)
    | W of t * whisker * t (** a whisker context *)

  (** String representation of a cell. *)
  let to_string c =
    let rec list = function
      | C (w,c) -> w::(list c)
      | I _ -> []
    in
    let rec cell = function
      | C _ as c -> "[" ^ String.concat "|" (List.map whisker (list c)) ^ "]"
      | I c -> "[" ^ cell c ^ "]"
    and whisker = function
      | G g -> G.to_string g
      | W (c1,w,c2) -> cell c1 ^ whisker w ^ cell c2
    in
    cell c

  (** Dimension of a cell. *)
  let dim c =
    let rec cell = function
      | C (w,_) -> whisker w
      | I c -> cell c + 1
    and whisker = function
      | G g -> G.dim g
      | W (_,w,_) -> whisker w
    in
    cell c

  (** Codimension of a whisker: the dimension on which it should be composed. *)
  let rec codim = function
    | G _ -> 0
    | W (_,w,_) -> codim w + 1
end
