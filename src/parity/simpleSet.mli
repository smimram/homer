type 'a t

(** {2 Creation} *)

val empty : 'a t

val singleton : 'a -> 'a t

val make : 'a list -> 'a t

val add : 'a t -> 'a -> 'a t

(** {2 Destruction} *)

val to_string : string -> ('a -> string) -> 'a t -> string

val card : 'a t -> int

(** Arbitrary element of a set. *)
val element : 'a t -> 'a

val the_element : 'a t -> 'a

val to_list : 'a t -> 'a list

(** {2 Operations} *)

val union : 'a t -> 'a t -> 'a t

val inter : 'a t -> 'a t -> 'a t

val remove : 'a t -> 'a -> 'a t

(** Difference: elements in a set but not in the other. *)
val diff : 'a t -> 'a t -> 'a t

(** Same as difference excepting that the second set is supposed to be included
    in the first one. *)
val minus : 'a t -> 'a t -> 'a t

val filter : ('a -> bool) -> 'a t -> 'a t

(** {2 Tests} *)

val mem : 'a t -> 'a -> bool

val is_empty : 'a t -> bool

val is_singleton : 'a t -> bool

val included : 'a t -> 'a t -> bool

(** Comparison for sets. *)
val eq : 'a t -> 'a t -> bool

val exists : ('a -> bool) -> 'a t -> bool

val for_all : ('a -> bool) -> 'a t -> bool

(** {2 Iterators} *)

val iter : ('a -> unit) -> 'a t -> unit

val iter_ordered_pairs : ('a -> 'a -> unit) -> 'a t -> unit

val map : ('a -> 'b) -> 'a t -> 'b t

val fold : ('a -> 'b -> 'a) -> 'a -> 'b t -> 'a

val bind : ('a -> 'b t) -> 'a t -> 'b t

val bind_pairs : ('a -> 'b -> 'c t) -> 'a t -> 'b t -> 'c t
