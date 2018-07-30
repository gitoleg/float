open Bap.Std

type gfloat

type rounding =
  | Nearest_even  (** round to nearest, ties to even *)
  | Nearest_away  (** round to nearest, ties to away *)
  | Towards_zero  (** round toward zero              *)
  | Positive_inf  (** round toward positive infinity *)
  | Negative_inf  (** round toward negative infinity *)

(** [mk ~base expn frac]  *)
val mk : base:int -> ?negative:bool -> word -> word -> gfloat

(** [mk ~base expn_bits prec]  *)
val mk_zero : base:int -> expn_bits:int -> int -> gfloat

(** [mk_inf ~base prec] *)
val mk_inf : base:int -> ?negative:bool -> int -> gfloat

(** [mk_nan ~base prec ] *)
val mk_nan : ?signaling:bool -> ?negative:bool -> base:int -> int -> gfloat

val is_fin : gfloat -> bool
val is_nan : gfloat -> bool
val is_inf : gfloat -> bool
val is_pos : gfloat -> bool
val is_neg : gfloat -> bool
val is_zero : gfloat -> bool

val fin  : gfloat -> (word * word) option
val frac : gfloat -> word option
val expn : gfloat -> word option

val add : ?rm:rounding -> gfloat -> gfloat -> gfloat
val sub : ?rm:rounding -> gfloat -> gfloat -> gfloat
val mul : ?rm:rounding -> gfloat -> gfloat -> gfloat
val div : ?rm:rounding -> gfloat -> gfloat -> gfloat
val sqrt :   ?rm:rounding -> gfloat -> gfloat


val truncate : ?rm:rounding -> upto:int -> gfloat -> gfloat option
