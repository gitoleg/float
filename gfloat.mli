open Bap.Std

type gfloat

type rounding =
  | Nearest_even  (** round to nearest, ties to even *)
  | Nearest_away  (** round to nearest, ties to away *)
  | Towards_zero  (** round toward zero              *)
  | Positive_inf  (** round toward positive infinity *)
  | Negative_inf  (** round toward negative infinity *)

(** [create ~radix expn frac] creates gfloat from radix, signed expn
    and fraction.  *)
val create : radix:int -> ?negative:bool -> word -> word -> gfloat

(** [zero ~radix expn_bits prec] creates gfloat equaled to zero from
    radix, exponent bits and precision *)
val zero : radix:int -> expn_bits:int -> int -> gfloat

(** [inf ~radix prec] creates positive or negative infinity from radix
    and precision *)
val inf : radix:int -> ?negative:bool -> int -> gfloat

(** [nan ~radix prec] creates nan from radix and precision. *)
val nan : ?signaling:bool -> ?negative:bool -> ?payload:word -> radix:int -> int -> gfloat

(** [is_fin x] returns true if [x] is finite number, i.e. neither nan
    nor inf *)
val is_fin : gfloat -> bool

(** [is_nan x] returns true if [x] is nan *)
val is_nan : gfloat -> bool

(** [is_signaling_nan x] returns true if [x] is nan and it's a
    signaling one *)
val is_signaling_nan : gfloat -> bool

(** [is_quite_nan x] returns true if [x] is nan and it's a
    quite one *)
val is_quite_nan : gfloat -> bool

(** [is_inf x] returns true if [x] is inf *)
val is_inf : gfloat -> bool

(** [is_pos x] returns true if [x] is positive *)
val is_pos : gfloat -> bool

(** [is_neg x] returns true if [x] is negative *)
val is_neg : gfloat -> bool

(** [is_zero x] returns true if [x] is zero *)
val is_zero : gfloat -> bool

(** [fin x] returns an exponent and fraction of [x], if
    [x] is finite number, i.e. neither infinity, nor nan *)
val fin : gfloat -> (word * word) option

(** [frac x] returns a fraction of a finite number or
    a payload of a nan *)
val frac : gfloat -> word option

(** [expn x] returns a exponent of a finite number *)
val expn : gfloat -> word option

(** [add ~rm x y] = x + y with rounding [rm] *)
val add : ?rm:rounding -> gfloat -> gfloat -> gfloat

(** [sub ~rm x y] = x - y with rounding [rm] *)
val sub : ?rm:rounding -> gfloat -> gfloat -> gfloat

(** [mul ~rm x y] = x * y with rounding [rm]  *)
val mul : ?rm:rounding -> gfloat -> gfloat -> gfloat

(** [div ~rm x y] = x / y with rounding [rm]  *)
val div : ?rm:rounding -> gfloat -> gfloat -> gfloat

(** [sqrt x] returns a square root of [x] with rounding [rm] *)
val sqrt : ?rm:rounding -> gfloat -> gfloat

(** [neg x] inverts sign of [x]  *)
val neg : gfloat -> gfloat

(** [round ~upto x] returns a rounded [x] to a [precision]. *)
val round : ?rm:rounding -> precision:int -> gfloat -> gfloat

(** [equal x y] return true if [x = y] *)
val equal : gfloat -> gfloat -> bool

(** A set of infix operators with default rounding = NearestTiesToEven *)
module Infix : sig
  val ( + ) : gfloat -> gfloat -> gfloat
  val ( - ) : gfloat -> gfloat -> gfloat
  val ( * ) : gfloat -> gfloat -> gfloat
  val ( / ) : gfloat -> gfloat -> gfloat
  val ( = ) : gfloat -> gfloat -> bool
end
